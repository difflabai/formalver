#!/usr/bin/env bash
# TLA+ layer of shared-pool (pattern: near-approval strategy.md section 17,
# tools/scripts/run-tla.sh). Exit 0 iff every check has its required outcome.
#
# PROP: TLA-SAFE TLA-WIT TLA-LIVE-1 TLA-LIVE-F1 TLA-LIVE-F2 REF-5 TLA-EXEC
#
#   safety     TLC, MC_Safety: InvMC and StepProperty (TLA-SAFE); then every
#              Witness_* invariant and WitStep_* step property must be
#              VIOLATED (TLA-WIT, non-vacuity)
#   liveness   TLC, MC_Liveness (LIVE-2):
#                liveness           completion path, MCConfig (TLA-LIVE-1)
#                liveness-f2-done   completion path, CreditHedgeConfig (TLA-LIVE-1)
#                liveness-unfair    without fairness LIVE-2 must FAIL
#                liveness-f1        disturbing observe: must FAIL as F-1 (TLA-LIVE-F1)
#                liveness-f1-shape  Live2F1 holds: every counterexample is F-1
#                liveness-f2        healthy, executor fair to settle(false): must
#                                   FAIL as F-2 (TLA-LIVE-F2)
#                liveness-f2-shape  Live2F2 holds: every counterexample is F-2
#   executor   TLA-EXEC (EX-6, EX-7, EX-8): TLC, Executor.tla, the executor's
#              job window against the lock's record window with receipts in
#              any order, at WINDOW 2 (MC_Executor_W2, as executor-w2) and 3
#              (MC_Executor_W3, as executor-w3); then every Witness_* and
#              WitStep_* of Executor.tla must be VIOLATED on MC_Executor_W2
#              without its VIEW (non-vacuity, and T-JOBCAP: the job cap
#              refuses a retained record's execute and confirmation)
#   apalache   TLA-IND (Apalache): not implemented, prints "skip" (a gap)
#   trace      REF-5: trace2tla.py converts conformance/traces/core.txt and
#              TLC replays every trace through TraceCheck (Inv and
#              StepProperty on every core state too); the state count must
#              equal traces + calls
#   mutants    every mutants/*.patch must make one of its checks fail. A
#              patch may start with `# checks: <check>...` (names as in the
#              liveness list, or trace / safety / executor-w2 / executor-w3 /
#              executor-w2-noview, the WINDOW 2 universe without the VIEW,
#              which the executor patches use); otherwise the checks are
#              trace, safety, liveness, liveness-f1-shape, liveness-f2-shape,
#              tried in order until one fails. The report names the killing
#              check and why (invariant, temporal, rejected trace call, or
#              a required violation that disappeared).
#
# usage: projects/shared-pool/tla/run.sh [check...]  (default: safety liveness trace)
# env:   TLA_WORKERS (default 4, keep <= 4), TLA_HEAP (default 6g), TLA_LOG_DIR,
#        TLA_CACHE (as tools/scripts/get-tla-tools.sh)
set -uo pipefail

dir=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$dir/../../.." && pwd)
. "$root/tools/versions.env"
# Reuse the machine-wide tool cache when it holds the pinned jar.
if [ -z "${TLA_CACHE:-}" ] && [ -f "$HOME/.cache/formalver-tools/tla2tools-$TLA2TOOLS.jar" ]; then
  export TLA_CACHE="$HOME/.cache/formalver-tools"
fi
cache=$("$root/tools/scripts/get-tla-tools.sh") || exit 2
jar="$cache/tla2tools-$TLA2TOOLS.jar"
traces="$root/projects/shared-pool/conformance/traces/core.txt"
logs=${TLA_LOG_DIR:-$dir/build/logs}
mkdir -p "$logs" "$dir/build/cfg"
[ $# -gt 0 ] || set -- safety liveness trace

# tlc <spec dir> <module> <cfg> <log> [java -D options...]
tlc() {
  local d=$1 m=$2 c=$3 log=$4 tmp
  shift 4
  tmp=$(mktemp -d)
  (cd "$d" && java -XX:+UseParallelGC -Xmx"${TLA_HEAP:-6g}" -Djava.io.tmpdir="$tmp" "$@" \
    -cp "$jar" tlc2.TLC -workers "${TLA_WORKERS:-4}" -cleanup -metadir "$tmp/states" \
    -config "$c" "$m") >"$log" 2>&1
  rm -rf "$tmp"
  rm -f "$d"/*_TTrace_*
}
tlc_ok() { grep -q 'Model checking completed. No error has been found.' "$1"; }
states() { grep -oE '[0-9,]+ distinct states found' "$1" | tail -1; }
depth() { grep -oE 'depth of the complete state graph search is [0-9]+' "$1" | grep -oE '[0-9]+$'; }
live_violated() { grep -q 'Temporal properties were violated' "$1"; }
# Why a TLC run did not pass: the first violation it reports.
why() {
  local w t
  w=$(grep -oE 'Invariant [A-Za-z0-9_]+ is violated|Action property [A-Za-z0-9_]+ is violated|Temporal properties were violated|Deadlock reached|Parsing or semantic analysis failed|Assumption .* is false' "$1" | head -1)
  # TraceCheck: a deadlock is a rejected call. Name it: trace(N) of core.txt
  # (tr is 1-based) and the call's 1-based position (pos calls replayed).
  if [ "$w" = "Deadlock reached" ]; then
    t=$(awk '/^\/\\ tr = /{tr=$4} /^\/\\ pos = /{pos=$4} END{if (tr != "") printf "trace(%d) call %d", tr-1, pos+1}' "$1")
    w="rejected ${t:-a trace call}"
  fi
  echo "$w"
}

# The last state of a TLC counterexample that ends stuttering, its records
# as JSON-ish lines "recipe status" (one per record), for shape checks.
cex_records() {
  python3 -I - "$1" <<'EOF'
import re, sys
s = open(sys.argv[1]).read()
i = s.find("Stuttering")
if "Temporal properties were violated" not in s or i < 0:
    sys.exit(1)
blocks = [b for b in re.split(r"\nState \d+: ", s[:i]) if b.strip()]
last = blocks[-1]
m = re.search(r"/\\ records = (.*?)(?:\n/\\ |\n\n|$)", last, re.S)
if not m:
    sys.exit(1)
for rec in re.findall(r"\[([^\[\]]*)\]", m.group(1)):
    f = dict(re.findall(r'(\w+) \|-> ("[^"]*"|-?\d+)', rec))
    print(f.get("recipe"), f.get("status", "").strip('"'))
b = re.search(r"/\\ base = <<([^>]*)>>", last)
print("base", b.group(1).replace(" ", "") if b else "?")
EOF
}

# Each run_<check> <spec dir> <log> returns 0 iff the check has its
# required outcome (shared by the checks and the mutant runner).
run_trace() {
  tlc "$1" TraceCheck.tla TraceCheck.cfg "$2" -DTLA-Library="$1/build"
  tlc_ok "$2"
}
run_safety() {
  tlc "$1" MC_Safety.tla MC_Safety.cfg "$2"
  tlc_ok "$2"
}
run_liveness() {
  tlc "$1" MC_Liveness.tla MC_Liveness.cfg "$2"
  tlc_ok "$2"
}
run_liveness-f2-done() {
  tlc "$1" MC_Liveness.tla MC_Liveness_F2Done.cfg "$2"
  tlc_ok "$2"
}
run_liveness-unfair() {
  tlc "$1" MC_Liveness.tla MC_Liveness_Unfair.cfg "$2"
  live_violated "$2"
}
# The counterexample must end stuttering with an in-flight record after a
# disturbing observe (m0 = 3 > max 2): F-1.
run_liveness-f1() {
  tlc "$1" MC_Liveness.tla MC_Liveness_F1.cfg "$2"
  live_violated "$2" && grep -q 'base = <<3, 2>>' "$2" && grep -q '^State [0-9]*: Stuttering' "$2"
}
run_liveness-f1-shape() {
  tlc "$1" MC_Liveness.tla MC_Liveness_F1Shape.cfg "$2"
  tlc_ok "$2"
}
# The counterexample must end stuttering with the credit (recipe 0) in
# flight, the hedge (recipe 1) Completed, and an in-bounds base: F-2.
run_liveness-f2() {
  local r
  tlc "$1" MC_Liveness.tla MC_Liveness_F2.cfg "$2"
  r=$(cex_records "$2") || return 1
  echo "$r" | grep -qE '^0 (Dispatched|Active|Unknown)$' &&
    echo "$r" | grep -qE '^1 Completed$' && echo "$r" | grep -qE '^base [012]$'
}
run_liveness-f2-shape() {
  tlc "$1" MC_Liveness.tla MC_Liveness_F2Shape.cfg "$2"
  tlc_ok "$2"
}
# TLA-EXEC: every invariant and StepExec of Executor.tla.
run_executor-w2() {
  tlc "$1" Executor.tla MC_Executor_W2.cfg "$2"
  tlc_ok "$2"
}
run_executor-w3() {
  tlc "$1" Executor.tla MC_Executor_W3.cfg "$2"
  tlc_ok "$2"
}
# The WINDOW 2 universe without the VIEW. The VIEW is a quotient of the
# unmutated model only (a mutant may change what a dead receipt does), so
# the executor mutants run here.
run_executor-w2-noview() {
  mkdir -p "$1/build/cfg"
  sed '/^VIEW /d' "$1/MC_Executor_W2.cfg" >"$1/build/cfg/MC_Executor_W2_noview.cfg"
  tlc "$1" Executor.tla build/cfg/MC_Executor_W2_noview.cfg "$2"
  tlc_ok "$2"
}

fail=0
report() { # name ok(0/1) detail log
  if [ "$2" = 0 ]; then
    printf '%-36s ok    %s\n' "$1" "$3"
  else
    printf '%-36s FAIL  %s (log %s)\n' "$1" "$3" "$4"
    fail=1
  fi
}

STATE_WITNESSES="Witness_Completed Witness_Prerequisite Witness_Disturbed Witness_Wedge"
STEP_WITNESSES="WitStep_CancelledAfterDispatch WitStep_UnknownToActive WitStep_Recovery
  WitStep_PausedSettle WitStep_PausedAck WitStep_PausedCancel WitStep_PausedObserve"

check_safety() {
  local d=$1 log="$logs/safety.log" start
  start=$(date +%s)
  run_safety "$d" "$log"
  report safety $? "InvMC + StepProperty, $(states "$log"), $(($(date +%s) - start))s" "$log"
  for w in $STATE_WITNESSES; do
    log="$logs/$w.log"
    sed -e "s/^INVARIANT InvMC$/INVARIANT $w/" -e '/^PROPERTY /d' "$d/MC_Safety.cfg" >"$d/build/cfg/$w.cfg"
    tlc "$d" MC_Safety.tla "build/cfg/$w.cfg" "$log"
    grep -q "Invariant $w is violated" "$log"
    report "$w" $? "must be reachable" "$log"
  done
  for w in $STEP_WITNESSES; do
    log="$logs/$w.log"
    sed -e '/^INVARIANT /d' -e "s/^PROPERTY StepProperty$/PROPERTY $w/" "$d/MC_Safety.cfg" >"$d/build/cfg/$w.cfg"
    tlc "$d" MC_Safety.tla "build/cfg/$w.cfg" "$log"
    grep -q "Action property $w is violated" "$log"
    report "$w" $? "must be reachable" "$log"
  done
}

check_liveness() {
  local d=$1 c log start
  for c in liveness liveness-f2-done liveness-unfair liveness-f1 liveness-f1-shape \
    liveness-f2 liveness-f2-shape; do
    log="$logs/$c.log"
    start=$(date +%s)
    "run_$c" "$d" "$log"
    report "$c" $? "$(desc "$c"), $(states "$log"), $(($(date +%s) - start))s" "$log"
  done
}
desc() {
  case $1 in
    liveness) echo "LIVE-2, completion path, MCConfig (TLA-LIVE-1)" ;;
    liveness-f2-done) echo "LIVE-2, completion path, CreditHedgeConfig (TLA-LIVE-1)" ;;
    liveness-unfair) echo "LIVE-2 must fail without fairness" ;;
    liveness-f1) echo "LIVE-2 must fail with a disturbing observe, F-1 (TLA-LIVE-F1)" ;;
    liveness-f1-shape) echo "Live2F1: every counterexample is F-1" ;;
    liveness-f2) echo "LIVE-2 must fail, healthy, fair settle(false): F-2 (TLA-LIVE-F2)" ;;
    liveness-f2-shape) echo "Live2F2: every counterexample is F-2" ;;
    executor-w2) echo "TLA-EXEC, WINDOW 2, MAX_JOBS 4" ;;
    executor-w3) echo "TLA-EXEC, WINDOW 3, MAX_JOBS 6" ;;
  esac
}

EXEC_STATE_WITNESSES="Witness_Pruned Witness_Cap Witness_JobCapExec Witness_JobCapConfirm
  Witness_ConfirmStale"
EXEC_STEP_WITNESSES="WitStep_ExecStale WitStep_ExecStored WitStep_ExecFull WitStep_ExecForgets
  WitStep_SettleForgets WitStep_SettleRefused WitStep_CapExit"

# TLA-EXEC at WINDOW 2 and 3, then its witnesses (non-vacuity, including
# the documented job-cap refusals T-JOBCAP) on the WINDOW 2 universe,
# without the VIEW: it may expand only one state of a view, and the one it
# keeps need not be a witness's source (a stale execute's state shares its
# view with one where the record was cancelled before dispatch).
check_executor() {
  local d=$1 c w log start
  for c in executor-w2 executor-w3; do
    log="$logs/$c.log"
    start=$(date +%s)
    "run_$c" "$d" "$log"
    report "$c" $? "$(desc "$c"), $(states "$log"), depth $(depth "$log"), $(($(date +%s) - start))s" "$log"
  done
  for w in $EXEC_STATE_WITNESSES $EXEC_STEP_WITNESSES; do
    log="$logs/$w.log"
    {
      sed -e '/^INVARIANT /d' -e '/^PROPERTY /d' -e '/^VIEW /d' "$d/MC_Executor_W2.cfg"
      case $w in
        Witness_*) echo "INVARIANT $w" ;;
        *) echo "PROPERTY $w" ;;
      esac
    } >"$d/build/cfg/$w.cfg"
    tlc "$d" Executor.tla "build/cfg/$w.cfg" "$log"
    grep -qE "(Invariant|Action property) $w is violated" "$log"
    report "$w" $? "must be reachable" "$log"
  done
}

gen_traces() { # out dir
  python3 -I "$dir/trace2tla.py" "$traces" "$1/TraceData.tla" 2>"$logs/trace2tla.log"
}

check_trace() {
  local d=$1 log="$logs/trace-tlc.log" ntr ncalls want got start
  gen_traces "$d/build"
  report trace2tla $? "$(cat "$logs/trace2tla.log")" "$logs/trace2tla.log"
  ntr=$(grep -c '^trace(' "$traces")
  ncalls=$(grep -c '^call(' "$traces")
  want=$((ntr + ncalls))
  start=$(date +%s)
  run_trace "$d" "$log"
  got=$(grep -oE '^[0-9]+ states generated, [0-9]+ distinct states found, 0 states left' "$log" |
    sed -E 's/.* ([0-9]+) distinct.*/\1/')
  tlc_ok "$log" && [ "$got" = "$want" ]
  report trace-tlc $? "$ntr traces, $ncalls calls: $got of $want states, $(($(date +%s) - start))s" "$log"
}

# TLA-IND is optional and not implemented: Apalache 0.47.2 rejects the
# model's RECURSIVE sums and symbolic ranges (RESULTS.md, "Not covered").
# Reported as skipped; it does not change the exit code.
check_apalache() {
  printf '%-36s skip  %s\n' apalache "TLA-IND not implemented (gap, see RESULTS.md)"
}

check_mutants() {
  local p tmp killed checks c start r
  for p in "$dir"/mutants/*.patch; do
    start=$(date +%s)
    tmp=$(mktemp -d)
    cp "$dir"/*.tla "$dir"/*.cfg "$dir"/trace2tla.py "$tmp/"
    mkdir -p "$tmp/build"
    if ! patch -s -p1 -d "$tmp" <"$p"; then
      report "mutant $(basename "$p" .patch)" 1 "patch does not apply" "$p"
      rm -rf "$tmp"
      continue
    fi
    cp "$dir/build/TraceData.tla" "$tmp/build/"
    checks=$(sed -n 's/^# checks: //p' "$p" | head -1)
    [ -n "$checks" ] || checks="trace safety liveness liveness-f1-shape liveness-f2-shape"
    killed=""
    for c in $checks; do
      if ! "run_$c" "$tmp" "$tmp/$c.log"; then
        case $c in
          liveness-unfair | liveness-f1 | liveness-f2)
            if live_violated "$tmp/$c.log"; then
              killed="$c (counterexample no longer has the required shape)"
            else
              r=$(why "$tmp/$c.log")
              killed="$c (required LIVE-2 violation gone: ${r:-no error})"
            fi
            ;;
          *) killed="$c ($(why "$tmp/$c.log"))" ;;
        esac
        break
      fi
    done
    report "mutant $(basename "$p" .patch)" "$([ -n "$killed" ] && echo 0 || echo 1)" \
      "killed by ${killed:-nothing (tried: $checks)}, $(($(date +%s) - start))s" "$p"
    rm -rf "$tmp"
  done
}

for c in "$@"; do
  case $c in
    safety | liveness | apalache | trace | executor) "check_$c" "$dir" ;;
    mutants)
      gen_traces "$dir/build" || { report trace2tla 1 "conversion failed" "$logs/trace2tla.log"; continue; }
      check_mutants
      ;;
    *) echo "unknown check $c" >&2; exit 2 ;;
  esac
done
exit $fail
