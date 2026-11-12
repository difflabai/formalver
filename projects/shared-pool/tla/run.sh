#!/usr/bin/env bash
# TLA+ layer of shared-pool (pattern: near-approval strategy.md section 17,
# tools/scripts/run-tla.sh). Exit 0 iff every check has its required outcome.
#
#   safety     TLC, MC_Safety: InvMC and StepProperty (TLA-SAFE); then every
#              Witness_* invariant and WitStep_* step property must be
#              VIOLATED (TLA-WIT, non-vacuity)
#   liveness   TLC, MC_Liveness: LIVE-2 under weak fairness with observes in
#              bounds (TLA-LIVE-1); without fairness it must FAIL; with a
#              disturbing observe it must FAIL (TLA-LIVE-F1), and Live2F1
#              (every counterexample is the F-1 wedge) must hold
#   apalache   TLA-IND (Apalache): not implemented, prints "skip" (a gap)
#   trace      REF-5: trace2tla.py converts conformance/traces/core.txt and
#              TLC replays every trace through TraceCheck (Inv and
#              StepProperty on every core state too); the state count must
#              equal traces + calls
#   mutants    every mutants/*.patch must make trace, safety or liveness fail
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
live_violated() { grep -q 'Temporal properties were violated' "$1"; }

fail=0
report() { # name ok(0/1) detail log
  if [ "$2" = 0 ]; then
    printf '%-32s ok    %s\n' "$1" "$3"
  else
    printf '%-32s FAIL  %s (log %s)\n' "$1" "$3" "$4"
    fail=1
  fi
}

STATE_WITNESSES="Witness_Completed Witness_Prerequisite Witness_Disturbed Witness_Wedge"
STEP_WITNESSES="WitStep_CancelledAfterDispatch WitStep_UnknownToActive WitStep_Recovery
  WitStep_PausedSettle WitStep_PausedAck WitStep_PausedCancel WitStep_PausedObserve"

check_safety() {
  local d=$1 log="$logs/safety.log" start
  start=$(date +%s)
  tlc "$d" MC_Safety.tla MC_Safety.cfg "$log"
  tlc_ok "$log"
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
  local d=$1 log="$logs/liveness.log" start
  start=$(date +%s)
  tlc "$d" MC_Liveness.tla MC_Liveness.cfg "$log"
  tlc_ok "$log"
  report liveness $? "LIVE-2 healthy (TLA-LIVE-1), $(states "$log"), $(($(date +%s) - start))s" "$log"
  log="$logs/liveness_unfair.log"
  tlc "$d" MC_Liveness.tla MC_Liveness_Unfair.cfg "$log"
  live_violated "$log"
  report liveness-unfair $? "LIVE-2 must fail without fairness" "$log"
  log="$logs/liveness_f1.log"
  tlc "$d" MC_Liveness.tla MC_Liveness_F1.cfg "$log"
  # The counterexample must end stuttering with an in-flight record after a
  # disturbing observe (m0 = 3 > max 2): F-1.
  live_violated "$log" && grep -q 'base = <<3, 2>>' "$log" && grep -q '^State [0-9]*: Stuttering' "$log"
  report liveness-f1 $? "LIVE-2 must fail with a disturbing observe (TLA-LIVE-F1)" "$log"
  log="$logs/liveness_f1shape.log"
  start=$(date +%s)
  tlc "$d" MC_Liveness.tla MC_Liveness_F1Shape.cfg "$log"
  tlc_ok "$log"
  report liveness-f1-shape $? "every LIVE-2 counterexample is F-1, $(states "$log"), $(($(date +%s) - start))s" "$log"
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
  tlc "$d" TraceCheck.tla TraceCheck.cfg "$log" -DTLA-Library="$d/build"
  got=$(grep -oE '^[0-9]+ states generated, [0-9]+ distinct states found, 0 states left' "$log" |
    sed -E 's/.* ([0-9]+) distinct.*/\1/')
  tlc_ok "$log" && [ "$got" = "$want" ]
  report trace-tlc $? "$ntr traces, $ncalls calls: $got of $want states, $(($(date +%s) - start))s" "$log"
}

# TLA-IND is optional and not implemented: Apalache 0.47.2 rejects the
# model's RECURSIVE sums and symbolic ranges (RESULTS.md, "Not covered").
# Reported as skipped; it does not change the exit code.
check_apalache() {
  printf '%-32s skip  %s\n' apalache "TLA-IND not implemented (gap, see RESULTS.md)"
}

check_mutants() {
  local p tmp killed rc
  for p in "$dir"/mutants/*.patch; do
    tmp=$(mktemp -d)
    cp "$dir"/*.tla "$dir"/*.cfg "$dir"/trace2tla.py "$tmp/"
    mkdir -p "$tmp/build"
    if ! patch -s -p1 -d "$tmp" <"$p"; then
      report "mutant $(basename "$p" .patch)" 1 "patch does not apply" "$p"
      rm -rf "$tmp"
      continue
    fi
    killed=""
    cp "$dir/build/TraceData.tla" "$tmp/build/"
    tlc "$tmp" TraceCheck.tla TraceCheck.cfg "$tmp/trace.log" -DTLA-Library="$tmp/build"
    tlc_ok "$tmp/trace.log" || killed="trace"
    if [ -z "$killed" ]; then
      tlc "$tmp" MC_Safety.tla MC_Safety.cfg "$tmp/safety.log"
      tlc_ok "$tmp/safety.log" || killed="safety"
    fi
    if [ -z "$killed" ]; then
      tlc "$tmp" MC_Liveness.tla MC_Liveness.cfg "$tmp/live.log"
      tlc_ok "$tmp/live.log" || killed="liveness"
    fi
    if [ -z "$killed" ]; then
      tlc "$tmp" MC_Liveness.tla MC_Liveness_F1Shape.cfg "$tmp/f1.log"
      tlc_ok "$tmp/f1.log" || killed="liveness-f1-shape"
    fi
    rc=1
    [ -n "$killed" ] && rc=0
    report "mutant $(basename "$p" .patch)" $rc "killed by ${killed:-nothing}" "$p"
    rm -rf "$tmp"
  done
}

for c in "$@"; do
  case $c in
    safety | liveness | apalache | trace) "check_$c" "$dir" ;;
    mutants)
      [ -f "$dir/build/TraceData.tla" ] || gen_traces "$dir/build"
      check_mutants
      ;;
    *) echo "unknown check $c" >&2; exit 2 ;;
  esac
done
exit $fail
