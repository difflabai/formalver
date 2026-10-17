#!/usr/bin/env bash
# Runs the Kani harnesses of a project one at a time and checks the outcome
# strategy.md section 6.2 requires: every harness verifies with unwinding
# assertions on, every cover is SATISFIED, and h_canary FAILS.
#
# A harness split into instances forms a family: the parts of a step
# harness (_tx, _post, _hist, _inv, _reg) and its _empty instance; h_read,
# h_read_page and h_read_find; h_bmc_from_init and its _witness. A cover
# must be SATISFIED in at least one instance of its family, and may be
# UNREACHABLE or UNSATISFIABLE in the others.
#
# usage: tools/scripts/run-kani.sh near-approval [harness...]
# env:   KANI (default: cargo kani), KANI_TIMEOUT seconds per harness (default 3600),
#        KANI_LOG_DIR (default: target/kani-logs under the crate),
#        KANI_DEFER_COVERS=1 to leave the family cover check to check-covers.sh
set -uo pipefail

project=${1:?usage: run-kani.sh <project> [harness...]}
shift
root=$(cd "$(dirname "$0")/../.." && pwd)
crate="$root/projects/$project/kani"
[ -d "$crate" ] || { echo "no Kani crate at $crate" >&2; exit 2; }
kani=${KANI:-cargo kani}
# The core is #![forbid(unsafe_code)]; the memory safety of std internals is
# trusted (ASM-TOOLS). Panics, overflow and unwinding checks stay on.
flags=${KANI_FLAGS:---no-memory-safety-checks}
timeout_s=${KANI_TIMEOUT:-3600}
logs=${KANI_LOG_DIR:-$crate/target/kani-logs}
mkdir -p "$logs"

if [ $# -eq 0 ]; then
  # Plain `fn h_*()` harnesses, plus the parts `step_parts!` generates.
  set -- $( (grep -A3 '#\[kani::proof\]' "$crate/src/proofs.rs" | sed -n 's/^fn \(h_[a-z_]*\)().*/\1/p'
             grep -oE '\bh_step_[a-z_]+_(tx|post|hist|inv|reg)\b' "$crate/src/proofs.rs") | awk '!seen[$0]++')
fi

fail=0
covers_all="$logs/covers.tsv"
: >"$covers_all"
printf '%-20s %-8s %8s  %s\n' harness result seconds covers
for h in "$@"; do
  log="$logs/$h.log"
  start=$(date +%s)
  (cd "$crate" && timeout "$timeout_s" $kani $flags --harness "proofs::$h" --exact) >"$log" 2>&1
  rc=$?
  secs=$(( $(date +%s) - start ))
  covers=$(grep -oE '[0-9]+ of [0-9]+ cover properties satisfied' "$log" | tail -1)
  family=${h%_tx}; family=${family%_post}; family=${family%_hist}; family=${family%_inv}; family=${family%_reg}
  family=${family%_empty}; family=${family%_page}; family=${family%_find}; family=${family%_witness}
  family=${family%_law_*}
  awk -v fam="$family" '/^Check [0-9]+: .*\.cover\./ {c=1; next}
       c && /Status:/ {st=$NF; next}
       c && /Description:/ {sub(/.*Description: /, ""); print fam "\t" $0 "\t" st; c=0}' \
    "$log" >>"$covers_all"
  if [ "$h" = h_canary ]; then
    # It must fail on its own assertion and nothing else; failing for any
    # other reason (an unwinding assertion, a panic in gen) says nothing.
    failed=$(grep '^Failed Checks:' "$log" | sort -u)
    if grep -q 'VERIFICATION:- FAILED' "$log" &&
       [ "$failed" = 'Failed Checks: "canary: no approval is ever recorded"' ]; then
      result=ok
    elif grep -q 'VERIFICATION:- SUCCESSFUL' "$log"; then
      result=CANARY-PASSED; fail=1
    else
      result=CANARY-OTHER; fail=1
    fi
  elif [ $rc -eq 124 ]; then
    result=TIMEOUT; fail=1
  elif grep -q 'VERIFICATION:- SUCCESSFUL' "$log"; then
    result=ok
  else
    result=FAILED; fail=1
  fi
  printf '%-20s %-8s %8s  %s\n' "$h" "$result" "$secs" "${covers:--}"
  # In GitHub Actions, surface why a harness failed as an annotation (rc
  # 137/143: the process was killed, usually for memory).
  if [ -n "${GITHUB_ACTIONS:-}" ] && [ "$result" != ok ]; then
    why=$(grep -E 'out of memory|Failed Checks:' "$log" | head -3 | tr '\n' ' ')
    echo "::error title=$h $result::rc=$rc after ${secs}s. ${why:-no diagnostics in log}"
  fi
done
# Covers, per family: each must be SATISFIED somewhere. KANI_DEFER_COVERS=1
# skips this when a family's harnesses run in separate invocations (CI); the
# caller then runs check-covers.sh over all of their covers.tsv files.
if [ "${KANI_DEFER_COVERS:-0}" != 1 ]; then
  "$root/tools/scripts/check-covers.sh" "$covers_all" || fail=1
fi
exit $fail
