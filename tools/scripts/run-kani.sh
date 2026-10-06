#!/usr/bin/env bash
# Runs the Kani harnesses of a project one at a time and checks the outcome
# strategy.md section 6.2 requires: every harness verifies with unwinding
# assertions on, every cover is SATISFIED, and h_canary FAILS.
#
# A harness split into instances (h_step_request and h_step_request_empty;
# h_read, h_read_page and h_read_find) forms a family: a cover must be
# SATISFIED in at least one instance of its family, and may be UNREACHABLE
# or UNSATISFIABLE in the others.
#
# usage: tools/scripts/run-kani.sh near-approval [harness...]
# env:   KANI (default: cargo kani), KANI_TIMEOUT seconds per harness (default 3600),
#        KANI_LOG_DIR (default: target/kani-logs under the crate)
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
  set -- $(grep -A3 '#\[kani::proof\]' "$crate/src/proofs.rs" | sed -n 's/^fn \(h_[a-z_]*\)().*/\1/p')
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
  family=${h%_empty}; family=${family%_page}; family=${family%_find}
  awk -v fam="$family" '/^Check [0-9]+: .*\.cover\./ {c=1; next}
       c && /Status:/ {st=$NF; next}
       c && /Description:/ {sub(/.*Description: /, ""); print fam "\t" $0 "\t" st; c=0}' \
    "$log" >>"$covers_all"
  if [ "$h" = h_canary ]; then
    if grep -q 'VERIFICATION:- FAILED' "$log" && grep -q 'canary' "$log"; then
      result=ok; else result=CANARY-PASSED; fail=1; fi
  elif [ $rc -eq 124 ]; then
    result=TIMEOUT; fail=1
  elif grep -q 'VERIFICATION:- SUCCESSFUL' "$log"; then
    result=ok
  else
    result=FAILED; fail=1
  fi
  printf '%-20s %-8s %8s  %s\n' "$h" "$result" "$secs" "${covers:--}"
done
# Covers, per family: each must be SATISFIED somewhere.
missing=$(awk -F'\t' '{k=$1 "\t" $2; if ($3=="SATISFIED") s[k]=1; else if (!(k in s)) s[k]=s[k]+0}
                     END {for (k in s) if (!s[k]) print k}' "$covers_all")
if [ -n "$missing" ]; then
  echo "unsatisfied covers:"; echo "$missing"; fail=1
fi
exit $fail
