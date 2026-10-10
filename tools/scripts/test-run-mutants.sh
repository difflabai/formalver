#!/usr/bin/env bash
# Self-test for run-mutants.sh's verdicts: stand-in cargo and Kani commands
# that are missing, fail to build, fail a check, or pass. A setup failure
# must never read as a kill or a survival.
#
# usage: tools/scripts/test-run-mutants.sh   (needs the near-approval submodule)
set -uo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
fail=0

# fake <dir> <name> <exit code> <output>: writes an executable stand-in.
fake() {
  mkdir -p "$1"
  printf '#!/bin/sh\ncat <<'"'"'OUT'"'"'\n%s\nOUT\nexit %s\n' "$4" "$3" >"$1/$2"
  chmod +x "$1/$2"
}
base_path=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
# run-mutants.sh needs timeout(1), which macOS only has from GNU coreutils
# (e.g. /opt/homebrew/bin, not on base_path); link it in on its own so no
# real cargo becomes visible.
mkdir -p "$t/tools"
ln -s "$(command -v timeout)" "$t/tools/timeout"

# check <case> <expected "plain kani"> <dir with stand-ins> [kani command]
check() {
  local out got
  out=$(PATH="$3:$t/tools:$base_path" KANI="${4:-false}" \
        "$root/tools/scripts/run-mutants.sh" near-approval --kani '01-*' 2>&1)
  got=$(printf '%s\n' "$out" | awk '$1 ~ /^01-/ {print $3, $4}')
  if [ "$got" = "$2" ]; then echo "ok    $1: $got"; else echo "FAIL  $1: got '$got', want '$2'"; fail=1; fi
}

mkdir -p "$t/none"
check "cargo and kani missing" "ERROR ERROR" "$t/none" "$t/none/kani"

fake "$t/build" cargo 101 'error: could not compile `approval-core`'
fake "$t/build" kani 1 'error: unsupported option'
check "build and backend failures" "ERROR ERROR" "$t/build" "$t/build/kani"

fake "$t/oom" cargo 101 'test result: FAILED. 0 passed; 1 failed'
fake "$t/oom" kani 1 'CBMC appears to have run out of memory. VERIFICATION:- FAILED'
check "kani out of memory" "killed ERROR" "$t/oom" "$t/oom/kani"

fake "$t/kill" cargo 101 'test result: FAILED. 11 passed; 1 failed'
fake "$t/kill" kani 1 "$(printf 'Failed Checks: "TX exact result"\nVERIFICATION:- FAILED')"
check "real kills" "killed killed" "$t/kill" "$t/kill/kani"

fake "$t/pass" cargo 0 'test result: ok. 12 passed; 0 failed'
fake "$t/pass" kani 0 'VERIFICATION:- SUCCESSFUL'
check "real survival" "survived survived" "$t/pass" "$t/pass/kani"

exit $fail
