#!/usr/bin/env bash
# Applies each shell mutant in projects/near-approval/near-tests/mutants/ to a
# temporary copy of the pinned contract and checks that the near-tests suite
# fails on it (strategy.md section 9, M3). Conventions follow
# tools/scripts/run-mutants.sh: a verdict needs evidence ("killed" only when a
# test actually failed); a patch or build failure is ERROR.
#
# usage: projects/near-approval/near-tests/run-mutants.sh [patch-glob]
#   MUTANT_STORE_DIFF_SEQS  store_diff sequences per mutant (default 300 x 50 steps)
#   KEEP_LOGS=<dir>         keep each mutant's test log
set -uo pipefail

glob=${1:-*}
here=$(cd "$(dirname "$0")" && pwd)
proj=$(cd "$here/.." && pwd)
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/near-mutants.XXXXXX") || exit 2
trap 'rm -rf "$work"' EXIT
# One target dir for every mutant: only approval-contract and the tests rebuild.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$work/target}"
export STORE_DIFF_SEQS=${MUTANT_STORE_DIFF_SEQS:-300}

verdict() { # <rc> <log>: survived | killed | ERROR
  if [ "$1" -eq 0 ] && grep -q '^test result: ok' "$2" && ! grep -q '^test result: FAILED' "$2"; then
    echo survived
  elif [ "$1" -ne 0 ] && grep -q '^test result: FAILED' "$2"; then
    echo killed
  else
    echo ERROR
  fi
}

# tree <patch|->: a fresh copy of the contract (patched) and the suite.
tree() {
  rm -rf "$work/tree"
  mkdir -p "$work/tree/source-mirror/contracts/approval" "$work/tree/near-tests"
  # Cargo.lock: tests/lockfile.rs compares against the mirror's lockfile.
  cp -r "$proj/source-mirror/contracts/approval/core" "$proj/source-mirror/contracts/approval/contract" \
    "$proj/source-mirror/contracts/approval/Cargo.lock" "$work/tree/source-mirror/contracts/approval/"
  cp -r "$here/Cargo.toml" "$here/Cargo.lock" "$here/src" "$here/tests" "$work/tree/near-tests/"
  [ "$1" = - ] || (cd "$work/tree/source-mirror/contracts/approval" && patch -s -p1 < "$1")
}

# Control: the unpatched copy must pass, or every "killed" below is noise.
tree - || exit 2
(cd "$work/tree/near-tests" && cargo test --locked --no-fail-fast) >"$work/log" 2>&1
rc=$?
v=$(verdict $rc "$work/log")
printf '%-44s %-8s\n' "(unpatched control)" "$v"
if [ "$v" != survived ]; then
  tail -n 40 "$work/log"; echo "the unpatched suite does not pass in the mutant tree" >&2; exit 2
fi

fail=0
n=0
printf '%-44s %-8s %s\n' mutant verdict failing-tests
for p in "$here"/mutants/$glob.patch; do
  [ -e "$p" ] || continue
  name=$(basename "$p" .patch)
  n=$((n + 1))
  if ! tree "$p"; then
    printf '%-44s %s\n' "$name" "PATCH-FAILED"; fail=1; continue
  fi
  (cd "$work/tree/near-tests" && cargo test --locked --no-fail-fast) >"$work/log" 2>&1
  rc=$?
  [ -n "${KEEP_LOGS:-}" ] && cp "$work/log" "$KEEP_LOGS/$name.log"
  v=$(verdict $rc "$work/log")
  failing=$(grep -a -E '^    [a-z0-9_]+$' "$work/log" | sed 's/^ *//' | sort -u | tr '\n' ' ')
  [ "$v" = killed ] || fail=1
  printf '%-44s %-8s %s%s\n' "$name" "$v" "$failing" "$([ "$v" = killed ] || echo '  <-- UNEXPECTED')"
done
[ $n -gt 0 ] || { echo "no mutants matched $glob" >&2; exit 2; }
exit $fail
