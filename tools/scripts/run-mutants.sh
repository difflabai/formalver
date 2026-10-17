#!/usr/bin/env bash
# Applies each core mutant in projects/<project>/kani/mutants/ to a temporary
# copy of the pinned core and checks it is killed (strategy.md section 6.4).
# Mutants marked "must-survive" are equivalent (F-14) and must NOT be killed.
#
# usage: tools/scripts/run-mutants.sh near-approval [--kani] [patch-glob]
#   default: plain mode (cargo test) for every mutant
#   --kani:  also run the mutant's "killed-by" harness under Kani
#            (for must-survive mutants: every h_step_approve part and h_read)
set -uo pipefail

project=${1:?usage: run-mutants.sh <project> [--kani] [glob]}
shift
use_kani=0
if [ "${1:-}" = --kani ]; then use_kani=1; shift; fi
glob=${1:-*}
root=$(cd "$(dirname "$0")/../.." && pwd)
proj="$root/projects/$project"
kani=${KANI:-cargo kani}
# The core is #![forbid(unsafe_code)]; the memory safety of std internals is
# trusted (ASM-TOOLS). Panics, overflow and unwinding checks stay on.
flags=${KANI_FLAGS:---no-memory-safety-checks}
# Under RUNNER_TEMP on CI: up to 6 runner instances share one Mac's TMPDIR,
# and the runner wipes its own _temp, reclaiming trees a cancelled job left.
work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/mutants.XXXXXX") || exit 2
trap 'rm -rf "$work"' EXIT
export CARGO_TARGET_DIR="$work/target"

# plain_verdict <rc> <log>: survived | killed | ERROR
plain_verdict() {
  if [ "$1" -eq 0 ] && grep -q '^test result: ok' "$2" && ! grep -q '^test result: FAILED' "$2"; then
    echo survived
  elif [ "$1" -ne 0 ] && grep -q '^test result: FAILED' "$2"; then
    echo killed
  else
    echo ERROR
  fi
}

# kani_verdict <rc> <log>: survived | killed | ERROR
# rc 124: timeout; 137/143: killed by a signal (usually the OOM killer).
# A failed unwinding assertion (the unwind bound is too low) or a reachable
# construct Kani cannot model means part of the search was skipped, not that
# a property failed, so either one is ERROR even next to a real failure.
# Only failed checks count: every log lists std's unsupported-construct
# checks, normally with Status: SUCCESS (unreachable).
kani_verdict() {
  if [ "$1" -eq 124 ] || [ "$1" -eq 137 ] || [ "$1" -eq 143 ] || grep -q 'run out of memory' "$2"; then
    echo ERROR
  elif grep -q '^Failed Checks: .*unwinding assertion' "$2" || grep -q '^Failed Checks: .*not currently supported by Kani' "$2"; then
    echo ERROR
  elif [ "$1" -eq 0 ] && grep -q 'VERIFICATION:- SUCCESSFUL' "$2"; then
    echo survived
  elif [ "$1" -ne 0 ] && grep -q 'VERIFICATION:- FAILED' "$2" && grep -q '^Failed Checks:' "$2"; then
    echo killed
  else
    echo ERROR
  fi
}

fail=0
printf '%-42s %-14s %-8s %s\n' mutant expect plain kani
for p in "$proj"/kani/mutants/$glob.patch; do
  name=$(basename "$p" .patch)
  rm -rf "$work/tree"
  mkdir -p "$work/tree/source-mirror/contracts/approval"
  cp -r "$proj/source-mirror/contracts/approval/core" "$work/tree/source-mirror/contracts/approval/"
  mkdir -p "$work/tree/kani"
  cp -r "$proj/kani/Cargo.toml" "$proj/kani/src" "$work/tree/kani/"
  [ -f "$proj/kani/Cargo.lock" ] && cp "$proj/kani/Cargo.lock" "$work/tree/kani/"
  if ! (cd "$work/tree/source-mirror/contracts/approval" && patch -s -p1 < "$p"); then
    printf '%-42s %s\n' "$name" "PATCH-FAILED"; fail=1; continue
  fi
  # Must-survive mutants are equivalent only under Inv (F-14): raw harnesses
  # (h_raw_*, h_proto_* on raw Sparse states, and facts, which judges guards
  # on raw states half the time) see non-Inv states and rightly tell them
  # apart, so they are excluded.
  plain_filter=""
  if grep -q "^# must-survive" "$p"; then expect=survive; harnesses="h_step_approve_tx h_step_approve_post h_step_approve_hist h_step_approve_inv h_step_approve_reg h_read"
    plain_filter="--skip h_raw_ --skip h_proto --skip facts"
  else expect=killed; harnesses=$(sed -n 's/^# killed-by: //p' "$p"); fi

  # A verdict needs evidence: "killed" only when a test or Kani property
  # actually failed, "survived" only when every check ran and passed.
  # Anything else (missing tools, build or backend failures, time-outs,
  # running out of memory, an unwind bound too low, an unsupported
  # construct) is ERROR.
  (cd "$work/tree/kani" && cargo test --release -q -- $plain_filter) >"$work/plain.log" 2>&1
  rc=$?
  [ -n "${KEEP_LOGS:-}" ] && cp "$work/plain.log" "$KEEP_LOGS/$name.plain.log"
  plain=$(plain_verdict $rc "$work/plain.log")

  kres=-
  if [ $use_kani -eq 1 ]; then
    kres=ERROR
    [ -n "$harnesses" ] && kres=survived
    for h in $harnesses; do
      (cd "$work/tree/kani" && timeout "${KANI_TIMEOUT:-3600}" $kani $flags --harness "proofs::$h" --exact) >"$work/kani-$h.log" 2>&1
      rc=$?
      [ -n "${KEEP_LOGS:-}" ] && cp "$work/kani-$h.log" "$KEEP_LOGS/$name.$h.log"
      v=$(kani_verdict $rc "$work/kani-$h.log")
      if [ "$v" != survived ]; then kres=$v; break; fi
    done
  fi

  ok=1
  if [ "$expect" = killed ]; then
    [ "$plain" = killed ] || ok=0
    [ $use_kani -eq 0 ] || [ "$kres" = killed ] || ok=0
  else
    [ "$plain" = survived ] || ok=0
    [ $use_kani -eq 0 ] || [ "$kres" = survived ] || ok=0
  fi
  [ $ok -eq 1 ] || fail=1
  printf '%-42s %-14s %-8s %s%s\n' "$name" "$expect" "$plain" "$kres" "$([ $ok -eq 1 ] || echo '  <-- UNEXPECTED')"
done
exit $fail
