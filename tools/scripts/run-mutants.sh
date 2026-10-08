#!/usr/bin/env bash
# Applies each core mutant in projects/<project>/kani/mutants/ to a temporary
# copy of the pinned core and checks it is killed (strategy.md section 6.4).
# Mutants marked "must-survive" are equivalent (F-14) and must NOT be killed.
#
# usage: tools/scripts/run-mutants.sh near-approval [--kani] [patch-glob]
#   default: plain mode (cargo test) for every mutant
#   --kani:  also run the mutant's "killed-by" harness under Kani
#            (for must-survive mutants: h_step_approve and h_read)
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
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export CARGO_TARGET_DIR="$work/target"

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
  # see non-Inv states and rightly tell them apart, so they are excluded.
  plain_filter=""
  if grep -q "^# must-survive" "$p"; then expect=survive; harnesses="h_step_approve h_read"
    plain_filter="--skip h_raw_"
  else expect=killed; harnesses=$(sed -n 's/^# killed-by: //p' "$p"); fi

  if (cd "$work/tree/kani" && cargo test --release -q -- $plain_filter >"$work/plain.log" 2>&1); then plain=survived; else plain=killed; fi
  [ -n "${KEEP_LOGS:-}" ] && cp "$work/plain.log" "$KEEP_LOGS/$name.plain.log"
  if grep -q 'error\[E' "$work/plain.log"; then plain=NO-BUILD; fi

  kres=-
  if [ $use_kani -eq 1 ]; then
    kres=survived
    for h in $harnesses; do
      (cd "$work/tree/kani" && timeout "${KANI_TIMEOUT:-3600}" $kani $flags --harness "proofs::$h" --exact >"$work/kani-$h.log" 2>&1)
      rc=$?
      [ -n "${KEEP_LOGS:-}" ] && cp "$work/kani-$h.log" "$KEEP_LOGS/$name.$h.log"
      # Only a failed property kills; running out of time or memory is no verdict.
      # rc 137/143: CBMC or the job was killed (usually the OOM killer).
      if [ $rc -eq 124 ] || [ $rc -eq 137 ] || [ $rc -eq 143 ] || grep -q 'run out of memory' "$work/kani-$h.log"; then
        kres=ERROR; break
      elif [ $rc -ne 0 ]; then
        kres=killed; break
      fi
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
