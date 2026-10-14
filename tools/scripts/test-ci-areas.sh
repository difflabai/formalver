#!/usr/bin/env bash
# Self-test for ci-areas.sh: which jobs each kind of change runs.
#
# usage: tools/scripts/test-ci-areas.sh
set -uo pipefail
areas="$(cd "$(dirname "$0")" && pwd)/ci-areas.sh"
fail=0
p=projects/near-approval

# expect "<jobs that run>" <changed path>...
expect() {
  local want=$1 got
  shift
  got=$(printf '%s\n' "$@" | "$areas" | sed -n 's/=true$//p' | tr '\n' ' ')
  got=${got% }
  if [ "$got" != "$want" ]; then
    echo "FAIL: $* -> '$got', want '$want'"
    fail=1
  fi
}

all="plain loops kani tla lean prolog"
expect "" $p/strategy.md $p/kani/RESULTS.md README.md
expect "" $p/status.toml tools/scripts/check-pin.sh
expect "" tools/upstream-watch.toml tools/scripts/run-verus.sh
expect "" # no changes
expect "$all" $p/source-mirror
expect "$all" $p/kani/src/lib.rs
expect "$all" $p/kani/Cargo.lock
expect "$all" tools/versions.env
expect "$all" .github/workflows/near-approval.yml
expect "$all" tools/scripts/ci-areas.sh
expect "$all" $p/some-new-dir/file
expect "plain" $p/kani/mutants/01-guard.patch
expect "loops" $p/kani/unwind-rules.tsv
expect "kani" tools/scripts/run-kani.sh
expect "tla lean prolog" $p/tla/ApprovalCore.tla
expect "tla" tools/scripts/run-tla.sh
expect "lean" $p/lean/ApprovalLean/Step.lean $p/lean/lean-toolchain
expect "prolog" $p/prolog/requirements/r.pl
expect "plain lean prolog" $p/prolog/extracted/code_facts.pl
expect "tla lean prolog" $p/lean/Main.lean $p/tla/MC_Safety.cfg $p/strategy.md
expect "$all" $p/lean/Main.lean $p/kani/src/trace.rs

out=$("$areas" --all </dev/null | tr '\n' ' ')
[ "$out" = "plain=true loops=true kani=true tla=true lean=true prolog=true " ] ||
  { echo "FAIL: --all -> $out"; fail=1; }

[ "$fail" = 0 ] && echo "ci-areas: all cases pass"
exit "$fail"
