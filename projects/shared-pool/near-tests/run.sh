#!/usr/bin/env bash
# Runner of the shared-pool shell layer (near-tests).
#
# usage: projects/shared-pool/near-tests/run.sh [test|mutants|surface|all] [args]
#   test     cargo test --locked --no-fail-fast (lockfile, shell, executor,
#            wedge, store_diff at the default 2,000 x 40 host and 300 x 40
#            wasm sequences per build; STORE_DIFF_SEQS / STORE_DIFF_STEPS /
#            STORE_DIFF_SEED / WASM_DIFF_SEQS override). The wasm of both
#            builds is built on first use into target/wasm/{plain,near}.
#   mutants  run-mutants.sh [patch-glob]: every mutants/*.patch must be killed
#            (the unpatched control must pass first).
#   surface  wasm-surface.sh: SURF-1 (surface == ../wasm-surface.expected)
#            must hold; SURF-2 (no deploy/delete/add-key/transfer imports)
#            fails on the pinned code with exactly the recorded imports, the
#            known finding NT-F3, reported as expected-fail (STRICT_SURFACE=1
#            makes it an error).
#   all      test, surface, mutants (default).
set -uo pipefail
export PATH="$HOME/.cargo/bin:$PATH"
here=$(cd "$(dirname "$0")" && pwd)
mode=${1:-all}
[ $# -gt 0 ] && shift

run_test() {
  (cd "$here" && cargo test --locked --no-fail-fast "$@")
}

run_surface() {
  "$here/wasm-surface.sh"
  local rc=$?
  if [ $rc -eq 3 ] && [ -z "${STRICT_SURFACE:-}" ]; then
    echo "surface: SURF-1 pass; SURF-2 expected-fail (known finding NT-F3)"
    return 0
  fi
  return $rc
}

run_mutants() {
  "$here/run-mutants.sh" "$@"
}

case "$mode" in
  test) run_test "$@" ;;
  surface) run_surface ;;
  mutants) run_mutants "$@" ;;
  all)
    s=0
    run_test || s=1
    run_surface || s=1
    run_mutants || s=1
    exit $s
    ;;
  *) echo "usage: $0 [test|mutants|surface|all]" >&2; exit 2 ;;
esac
