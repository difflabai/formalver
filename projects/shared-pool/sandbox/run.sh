#!/usr/bin/env bash
# Runtime layer runner (shared-pool). Exit 0 = every check passes.
#
#   1. lockfile rule: every registry package shared with the source mirror is
#      at the mirror's version (scripts/check-lock.py);
#   2. the contracts under test from the pinned mirror, two variants with
#      their own CARGO_TARGET_DIR, sha256 to results/wasm.json
#      (scripts/build-wasm.sh): `upstream` (upstream scripts/build.sh exactly)
#      and `cfg-near` (the same with RUSTFLAGS="--cfg near");
#   3. the helper contract relay/ (scripts/build-res.sh);
#   4. a sha256-checked near-sandbox 2.13.4 (scripts/sandbox-bin.sh), so
#      near-workspaces does not download an unchecked one;
#   5. tests/runtime.rs (RT-PRED, RT-PRIVATE, RT-CALLBACK, RT-REVERT,
#      RT-RACE, RT-WEDGE, SB-1) on each variant, then tests/resources.rs
#      (RES-1) on each variant. Results: results/<variant>/<ID>.json.
#
# Env: SANDBOX_VARIANTS (default "upstream cfg-near"), SANDBOX_TEST_THREADS
# (default 3), SANDBOX_SKIP_RES=1 skips RES-1 (about 7 minutes per variant),
# SANDBOX_SKIP_BUILD=1 reuses the built wasm (still checks the lock),
# POOL_TOOLCHAIN overrides the channel read from
# ../source-mirror/rust-toolchain.toml.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.cargo/bin:$PATH"
# The upstream channel, read as the workflow's sandbox job reads it, so a
# re-pin that changes rust-toolchain.toml changes the toolchain here too.
# POOL_TOOLCHAIN, if set, overrides it; it is passed on to
# scripts/build-wasm.sh and scripts/build-res.sh.
channel=${POOL_TOOLCHAIN:-$(sed -n 's/^channel *= *"\(.*\)"$/\1/p' ../source-mirror/rust-toolchain.toml)}
[ -n "$channel" ] || { echo "no channel in ../source-mirror/rust-toolchain.toml" >&2; exit 2; }
export POOL_TOOLCHAIN="$channel"
toolchain="+$channel"
start=$(date +%s)

python3 scripts/check-lock.py results/lock-check.json
if [ "${SANDBOX_SKIP_BUILD:-0}" != 1 ]; then
    scripts/build-wasm.sh > /dev/null
    scripts/build-res.sh
fi
NEAR_SANDBOX_BIN_PATH="$(scripts/sandbox-bin.sh)"
export NEAR_SANDBOX_BIN_PATH

threads="${SANDBOX_TEST_THREADS:-3}"
for v in ${SANDBOX_VARIANTS:-upstream cfg-near}; do
    echo "== runtime tests, POOL_WASM_VARIANT=$v"
    POOL_WASM_VARIANT="$v" cargo "$toolchain" test --locked --test runtime -- --test-threads="$threads"
done
if [ "${SANDBOX_SKIP_RES:-0}" != 1 ]; then
    for v in ${SANDBOX_VARIANTS:-upstream cfg-near}; do
        echo "== RES-1, POOL_WASM_VARIANT=$v"
        POOL_WASM_VARIANT="$v" cargo "$toolchain" test --locked --test resources
    done
fi
echo "sandbox layer: all checks passed in $(( $(date +%s) - start ))s"
