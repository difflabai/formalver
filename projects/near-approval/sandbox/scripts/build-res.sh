#!/usr/bin/env bash
# Builds the sandbox helper contracts (res/relay, res/selfacct, res/spoofer)
# to res/wasm/<name>.wasm. Uses cargo-near when it is on PATH, otherwise a
# plain wasm32 release build (RUSTFLAGS as cargo-near sets them).
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p res/wasm
for c in relay selfacct spoofer; do
    if command -v cargo-near >/dev/null; then
        cargo near build non-reproducible-wasm --manifest-path "res/$c/Cargo.toml" --no-abi --locked
        cp "target/near/sandbox_$c/sandbox_$c.wasm" "res/wasm/$c.wasm"
    else
        RUSTFLAGS="-C link-arg=-s -C target-cpu=mvp" \
            cargo build -p "sandbox-$c" --release --target wasm32-unknown-unknown --locked
        cp "target/wasm32-unknown-unknown/release/sandbox_$c.wasm" "res/wasm/$c.wasm"
    fi
    echo "res/wasm/$c.wasm $(sha256sum "res/wasm/$c.wasm" | cut -d' ' -f1)"
done
