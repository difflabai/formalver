#!/usr/bin/env bash
# Builds the two wasm files under test from the pinned source mirror, in two
# variants, each with its own CARGO_TARGET_DIR so the mirror stays clean:
#
#   upstream  exactly upstream scripts/build.sh: `cargo build -p pool-contract
#             -p pool-executor --target wasm32-unknown-unknown --release
#             --locked` (toolchain 1.98 from the mirror's rust-toolchain.toml,
#             release profile with overflow-checks = true), no RUSTFLAGS.
#             -> target/pool/wasm32-unknown-unknown/release/*.wasm
#   cfg-near  the same plus RUSTFLAGS="--cfg near", the cfg cargo-near sets.
#             near-sdk 5.29.1 (lib.rs, its compile_error! text) documents
#             target_family = "wasm" without cfg(near) as "uses pure-Rust
#             fallbacks. not for on-chain use"; in particular
#             near_sdk_env::panic_str only calls the panic_utf8 host function
#             under cfg(near), so the upstream build turns every panic message
#             into a bare `unreachable` trap (finding SB-1, RESULTS.md).
#             -> target/pool-near/wasm32-unknown-unknown/release/*.wasm
#
# Writes results/wasm.json (sha256, NEAR code_hash, size, rustc, flags).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
mirror="$here/../source-mirror"
export PATH="$HOME/.cargo/bin:$PATH"
toolchain="${POOL_TOOLCHAIN:-1.98}"
cd "$mirror"
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS
CARGO_TARGET_DIR="$here/target/pool" \
    cargo "+$toolchain" build -p pool-contract -p pool-executor \
    --target wasm32-unknown-unknown --release --locked
CARGO_TARGET_DIR="$here/target/pool-near" RUSTFLAGS="--cfg near" \
    cargo "+$toolchain" build -p pool-contract -p pool-executor \
    --target wasm32-unknown-unknown --release --locked
rustc_v="$(rustc "+$toolchain" --version)"
commit="$(git -C "$mirror" rev-parse HEAD 2>/dev/null || echo unknown)"
dirty="$( [ -z "$(git -C "$mirror" status --porcelain 2>/dev/null)" ] && echo false || echo true)"
python3 - "$here" "$rustc_v" "$commit" "$dirty" <<'PY'
import hashlib, json, pathlib, sys
here, rustc, commit, dirty = sys.argv[1:]
here = pathlib.Path(here)
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58(d):
    n = int.from_bytes(d, "big"); s = ""
    while n:
        n, r = divmod(n, 58); s = A[r] + s
    return "1" * (len(d) - len(d.lstrip(b"\0"))) + s
cmd = "cargo +1.98 build -p pool-contract -p pool-executor --target wasm32-unknown-unknown --release --locked"
variants = {}
for variant, tdir, flags in [("upstream", "target/pool", ""), ("cfg-near", "target/pool-near", "--cfg near")]:
    wasm = {}
    for name in ["pool_contract", "pool_executor"]:
        p = here / tdir / "wasm32-unknown-unknown/release" / f"{name}.wasm"
        b = p.read_bytes()
        d = hashlib.sha256(b).digest()
        wasm[name] = {"path": str(p.relative_to(here)), "sha256": d.hex(), "code_hash": b58(d), "bytes": len(b)}
    variants[variant] = {"RUSTFLAGS": flags, "command": cmd, "wasm": wasm}
manifest = {
    "source_commit": commit,
    "source_dirty": dirty == "true",
    "rustc": rustc,
    "profile": "mirror [profile.release]: codegen-units=1, opt-level=z, lto, panic=abort, overflow-checks=true",
    "default_variant": "upstream",
    "variants": variants,
}
(here / "results").mkdir(exist_ok=True)
(here / "results/wasm.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
PY
