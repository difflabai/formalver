#!/usr/bin/env bash
# Builds the approval contract wasm under test into
# target/approval/near/approval_contract/approval_contract.wasm (the tests'
# default; APPROVAL_WASM overrides it).
#
#   scripts/build-wasm.sh                 cargo near build non-reproducible-wasm
#   scripts/build-wasm.sh reproducible    cargo near build reproducible-wasm (Docker,
#                                         the image pinned in contract/Cargo.toml)
#
# Prints the sha256 (hex) and NEAR code_hash (base58) of the result.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
contract="$here/../source-mirror/contracts/approval/contract"
mode="${1:-non-reproducible}"
export CARGO_TARGET_DIR="$here/target/approval"
cd "$contract"
case "$mode" in
    non-reproducible) cargo near build non-reproducible-wasm --locked ;;
    reproducible)
        # Writes to the crate's own target/near; copy it to where the tests look.
        cargo near build reproducible-wasm
        mkdir -p "$CARGO_TARGET_DIR/near/approval_contract"
        cp "$contract/../target/near/approval_contract/approval_contract.wasm" \
            "$CARGO_TARGET_DIR/near/approval_contract/approval_contract.wasm"
        ;;
    *) echo "usage: $0 [non-reproducible|reproducible]" >&2; exit 2 ;;
esac
wasm="$CARGO_TARGET_DIR/near/approval_contract/approval_contract.wasm"
echo "$mode" > "$CARGO_TARGET_DIR/near/approval_contract/BUILD_KIND"
python3 - "$wasm" <<'PY'
import hashlib, sys
d = hashlib.sha256(open(sys.argv[1], "rb").read()).digest()
A = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
n = int.from_bytes(d, "big"); s = ""
while n: n, r = divmod(n, 58); s = A[r] + s
s = "1" * (len(d) - len(d.lstrip(b"\0"))) + s
print(f"{sys.argv[1]}\n  sha256    {d.hex()}\n  code_hash {s}")
PY
