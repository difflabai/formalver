#!/usr/bin/env bash
# Builds the approval contract wasm under test into
# target/approval/near/approval_contract/approval_contract.wasm (the tests'
# default; APPROVAL_WASM overrides it).
#
#   scripts/build-wasm.sh                 cargo near build non-reproducible-wasm
#   scripts/build-wasm.sh reproducible    cargo near build reproducible-wasm (Docker,
#                                         the image pinned in contract/Cargo.toml)
#   scripts/build-wasm.sh reproducible-manual
#                                         the same container build run by hand, for
#                                         hosts where cargo-near's own `docker run`
#                                         can't reach crates.io or Docker Hub: the
#                                         image must already be present locally
#                                         under its pinned name; HTTPS_PROXY and
#                                         CARGO_HTTP_CAINFO are passed through (they
#                                         are not embedded in the wasm). The NEP-330
#                                         environment is the one cargo-near 0.22.0
#                                         sets (seen with `cargo near --teach-me`).
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
        # cargo-near opens the contract's git repository with libgit2 and
        # clones it to a build site. From inside the source-mirror submodule
        # (a `.git` file, not a directory) it resolves formalver's repository
        # instead, then needs credentials for its remote. Build from a plain
        # local clone of the mirror at the same commit: a filesystem clone
        # needs no network or credentials, and the wasm records the commit
        # and the Cargo.toml repository URL, not where the clone lives.
        repo="$(git -C "$contract" rev-parse --show-toplevel)"
        rev="$(git -C "$repo" rev-parse HEAD)"
        [ -z "$(git -C "$repo" status --porcelain)" ] || { echo "$repo is dirty" >&2; exit 1; }
        rel="$(git -C "$contract" rev-parse --show-prefix)"
        clone="$(mktemp -d)/trust-framework"
        trap 'rm -rf "$(dirname "$clone")"' EXIT
        git clone --quiet --no-checkout "$repo" "$clone"
        git -C "$clone" checkout --quiet --detach "$rev"
        # Without CARGO_TARGET_DIR: cargo-near looks for the container's output
        # under the host's target directory, which the container never sees.
        out="$CARGO_TARGET_DIR/near/approval_contract"
        (cd "$clone/$rel" && env -u CARGO_TARGET_DIR cargo near build reproducible-wasm --out-dir "$out") ;;
    reproducible-manual)
        repo="$(git -C "$contract" rev-parse --show-toplevel)"
        rev="$(git -C "$repo" rev-parse HEAD)"
        [ -z "$(git -C "$repo" status --porcelain)" ] || { echo "$repo is dirty" >&2; exit 1; }
        meta="$(cargo metadata --format-version 1 --no-deps --manifest-path "$contract/Cargo.toml")"
        read -r image digest repo_url < <(python3 -c '
import json, sys
m = json.load(sys.stdin)
p = next(p for p in m["packages"] if p["name"] == "approval-contract")
rb = p["metadata"]["near"]["reproducible_build"]
print(rb["image"], rb["image_digest"], p["repository"])' <<<"$meta")
        work="$(mktemp -d)"
        git clone -q "$repo" "$work/code"
        git -C "$work/code" checkout -q "$rev"
        env_args=(
            --env "NEP330_BUILD_INFO_BUILD_ENVIRONMENT=$image@$digest"
            --env "NEP330_BUILD_INFO_SOURCE_CODE_SNAPSHOT=git+$repo_url?rev=$rev"
            --env "NEP330_BUILD_INFO_CONTRACT_PATH=contracts/approval/contract"
            --env "NEP330_LINK=$repo_url/tree/$rev"
        )
        proxy_args=()
        if [ -n "${HTTPS_PROXY:-}" ]; then
            proxy_args+=(--network host --env "HTTPS_PROXY=$HTTPS_PROXY")
        fi
        if [ -n "${CARGO_HTTP_CAINFO:-}" ]; then
            proxy_args+=(--volume "$CARGO_HTTP_CAINFO:/ca.crt:ro" --env CARGO_HTTP_CAINFO=/ca.crt)
        fi
        docker run -u "$(id -u):$(id -g)" --rm --volume "$work/code:/home/near/code:z" \
            --workdir /home/near/code/contracts/approval/contract \
            "${env_args[@]}" "${proxy_args[@]}" "$image@$digest" \
            /bin/bash -c 'cargo near build non-reproducible-wasm --locked'
        mkdir -p "$CARGO_TARGET_DIR/near/approval_contract"
        cp "$work/code/contracts/approval/target/near/approval_contract/approval_contract.wasm" \
            "$CARGO_TARGET_DIR/near/approval_contract/approval_contract.wasm"
        mode=reproducible
        ;;
    *) echo "usage: $0 [non-reproducible|reproducible|reproducible-manual]" >&2; exit 2 ;;
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
