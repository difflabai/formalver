#!/usr/bin/env bash
# Print a sha256-checked near-sandbox 2.13.4 binary, and drop any copy the
# near-sandbox crate cached before rustls-webpki 0.103.16.
#
# near-workspaces downloads in its build script, before tests run, and reuses
# that file with no hash check. Export the printed path as NEAR_SANDBOX_BIN_PATH
# before `cargo test`. Hashes match trust-framework scripts/near/sandbox.sh
# (recorded 2026-10-19). The pinned mirror does not have that script yet.
set -euo pipefail

VER=2.13.4
MARK=rustls-webpki-0.103.16
ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
CACHE=${SANDBOX_BIN_CACHE:-"$HOME/.cache/formalver/near-sandbox"}

pinned_sha256() {
  case "$1" in
    Darwin-arm64) echo 158cedb02e5a83d51b47c16e13cd04a84abf493f1f38688ee257cb0263450631 ;;
    Linux-x86_64) echo 5690a4635172263cf026683f75965cac09dd916912584f12709974fed620163f ;;
    Linux-aarch64) echo edd77d6d28b960852243fc6f45656c97a7976fc2b3cfe53cda89324a6804bd30 ;;
    *) echo "" ;;
  esac
}

platform() {
  case "$(uname -s):$(uname -m)" in
    Darwin:arm64) echo Darwin-arm64 ;;
    Linux:x86_64) echo Linux-x86_64 ;;
    Linux:aarch64 | Linux:arm64) echo Linux-aarch64 ;;
    *) echo "near-sandbox has no build for $(uname -s) $(uname -m)" >&2; exit 1 ;;
  esac
}

sha256_hex() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{ print $1 }'
  else
    shasum -a 256 "$1" | awk '{ print $1 }'
  fi
}

# ureq's cache. ~/.near is global_install. OUT_DIR/.near is the default.
# A binary fetched while the compromised intermediates were trusted must not
# be reused after the lockfile bump. The stamp is the distrust generation.
drop_ureq_cache() {
  local cache stamp target
  if [ -n "${HOME:-}" ]; then
    cache="$HOME/.near/near-sandbox-$VER"
    stamp="$cache/.emudhra-distrust"
    if [ ! -f "$stamp" ] || [ "$(cat "$stamp" 2>/dev/null || true)" != "$MARK" ]; then
      rm -rf "$cache"
      mkdir -p "$cache"
      printf '%s\n' "$MARK" >"$stamp"
    fi
  fi
  target="$ROOT/target"
  if [ -d "$target" ]; then
    stamp="$target/.emudhra-distrust"
    if [ ! -f "$stamp" ] || [ "$(cat "$stamp" 2>/dev/null || true)" != "$MARK" ]; then
      find "$target" -path "*/near-sandbox-$VER/near-sandbox" -delete 2>/dev/null || true
      find "$target" -path "*/near-sandbox-$VER/near-sandbox.tmp" -delete 2>/dev/null || true
      printf '%s\n' "$MARK" >"$stamp"
    fi
  fi
}

plat=$(platform)
sha=$(pinned_sha256 "$plat")
[ -n "$sha" ] || { echo "no pinned sha256 for near-sandbox $VER on $plat" >&2; exit 1; }
bin="$CACHE/near-sandbox-$VER-$plat/near-sandbox"
if [ ! -x "$bin" ]; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  url="https://s3-us-west-1.amazonaws.com/build.nearprotocol.com/nearcore/$plat/$VER/near-sandbox.tar.gz"
  echo "Downloading near-sandbox $VER ($plat)" >&2
  curl --proto '=https' --tlsv1.2 -fsSL --retry 3 -o "$tmp/near-sandbox.tar.gz" "$url"
  got=$(sha256_hex "$tmp/near-sandbox.tar.gz")
  [ "$got" = "$sha" ] || { echo "sha256 mismatch for $url" >&2; echo "expected $sha" >&2; echo "got      $got" >&2; exit 1; }
  mkdir -p "$tmp/x"
  tar -xzf "$tmp/near-sandbox.tar.gz" -C "$tmp/x"
  f=$(find "$tmp/x" -type f -name near-sandbox | head -n 1)
  [ -n "$f" ] || { echo "near-sandbox binary not found in the tarball" >&2; exit 1; }
  mkdir -p "$(dirname "$bin")"
  install -m 0755 "$f" "$bin"
fi
drop_ureq_cache
printf '%s\n' "$bin"
