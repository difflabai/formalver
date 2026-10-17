#!/usr/bin/env bash
# Installs the cargo-near release pinned in tools/versions.env into <dir>
# (default: tools/.cargo-near) and prints the bin directory. The tarball is
# checked against the pinned sha256; no installer script runs.
#
# usage: bin=$(tools/scripts/get-cargo-near.sh [dir]); PATH="$bin:$PATH"
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
. "$root/tools/versions.env"
dir=${1:-$root/tools/.cargo-near}
bin="$dir/cargo-near-$CARGO_NEAR"
if [ -x "$bin/cargo-near" ]; then echo "$bin"; exit 0; fi

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) target=x86_64-unknown-linux-gnu sha=$CARGO_NEAR_LINUX_SHA256 ;;
  Darwin-arm64) target=aarch64-apple-darwin sha=$CARGO_NEAR_DARWIN_AARCH64_SHA256 ;;
  *) echo "get-cargo-near.sh: no pinned cargo-near for $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
tarball=cargo-near-$target.tar.gz
curl --proto '=https' --tlsv1.2 -LsSf -o "$tmp/$tarball" \
  "https://github.com/near/cargo-near/releases/download/cargo-near-v$CARGO_NEAR/$tarball"
got=$( (sha256sum "$tmp/$tarball" 2>/dev/null || shasum -a 256 "$tmp/$tarball") | cut -d' ' -f1)
if [ "$got" != "$sha" ]; then
  echo "get-cargo-near.sh: sha256 $got != pinned $sha" >&2; exit 1
fi
tar xzf "$tmp/$tarball" -C "$tmp"
mkdir -p "$bin"
install -m 0755 "$tmp/cargo-near-$target/cargo-near" "$bin/cargo-near"
echo "$bin"
