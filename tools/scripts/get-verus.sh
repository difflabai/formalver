#!/usr/bin/env bash
# Downloads the pinned Verus release (tools/versions.env) into VERUS_CACHE
# (default tools/.cache), checks its sha256 and installs the rustup
# toolchain it needs. Prints the directory holding `verus`. Idempotent.
#
# usage: tools/scripts/get-verus.sh
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
. "$root/tools/versions.env"
cache=${VERUS_CACHE:-$root/tools/.cache}
mkdir -p "$cache"

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) plat=x86-linux; sha=$VERUS_LINUX_SHA256 ;;
  Darwin-arm64) plat=arm64-macos; sha=$VERUS_DARWIN_AARCH64_SHA256 ;;
  *) echo "no pinned Verus build for $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac

hash() {
  if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | awk '{print $1}'
}

rustup toolchain list | grep -q "^$VERUS_RUST_TOOLCHAIN-" ||
  rustup toolchain install "$VERUS_RUST_TOOLCHAIN" --profile minimal >&2

name="verus-$VERUS-$plat"
dest="$cache/$name-${sha:0:12}"
# Same install pattern as get-lean.sh: unpack in a per-process temp
# directory, then rename the complete tree into place.
find "$cache" -maxdepth 1 -name "$name.??????" -mmin +60 -exec rm -rf {} +
if [ ! -x "$dest/verus" ]; then
  tmp=$(mktemp -d "$cache/$name.XXXXXX")
  trap 'rm -rf "$tmp"' EXIT
  curl -fsSL --retry 4 --retry-all-errors -o "$tmp/$name.zip" \
    "https://github.com/verus-lang/verus/releases/download/release/$VERUS/$name.zip"
  if [ "$(hash "$tmp/$name.zip")" != "$sha" ]; then
    echo "sha256 mismatch for $name.zip (got $(hash "$tmp/$name.zip"), pinned $sha)" >&2
    exit 1
  fi
  unzip -q "$tmp/$name.zip" -d "$tmp"
  uniq=$(basename "$tmp")
  mv "$tmp/verus-$plat" "$tmp/$uniq"
  if [ ! -e "$dest" ]; then
    mv "$tmp/$uniq" "$dest" 2>/dev/null || true
    rm -rf "${dest:?}/$uniq"
  fi
  [ -x "$dest/verus" ] || { echo "could not install $dest" >&2; exit 1; }
fi
echo "$dest"
