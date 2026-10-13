#!/usr/bin/env bash
# Downloads the pinned Lean 4 toolchain (tools/versions.env) into
# LEAN_CACHE (default tools/.cache) and checks its sha256. Prints the
# toolchain's bin directory (lean, lake). Idempotent. Checks that every
# lean-toolchain file under projects/ names the same version.
#
# usage: tools/scripts/get-lean.sh
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
. "$root/tools/versions.env"
cache=${LEAN_CACHE:-$root/tools/.cache}
mkdir -p "$cache"

for f in "$root"/projects/*/lean/lean-toolchain; do
  [ -f "$f" ] || continue
  if [ "$(cat "$f")" != "leanprover/lean4:v$LEAN" ]; then
    echo "$f says $(cat "$f"), tools/versions.env says v$LEAN" >&2
    exit 1
  fi
done

case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) plat=linux; sha=$LEAN_LINUX_SHA256 ;;
  Darwin-arm64) plat=darwin_aarch64; sha=$LEAN_DARWIN_AARCH64_SHA256 ;;
  *) echo "no pinned Lean build for $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac

hash() {
  if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | awk '{print $1}'
}

name="lean-$LEAN-$plat"
if [ ! -x "$cache/$name/bin/lake" ]; then
  curl -fsSL --retry 4 --retry-all-errors -o "$cache/$name.zip.part" \
    "https://github.com/leanprover/lean4/releases/download/v$LEAN/$name.zip"
  if [ "$(hash "$cache/$name.zip.part")" != "$sha" ]; then
    echo "sha256 mismatch for $name.zip" >&2
    rm -f "$cache/$name.zip.part"
    exit 1
  fi
  rm -rf "$cache/$name"
  unzip -q "$cache/$name.zip.part" -d "$cache"
  rm -f "$cache/$name.zip.part"
fi
echo "$cache/$name/bin"
