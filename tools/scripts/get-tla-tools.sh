#!/usr/bin/env bash
# Downloads the pinned TLA+ tools (tools/versions.env) into tools/.cache and
# checks their sha256. Prints the directory. Idempotent.
#
# usage: tools/scripts/get-tla-tools.sh
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
. "$root/tools/versions.env"
cache=${TLA_CACHE:-$root/tools/.cache}
mkdir -p "$cache"

fetch() { # url file sha256
  if [ ! -f "$cache/$2" ] || ! echo "$3  $cache/$2" | sha256sum -c --status; then
    curl -fsSL --retry 4 -o "$cache/$2.part" "$1"
    echo "$3  $cache/$2.part" | sha256sum -c --quiet
    mv "$cache/$2.part" "$cache/$2"
  fi
}

fetch "https://github.com/tlaplus/tlaplus/releases/download/v$TLA2TOOLS/tla2tools.jar" \
  "tla2tools-$TLA2TOOLS.jar" "$TLA2TOOLS_SHA256"
fetch "https://github.com/apalache-mc/apalache/releases/download/v$APALACHE/apalache-$APALACHE.tgz" \
  "apalache-$APALACHE.tgz" "$APALACHE_SHA256"
if [ ! -x "$cache/apalache-$APALACHE/bin/apalache-mc" ]; then
  mkdir -p "$cache/apalache-$APALACHE"
  tar xzf "$cache/apalache-$APALACHE.tgz" -C "$cache/apalache-$APALACHE" --strip-components=1
fi
echo "$cache"
