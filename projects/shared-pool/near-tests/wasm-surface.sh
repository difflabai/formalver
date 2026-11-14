#!/usr/bin/env bash
# Export and import surface of the shared-pool wasm (pool_contract and
# pool_executor), in both builds the near-tests use:
#   plain  cargo build --target wasm32-unknown-unknown --release --locked
#          (exactly upstream scripts/build.sh)
#   near   the same with RUSTFLAGS="--cfg near" (as cargo-near builds)
#
# usage: projects/shared-pool/near-tests/wasm-surface.sh [--update]
#   --update   rewrite projects/shared-pool/wasm-surface.expected from this
#              build instead of comparing against it.
#   POOL_WASM_TARGET_DIR  build directory (default near-tests/target/wasm,
#              shared with the tests; one subdirectory per build).
#
# Each import line carries a class:
#   promise    promise_* host functions (the shell's receipts; expected)
#   forbidden  deploy / delete / add-key / transfer / stake / gas-key /
#              global-contract host functions (an escape hatch if reachable)
#   -          everything else
#
# Checks (SURF-1 and SURF-2 are local names; each tag line names the
# catalogue IDs the check bears on):
#   SURF-1  the surface (exports, imports, classes) == wasm-surface.expected.
#           Pins the exports to the documented methods plus
#           contract_source_metadata (no upgrade, migrate or reset export:
#           SH-11; it bears on ASM-DEPLOY), and records that the plain build
#           does not import panic_utf8, so its panics carry no message (SH-5,
#           finding NT-F1).
#           PROP: SH-5 SH-11 ASM-DEPLOY
#   SURF-2  no import is `forbidden`. If it held, the contracts could not
#           deploy code, delete the account or add keys (the in-contract
#           half of ASM-DEPLOY). It fails on the pin (NT-F3), so ASM-DEPLOY
#           stays an assumption.
#           PROP: ASM-DEPLOY
# Exit: 0 both hold; 1 SURF-1 fails (the surface changed: review, --update);
#       3 SURF-1 holds and SURF-2 fails with exactly the recorded imports
#       (the known finding NT-F3; run.sh reports it as expected-fail).
# The parser reads only the import (2) and export (7) sections; python3 only.
set -euo pipefail
export PATH="$HOME/.cargo/bin:$PATH"

here=$(cd "$(dirname "$0")" && pwd)
proj=$(cd "$here/.." && pwd)
expected="$proj/wasm-surface.expected"
update=0
[ "${1:-}" = --update ] && update=1

work=$(mktemp -d "${TMPDIR:-/tmp}/pool-surface.XXXXXX")
trap 'rm -rf "$work"' EXIT
target=${POOL_WASM_TARGET_DIR:-$here/target/wasm}
rustc_v=$(cd "$proj/source-mirror" && rustc --version)

: >"$work/surface"
for b in plain near; do
  flags=""
  [ $b = near ] && flags="--cfg near"
  (cd "$proj/source-mirror" && env -u CARGO_ENCODED_RUSTFLAGS RUSTFLAGS="$flags" CARGO_TARGET_DIR="$target/$b" \
    cargo build --target wasm32-unknown-unknown --release --locked -p pool-contract -p pool-executor) \
    >"$work/build-$b.log" 2>&1 || { tail -n 30 "$work/build-$b.log"; echo "wasm build ($b) failed" >&2; exit 2; }
  for w in pool_contract pool_executor; do
    f="$target/$b/wasm32-unknown-unknown/release/$w.wasm"
    echo "$b $w sha256 $(shasum -a 256 "$f" | cut -d' ' -f1) ($(wc -c <"$f" | tr -d ' ') bytes)"
    python3 -I - "$f" "$b $w" >>"$work/surface" <<'PY'
import sys
path, prefix = sys.argv[1], sys.argv[2]
data = open(path, "rb").read()
if data[:4] != b"\0asm" or data[4:8] != b"\x01\0\0\0":
    sys.exit("not a wasm v1 module: " + path)
def leb(buf, i):
    result = shift = 0
    while True:
        b = buf[i]; i += 1
        result |= (b & 0x7F) << shift
        shift += 7
        if not b & 0x80:
            return result, i
def name(buf, i):
    n, i = leb(buf, i)
    return buf[i:i + n].decode("utf-8"), i + n
def limits(buf, i):
    flags = buf[i]; i += 1
    _, i = leb(buf, i)
    if flags & 1:
        _, i = leb(buf, i)
    return i
KIND = {0: "func", 1: "table", 2: "memory", 3: "global", 4: "tag"}
imports, exports = [], []
i = 8
while i < len(data):
    sid = data[i]; i += 1
    size, i = leb(data, i)
    body, i = data[i:i + size], i + size
    if sid == 2:
        n, j = leb(body, 0)
        for _ in range(n):
            mod, j = name(body, j)
            field, j = name(body, j)
            kind = body[j]; j += 1
            if kind == 0:
                _, j = leb(body, j)
            elif kind == 1:
                j = limits(body, j + 1)
            elif kind == 2:
                j = limits(body, j)
            elif kind == 3:
                j += 2
            elif kind == 4:
                _, j = leb(body, j + 1)
            else:
                sys.exit("unknown import kind %d" % kind)
            imports.append((KIND[kind], mod, field))
    elif sid == 7:
        n, j = leb(body, 0)
        for _ in range(n):
            nm, j = name(body, j)
            kind = body[j]; j += 1
            _, j = leb(body, j)
            exports.append((KIND.get(kind, str(kind)), nm))
FORBIDDEN = ("deploy", "delete", "add_key", "add_gas_key", "transfer", "stake", "global_contract", "create_account")
def cls(field):
    if any(p in field for p in FORBIDDEN):
        return "forbidden"
    if field.startswith("promise_"):
        return "promise"
    return "-"
lines = sorted("%s export %s %s" % (prefix, k, n) for (k, n) in exports)
lines += sorted("%s import %s %s.%s %s" % (prefix, k, m, f, cls(f)) for (k, m, f) in imports)
print("\n".join(lines))
PY
  done
done

echo
for b in plain near; do
  for w in pool_contract pool_executor; do
    sel() { grep "^$b $w import .* $1\$" "$work/surface" | awk '{print $5}' | sed 's/^env\.//' | tr '\n' ' '; }
    echo "$b $w: $(grep -c "^$b $w export" "$work/surface") exports, $(grep -c "^$b $w import" "$work/surface") imports"
    echo "  promise:   $(sel promise)"
    echo "  forbidden: $(sel forbidden)"
    grep -q "^$b $w import func env.panic_utf8 " "$work/surface" && p=yes || p=no
    echo "  panic_utf8 imported: $p"
  done
done
echo

if [ $update -eq 1 ]; then
  {
    echo "# wasm-surface.expected -- exports and imports of the pinned shared-pool wasm"
    echo "# (difflabai/shared-pool-controls a4bb5c3c, PR #1 head)."
    echo "# Generated by near-tests/wasm-surface.sh --update; review every change."
    echo "# plain: cargo build --target wasm32-unknown-unknown --release --locked (scripts/build.sh), $rustc_v"
    echo "# near:  the same with RUSTFLAGS=\"--cfg near\" (cargo-near's cfg)"
    echo "# Line: <build> <wasm> export <kind> <name> | <build> <wasm> import <kind> <module.name> <class>"
    echo "# class: promise (promise_* host functions), forbidden (deploy/delete/add-key/transfer/"
    echo "# stake/gas-key/global-contract: present, linked by near-sdk's Promise; finding NT-F3), - (other)."
    cat "$work/surface"
  } >"$expected"
  echo "updated $expected"
  exit 0
fi

status=0
if diff -u <(grep -v '^#' "$expected") "$work/surface"; then
  echo "SURF-1 ok: surface equals wasm-surface.expected"
else
  echo "SURF-1 FAIL: surface differs from wasm-surface.expected" >&2
  exit 1
fi
nf=$(grep -c ' forbidden$' "$work/surface" || true)
if [ "$nf" -gt 0 ]; then
  echo "SURF-2 FAIL (known finding NT-F3): $nf forbidden host-function imports across the four wasm files;"
  echo "  the shell never calls them (tests trap any call), but the surface alone cannot rule them out."
  status=3
else
  echo "SURF-2 ok: no deploy/delete/add-key/transfer/stake/global-contract imports"
fi
exit $status
