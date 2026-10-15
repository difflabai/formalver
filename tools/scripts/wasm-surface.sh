#!/usr/bin/env bash
# Export and import surface of the near-approval contract wasm
# (strategy.md SH-11, SH-12, C-6; section 9).
#
# usage: tools/scripts/wasm-surface.sh [--wasm FILE [--abi FILE]] [--update]
#
#   default    build `cargo near build non-reproducible-wasm --locked` in a
#              temporary copy of source-mirror/contracts/approval (the mirror
#              stays clean), then check the result.
#   --wasm     check an existing wasm instead of building (--abi: its ABI
#              JSON, as cargo-near writes next to it; without it the ABI part
#              of api_facts.pl is not compared).
#   --source   with --wasm: how that wasm was built, for the header --update
#              writes (default "given wasm").
#   --update   rewrite projects/near-approval/wasm-surface.expected and
#              prolog/extracted/api_facts.pl from this build instead of
#              comparing against them.
#
# Checks (exit 1 on any failure):
#   SH-11  function and non-function exports == wasm-surface.expected
#   SH-12  imports == wasm-surface.expected, and no import is a promise_*,
#          deploy, delete-account, transfer, add-key, yield/resume or
#          global-contract host function (checked even with --update)
#   C-6    prolog/extracted/api_facts.pl regenerates without a diff (the
#          facts C-6 compares with the requirements' API table)
#
# The parser below reads only the wasm import (2) and export (7) sections;
# it needs python3 and nothing else. cargo-near is needed only to build.
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
proj="$root/projects/near-approval"
expected="$proj/wasm-surface.expected"
facts="$proj/prolog/extracted/api_facts.pl"

wasm="" abi="" update=0 source=""
while [ $# -gt 0 ]; do
  case "$1" in
    --wasm) wasm=$2; shift 2 ;;
    --abi) abi=$2; shift 2 ;;
    --source) source=$2; shift 2 ;;
    --update) update=1; shift ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

work=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/wasm-surface.XXXXXX")
trap 'rm -rf "$work"' EXIT

build=${source:-given wasm}
if [ -z "$wasm" ]; then
  command -v cargo-near >/dev/null || { echo "cargo-near not found (tools/versions.env CARGO_NEAR)" >&2; exit 2; }
  cp -r "$proj/source-mirror/contracts/approval" "$work/approval"
  (cd "$work/approval/contract" && cargo near build non-reproducible-wasm --locked) >"$work/build.log" 2>&1 \
    || { tail -n 40 "$work/build.log"; echo "cargo near build failed" >&2; exit 1; }
  wasm="$work/approval/target/near/approval_contract/approval_contract.wasm"
  abi="$work/approval/target/near/approval_contract/approval_contract_abi.json"
  build="cargo near build non-reproducible-wasm --locked ($(cargo-near --version 2>/dev/null), $(rustc --version))"
fi
[ -f "$wasm" ] || { echo "no wasm at $wasm" >&2; exit 2; }
echo "wasm: $wasm"
echo "sha256: $(sha256sum "$wasm" | cut -d' ' -f1)"
echo "build: $build"

python3 -I - "$wasm" "${abi:-}" "$work/surface" "$work/api_facts.pl" <<'PY'
import json, sys

wasm_path, abi_path, surface_out, facts_out = sys.argv[1:5]
data = open(wasm_path, "rb").read()
if data[:4] != b"\0asm" or data[4:8] != b"\x01\0\0\0":
    sys.exit("not a wasm v1 module: " + wasm_path)

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

# SH-12: host functions that would give the contract an escape hatch.
# promise_* covers create, then, and, batch_*, yield_*, return and results.
FORBIDDEN = ("promise_", "deploy", "delete", "transfer", "add_key", "delete_key",
             "global_contract", "function_call")
bad = [f for (_, _, f) in imports if any(p in f for p in FORBIDDEN)]

lines = sorted("export %s %s" % e for e in exports) + sorted("import %s %s.%s" % imp for imp in imports)
with open(surface_out, "w") as out:
    out.write("\n".join(lines) + "\n")

# api_facts.pl (strategy section 8; read by consistency.pl, C-6).
SDK = {"contract_source_metadata", "__contract_abi"}  # generated by near-sdk / cargo-near
funcs = sorted(n for (k, n) in exports if k == "func")

def atom(x):
    """A Prolog atom: quoted unless it is a plain lower-case identifier."""
    import re
    if re.fullmatch(r"[a-z][a-zA-Z0-9_]*", x):
        return x
    return "'" + x.replace("\\", "\\\\").replace("'", "\\'") + "'"
facts = [
    "%% api_facts.pl -- GENERATED by tools/scripts/wasm-surface.sh; do not edit.",
    "%% The contract's API surface as built (strategy.md section 8, C-6):",
    "%%   api_method(Name)                     wasm function export that is a #[near] method",
    "%%   api_sdk_export(Name)                 wasm function export generated by near-sdk / cargo-near",
    "%%   api_abi_method(Name, Kind, Mods, Args)  ABI entry (Kind call | view; Mods e.g. [init, private])",
    "%% Regenerate with tools/scripts/wasm-surface.sh --update; CI fails on a diff.",
    "",
]
facts += ["api_method(%s)." % atom(n) for n in funcs if n not in SDK]
facts += ["api_sdk_export(%s)." % atom(n) for n in funcs if n in SDK]
if abi_path:
    abi = json.load(open(abi_path))
    for f in sorted(abi["body"]["functions"], key=lambda f: f["name"]):
        args = [a["name"] for a in f.get("params", {}).get("args", [])]
        facts.append("api_abi_method(%s, %s, [%s], [%s])." % (
            atom(f["name"]), atom(f["kind"]), ", ".join(map(atom, f.get("modifiers") or [])),
            ", ".join(map(atom, args))))
with open(facts_out, "w") as out:
    out.write("\n".join(facts) + "\n")

print("exports: %d (%d functions), imports: %d" % (len(exports), len(funcs), len(imports)))
if bad:
    print("SH-12 FAIL: forbidden imports: " + ", ".join(bad))
    sys.exit(3)
print("SH-12 ok: no promise/deploy/delete/transfer/add-key imports")
PY

if [ $update -eq 1 ]; then
  {
    echo "# wasm-surface.expected -- SH-11 (exports) and SH-12 (imports) of approval_contract.wasm"
    echo "# Generated by tools/scripts/wasm-surface.sh --update; review every change."
    echo "# Source: $build"
    echo "# sha256 of that build: $(sha256sum "$wasm" | cut -d' ' -f1) (not compared; non-reproducible builds may differ)"
    echo "# One line per export (kind name) and per import (kind module.name), sorted."
    cat "$work/surface"
  } >"$expected"
  if [ -n "$abi" ]; then cp "$work/api_facts.pl" "$facts"; else
    echo "note: no ABI given; api_facts.pl not rewritten" >&2; fi
  echo "updated $expected${abi:+ and $facts}"
  exit 0
fi

status=0
if diff -u <(grep -v '^#' "$expected") "$work/surface"; then
  echo "SH-11/SH-12 ok: surface equals wasm-surface.expected"
else
  echo "SH-11/SH-12 FAIL: surface differs from wasm-surface.expected" >&2; status=1
fi
if [ -n "$abi" ]; then
  if diff -u "$facts" "$work/api_facts.pl"; then echo "C-6 input ok: api_facts.pl up to date"
  else echo "FAIL: prolog/extracted/api_facts.pl is stale (rerun with --update)" >&2; status=1; fi
else
  echo "note: no ABI given; api_facts.pl not compared"
fi
exit $status
