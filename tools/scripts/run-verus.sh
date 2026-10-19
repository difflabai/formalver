#!/usr/bin/env bash
# Run Verus verification on a project's verus crate.
#
# Usage: ./tools/scripts/run-verus.sh <project-name>
# Example: ./tools/scripts/run-verus.sh near-approval
#
# Always compiles with --cfg 'feature="verus"' (F-10b): code gated on the
# crate's `verus` feature is otherwise never seen by Verus.
#
# A project whose verus/ holds REWRITES.toml is a "verified twin" of
# upstream code (strategy.md §7, path A). For it this script also:
# - fails if fewer than status.toml's verus_min_verified items verify;
# - requires verus/canary/false_lemma.rs to FAIL;
# - runs tools/scripts/erasure-check.py against the pinned upstream file;
# - applies each verus/mutants.toml mutant to a copy of src/ and requires
#   Verus to reject it.
# VERUS_LOG_DIR (optional) receives each run's output.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

PROJECT="${1:?Usage: run-verus.sh <project-name>}"
VERUS_DIR="$ROOT_DIR/projects/$PROJECT/verus"
LOG_DIR="${VERUS_LOG_DIR:-$(mktemp -d)}"
mkdir -p "$LOG_DIR"

if [ ! -d "$VERUS_DIR" ]; then
    echo "Error: no verus directory at $VERUS_DIR"
    exit 1
fi

# Check for verus binary
if ! command -v verus &> /dev/null; then
    echo "Error: verus not found in PATH (tools/scripts/get-verus.sh prints its directory)"
    exit 1
fi

. "$ROOT_DIR/tools/versions.env"
export RUSTUP_TOOLCHAIN="${VERUS_RUST_TOOLCHAIN:-${RUSTUP_TOOLCHAIN:-}}"

run_verus() { # <lib.rs> <log>
    verus "$1" --crate-type=lib --cfg 'feature="verus"' > "$2" 2>&1
}

echo "=== Running Verus verification for $PROJECT ==="
echo "Crate: $VERUS_DIR"
echo ""

fail=0
log="$LOG_DIR/verus.log"
if run_verus "$VERUS_DIR/src/lib.rs" "$log"; then
    status=ok
else
    status=failed
fi
cat "$log"
result=$(grep -o 'verification results:: [0-9]* verified, [0-9]* errors' "$log" | tail -1 || true)
if [ "$status" != ok ] || [ -z "$result" ]; then
    echo "::error::verus: $PROJECT does not verify"
    exit 1
fi

if [ ! -f "$VERUS_DIR/REWRITES.toml" ]; then
    echo ""
    echo "=== Verification complete ==="
    exit 0
fi

# --- verified twin checks -------------------------------------------------

verified=$(echo "$result" | awk '{print $3}')
floor=$(python3 -I -c 'import sys,tomllib; print(tomllib.load(open(sys.argv[1],"rb"))["project"].get("verus_min_verified", 0))' \
    "$ROOT_DIR/projects/$PROJECT/status.toml")
if [ "$verified" -lt "$floor" ]; then
    echo "::error::verus: $verified items verified, below verus_min_verified = $floor"
    fail=1
else
    echo "verus: $verified items verified (floor $floor)"
fi

if [ -f "$VERUS_DIR/canary/false_lemma.rs" ]; then
    if verus "$VERUS_DIR/canary/false_lemma.rs" > "$LOG_DIR/canary.log" 2>&1; then
        echo "::error::verus: canary false_lemma.rs verified; the toolchain proves false"
        fail=1
    else
        echo "verus: canary fails, as it must"
    fi
else
    echo "::error::verus: canary/false_lemma.rs missing"
    fail=1
fi

# Hygiene: trusted constructs live in src/trusted.rs only (TRUSTED.toml).
if grep -nE '\b(assume|admit)\(|external_body|assume_specification' \
    $(find "$VERUS_DIR/src" -name '*.rs' ! -name trusted.rs) > "$LOG_DIR/hygiene.log"; then
    cat "$LOG_DIR/hygiene.log"
    echo "::error::verus: trusted construct outside src/trusted.rs"
    fail=1
else
    echo "verus: hygiene ok (trusted constructs only in src/trusted.rs)"
fi

upstream_path=$(python3 -I -c 'import sys,tomllib; print(tomllib.load(open(sys.argv[1],"rb"))["project"]["upstream_path"])' \
    "$ROOT_DIR/projects/$PROJECT/status.toml")
upstream="$ROOT_DIR/projects/$PROJECT/source-mirror/$upstream_path/core/src/lib.rs"
if ! python3 -I "$SCRIPT_DIR/erasure-check.py" "$VERUS_DIR/src/lib.rs" "$upstream" "$VERUS_DIR/REWRITES.toml"; then
    echo "::error::verus: erasure check failed (twin and upstream differ in executable code)"
    fail=1
fi

if [ -f "$VERUS_DIR/mutants.toml" ]; then
    work=$(mktemp -d)
    trap 'rm -rf "$work"' EXIT
    ids=$(python3 -I -c 'import sys,tomllib; [print(m["id"]) for m in tomllib.load(open(sys.argv[1],"rb"))["mutant"]]' "$VERUS_DIR/mutants.toml")
    for id in $ids; do
        rm -rf "$work/src"
        cp -R "$VERUS_DIR/src" "$work/src"
        python3 -I - "$VERUS_DIR/mutants.toml" "$id" "$work/src" <<'PY'
import sys, tomllib, pathlib
muts, want, src = sys.argv[1], sys.argv[2], pathlib.Path(sys.argv[3])
m = next(m for m in tomllib.load(open(muts, "rb"))["mutant"] if m["id"] == want)
f = src / m["file"]
text = f.read_text()
if text.count(m["old"]) != 1:
    sys.exit(f"mutant {want}: `old` occurs {text.count(m['old'])} times in {m['file']}")
f.write_text(text.replace(m["old"], m["new"]))
PY
        if run_verus "$work/src/lib.rs" "$LOG_DIR/mutant-$id.log"; then
            echo "::error::verus: mutant $id survived"
            fail=1
        elif grep -q 'verification results::' "$LOG_DIR/mutant-$id.log"; then
            echo "verus: mutant $id killed"
        else
            echo "::error::verus: mutant $id did not compile (fix the mutant)"
            fail=1
        fi
    done
fi

echo ""
if [ "$fail" -ne 0 ]; then
    echo "=== Verification FAILED ==="
    exit 1
fi
echo "=== Verification complete ==="
