#!/usr/bin/env bash
# Run Verus verification on a project's verus crate.
#
# Usage: ./tools/scripts/run-verus.sh <project-name>
# Example: ./tools/scripts/run-verus.sh ironclaw

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

PROJECT="${1:?Usage: run-verus.sh <project-name>}"
VERUS_DIR="$ROOT_DIR/projects/$PROJECT/verus"

if [ ! -d "$VERUS_DIR" ]; then
    echo "Error: no verus directory at $VERUS_DIR"
    exit 1
fi

# Check for verus binary
if ! command -v verus &> /dev/null; then
    echo "Error: verus not found in PATH"
    echo "Install from: https://github.com/verus-lang/verus/releases/latest"
    exit 1
fi

echo "=== Running Verus verification for $PROJECT ==="
echo "Crate: $VERUS_DIR"
echo ""

verus "$VERUS_DIR/src/lib.rs" --crate-type=lib

echo ""
echo "=== Verification complete ==="
