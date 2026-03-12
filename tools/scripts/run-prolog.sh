#!/usr/bin/env bash
# Run Prolog verification tests for a project.
#
# Usage: ./tools/scripts/run-prolog.sh <project-name> [test-file]
# Example: ./tools/scripts/run-prolog.sh ironclaw
# Example: ./tools/scripts/run-prolog.sh ironclaw test_sanitizer.pl

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"

PROJECT="${1:?Usage: run-prolog.sh <project-name> [test-file]}"
TEST_FILE="${2:-}"
PROLOG_DIR="$ROOT_DIR/projects/$PROJECT/prolog"

if [ ! -d "$PROLOG_DIR" ]; then
    echo "Error: no prolog directory at $PROLOG_DIR"
    exit 1
fi

# Check for scryer-prolog binary
if ! command -v scryer-prolog &> /dev/null; then
    echo "Error: scryer-prolog not found in PATH"
    echo "Install with: cargo install scryer-prolog"
    exit 1
fi

echo "=== Running Prolog verification for $PROJECT ==="

if [ -n "$TEST_FILE" ]; then
    # Run specific test file
    TEST_PATH="$PROLOG_DIR/tests/$TEST_FILE"
    if [ ! -f "$TEST_PATH" ]; then
        echo "Error: test file not found at $TEST_PATH"
        exit 1
    fi
    echo "Test: $TEST_PATH"
    echo ""
    cd "$PROLOG_DIR/tests"
    scryer-prolog "$TEST_FILE" -g "run_tests, halt."
else
    # Run all test files
    for test in "$PROLOG_DIR/tests/"*.pl; do
        if [ -f "$test" ]; then
            echo "--- $(basename "$test") ---"
            cd "$PROLOG_DIR/tests"
            scryer-prolog "$(basename "$test")" -g "run_tests, halt." || true
            echo ""
        fi
    done
fi

echo "=== Prolog verification complete ==="
