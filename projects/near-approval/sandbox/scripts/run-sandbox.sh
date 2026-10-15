#!/usr/bin/env bash
# The M6 sandbox job (strategy.md sections 9 and 14):
#   1. lockfile rule (check-lock.py);
#   2. helper contracts (build-res.sh);
#   3. every sandbox test, on APPROVAL_WASM (default: target/approval/...,
#      from scripts/build-wasm.sh).
# Extra arguments go to `cargo test` (e.g. `--test runtime`).
# Env: APPROVAL_WASM, APPROVAL_WASM_KIND (reproducible|non-reproducible),
# APPROVAL_WASM_EXPECTED_SHA256 (RT-CODEHASH asserts it), RT_TRACE_JOBS,
# RT_TRACE_LIMIT, SCRYER (scryer-prolog binary for RT-SPOOF and deploy.rs).
# Results land in results/*.json; a diff there is a changed runtime outcome.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-lock.py
scripts/build-res.sh
cargo test --locked "$@" -- --test-threads="${SANDBOX_TEST_THREADS:-2}"
