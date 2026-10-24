#!/usr/bin/env bash
# The M6 sandbox job (strategy.md sections 9 and 14):
#   1. lockfile rule (check-lock.py);
#   2. helper contracts (build-res.sh);
#   3. every sandbox test, on APPROVAL_WASM (default: target/approval/...,
#      from scripts/build-wasm.sh).
# Extra arguments go to `cargo test` (e.g. `--test runtime`).
# Sets NEAR_SANDBOX_BIN_PATH to a sha256-checked binary (scripts/sandbox-bin.sh)
# so near-workspaces does not download one with ureq. That download is cached
# with no hash check, including a copy fetched before the eMudhra distrust.
# Env: APPROVAL_WASM, APPROVAL_WASM_KIND (reproducible|non-reproducible),
# APPROVAL_WASM_EXPECTED_SHA256 (RT-CODEHASH asserts it), RT_TRACE_JOBS,
# RT_TRACE_LIMIT, SCRYER (scryer-prolog binary for RT-SPOOF and deploy.rs).
# Recorded outcomes are checked against results/*.json: a difference fails
# the test and lands in results/*.observed.json. SANDBOX_RECORD=1 rewrites
# the committed files instead (after reviewing the change).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check-lock.py
scripts/build-res.sh
NEAR_SANDBOX_BIN_PATH=$(scripts/sandbox-bin.sh)
export NEAR_SANDBOX_BIN_PATH
cargo test --locked "$@" -- --test-threads="${SANDBOX_TEST_THREADS:-2}"
