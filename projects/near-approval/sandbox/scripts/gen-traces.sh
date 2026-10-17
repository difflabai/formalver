#!/usr/bin/env bash
# Regenerates the RT-TRACE inputs in projects/near-approval/conformance/traces/
# (MC-2 format, strategy.md sections 5.11 and 9):
#   core-random.txt  200 seeded random sequences of 30 calls on the real core
#                    (kani mc2_core_traces; each step checked against tla.rs)
#   prolog.txt       traces of 80 calls from the Prolog step/4 (mc2.pl generate/2)
# Both generators are deterministic, so a diff means a generator or the
# core changed. Needs cargo (kani crate, plain mode) and scryer-prolog.
set -euo pipefail
proj="$(cd "$(dirname "$0")/../.." && pwd)"
out="$proj/conformance/traces"
mkdir -p "$out"
(cd "$proj/kani" && MC2_TRACES="${CORE_TRACES:-200}" MC2_LEN="${CORE_LEN:-30}" \
    cargo test --release --locked --lib mc2_core_traces -- --exact mc2::mc2_core_traces >/dev/null)
cp "$proj/kani/target/mc2/core.txt" "$out/core-random.txt"
(cd "$proj/prolog/verification" && scryer-prolog mc2.pl \
    -g "generate('$out/prolog.txt', ${PROLOG_TRACES:-10}), halt" </dev/null)
for f in "$out"/*.txt; do
    echo "$(basename "$f"): $(grep -c '^#$' "$f") traces, $(grep -vc '^#$' "$f") steps"
done
