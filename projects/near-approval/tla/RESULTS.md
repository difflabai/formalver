# near-approval: M1.5 results (TLA+ model refined by Kani)

Pin: trust-framework `3426c9246cee98dbfaa3ff7980bd85ff839d60d6` (PR #15:
reject, registration ids, revocation records; strategy.md section 17.6).
Tools: TLC 1.8.0 (tla2tools.jar), Apalache 0.47.2, OpenJDK 21; Kani 0.68.0
with CBMC 6.11.0. Machine: 4 cores, 15 GB. Commands:
`tools/scripts/run-tla.sh near-approval safety liveness apalache trace
mutants` and `tools/scripts/run-kani.sh near-approval h_ref_*`.

## TLA+

| Check | Result | Size / time |
|---|---|---|
| TLA-SAFE (TLC, `MC_Safety`, one storable payload) | no error | 8,629,059 distinct states, depth 21, 36 min on 4 workers |
| TLA-WIT (`Witness_Approved`, `_Rejected`, `_Void`, `_Revival`, `_Cap`) | each violated, as required | seconds |
| TLA-IND, `Init ⇒ Inv` (Apalache) | OK | 5 s |
| TLA-IND, `Inv ∧ Next ⇒ Inv'` | OK | 94 s |
| TLA-IND, `Inv ∧ Next ⇒ StepProps` | OK | 14 s |
| `IndWitness` (IndInit has approved, rejected and void requests and a revocation) | violated, as required | 8 s |
| TLA-LIVE-1 (TLC, `MC_Liveness`, with `Inv`) | no error | 199,145 distinct states, 38 s |
| TLA-LIVE-1 without fairness | violated, as required | seconds |
| REF-5, core vs `tla.rs` | 60 traces × 80 calls equal on every step; every error except `TooManyPending` and `LogFull` produced; ≥ 5 revival attempts, ≥ 20 rejections and revocations | < 1 s |
| REF-5, TLC `TraceCheck` | every trace accepted | 4,860 states, 7 s |

With two storable payloads `MC_Safety` passed 7M distinct states with the
queue still growing, too large for a 2-core CI runner. Two payloads only
matter for `ActionMismatch` between two storable actions, which Apalache
(`Payloads = {x, y}`) and the traces (three payloads) still cover.

## Spec mutants

All 15 killed (`tla/mutants/`):

| Mutant | Killed by |
|---|---|
| 01 `active_from` check dropped from `Live` | trace |
| 02 `SelfApproval` dropped from `ApproveErr` | trace |
| 03 pending not decremented on a decision | trace |
| 04 approve doesn't append to the log | trace |
| 05 `active_from` set to 0 on add | trace |
| 06 revoke leaves the key registered | trace |
| 07 `AlreadyRejected` / `AgentRevoked` order swapped | trace |
| 08 pending cap off by one | Apalache (`Inv9`) |
| 09 approval index taken from `#R` | trace |
| 10 `SelfApproval` dropped from `RejectErr` | trace |
| 11 `AlreadyRejected` guard dropped | trace |
| 12 rejection records the agent's registration id | trace |
| 13 revoke records no revocation | trace |
| 14 registration counter not incremented | trace |
| 15 request records registration id 0 | trace |

## Kani refinement harnesses

All pass with unwinding assertions on, every cover satisfied in its family
(local runs; CI runs each as its own job).

| Harness | Result | Time | Covers | Properties |
|---|---|---:|---|---|
| `h_ref_add` | verified | 6.0 min | 3/3 | REF-1..4 for `add_principal` |
| `h_ref_revoke` | verified | 9.1 min | 4/4 | same, `revoke_key` |
| `h_ref_request` | verified | 7.3 min | 5/6 | same, `request_action` |
| `h_ref_request_empty` | verified | 6.4 min | 5/6 | `""` instance; family 6/6 |
| `h_ref_approve` | verified | 12.8 min | 11/11 | same, `approve` |
| `h_ref_reject` | verified | 9.3 min | 10/10 | same, `reject` |
| `h_ref_toolong` | verified in CI | — | 2/2 | REF-1..3 for the `TooLong` class (A5), request and approve. Locally it ran out of memory while TLC shared the machine |

Plain mode runs the same refinement checks inside every `h_step_*` test.

## Not covered

- Constants are small (strategy.md section 17.3); `ASM-TLA-SCOPE` and
  `ASM-MODEL` carry the rest.
- A8 (each call is one atomic step) stays a runtime assumption (ASM-SEQ,
  ASM-ATOMIC).
- `TooManyPending` with the real cap of 16 is covered by Kani (`h_raw_request`),
  not by the traces.
