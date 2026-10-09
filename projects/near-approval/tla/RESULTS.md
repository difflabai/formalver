# near-approval: M1.5 results (TLA+ model refined by Kani)

Pin: trust-framework `5736251d65c6bc11c20e5f27ddc869db27bd7299` (see
strategy.md section 17.6 for the gap to PR #15). Tools: TLC 1.8.0
(tla2tools.jar), Apalache 0.47.2, OpenJDK 21; Kani 0.68.0 with CBMC 6.11.0.
Machine: 4 cores, 15 GB. Commands: `tools/scripts/run-tla.sh near-approval
safety liveness apalache trace mutants` and `tools/scripts/run-kani.sh
near-approval h_ref_*`.

## TLA+

| Check | Result | Size / time |
|---|---|---|
| TLA-SAFE (TLC, `MC_Safety`) | no error | 1,831,373 distinct states, depth 23, 10 min 21 s on 2 workers |
| TLA-WIT (`Witness_Approved`, `_Void`, `_Revival`, `_Cap`) | each violated, as required | seconds |
| TLA-IND, `Init ⇒ Inv` (Apalache) | OK | 10 s |
| TLA-IND, `Inv ∧ Next ⇒ Inv'` | OK | 27 s |
| TLA-IND, `Inv ∧ Next ⇒ StepProps` | OK | 20 s |
| `IndWitness` (IndInit not vacuous) | violated, as required | 10 s |
| TLA-LIVE-1 (TLC, `MC_Liveness`, with `Inv`) | no error | 17,602 distinct states, 6 s |
| TLA-LIVE-1 without fairness | violated, as required | 3 s |
| REF-5, core vs `tla.rs` | 60 traces × 80 calls equal on every step; every error except `TooManyPending` and `LogFull` produced; ≥ 5 revival attempts | < 1 s |
| REF-5, TLC `TraceCheck` | every trace accepted | 4,860 states, 12 s |

## Spec mutants

All 9 killed (`tla/mutants/`):

| Mutant | Killed by |
|---|---|
| 01 `active_from` check dropped from `Live` | trace (also Apalache `StepProps`) |
| 02 `SelfApproval` guard dropped | trace (also Apalache `Inv`) |
| 03 pending not decremented on approve | trace |
| 04 approve doesn't append to the log | trace |
| 05 `active_from` set to 0 on add | trace |
| 06 revoke leaves the key registered | trace |
| 07 `AlreadyApproved` / `AgentRevoked` order swapped | trace |
| 08 pending cap off by one | Apalache (`Inv9`) |
| 09 approval index taken from `#R` | trace |

## Kani refinement harnesses

All pass with unwinding assertions on, every cover satisfied in its family.

| Harness | Result | Time | Covers | Properties |
|---|---|---:|---|---|
| `h_ref_add` | verified | 3.6 min | 3/3 | REF-1..4 for `add_principal` |
| `h_ref_revoke` | verified | 5.1 min | 4/4 | same, `revoke_key` |
| `h_ref_request` | verified | 4.2 min | 5/6 | same, `request_action` |
| `h_ref_request_empty` | verified | 3.6 min | 5/6 | `""` instance; family 6/6 |
| `h_ref_approve` | verified | 6.0 min | 10/10 | same, `approve` |
| `h_ref_toolong` | verified | 9.0 min | 2/2 | REF-1..3 for the `TooLong` class (A5), request and approve |

Plain mode runs the same refinement checks inside every `h_step_*` test, and
dropping the pending decrement from `tla.rs` fails them (REF-2).

## Not covered

- Constants are small (strategy.md section 17.3); `ASM-TLA-SCOPE` and
  `ASM-MODEL` carry the rest.
- A8 (each call is one atomic step) stays a runtime assumption (ASM-SEQ,
  ASM-ATOMIC).
- `TooManyPending` with the real cap of 16 is covered by Kani (`h_raw_request`),
  not by the traces.
