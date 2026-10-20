# Lean results (strategy.md section 18)

Lean 4.34.1, core library only. Model at trust-framework `3426c92` through
`tla/ApprovalCore.tla`. Run on 2026-10-13 in a Linux x86_64 cloud container
with `tools/scripts/run-lean.sh near-approval`.

## Proofs

| ID | Theorems | Result |
|---|---|---|
| LEAN-IND | `inv_init`, `inv_add`, `inv_revoke`, `inv_request`, `inv_approve`, `inv_reject`, `inv_next`, `inv_step`, `reach_inv`, `approvable_all` | proved, every size |
| LEAN-STEP | `stepProps_next`, `stepProps_step` | proved, every size |
| LEAN-TR | `reach_run`, `tr1_provenance`, `tr2_decision_final`, `tr3_void_terminal`, `hist1_run`, `hist3_run`, `hist10_run` | proved, runs of any length |
| LEAN-GUARD | `err_eq_firstFail`, `guards_order`, `err_mem_guardOrder`, `err_ne_logFull` | proved |
| LEAN-WIT | `witness_approved`, `witness_rejected`, `witness_void`, `witness_revival`, `witness_cap`, `witness_cap_refused` | proved by evaluation |
| LEAN-LIVE | `approveReq_not_pending`, `enabled_of_pending`, `live1_wf`, `live1`, `live1_sf`, `live1_of_live1Inf`, `unfair_violates`, `fair_witness` (2026-10-19) | proved, every behaviour at every size |
| LEAN-DELTA | `delta_add`, `delta_revoke`, `delta_request`, `delta_approve`, `delta_reject`, `delta_refines` (2026-10-17) | proved, concrete stores of every size |

No invariant needed strengthening: `Inv` exactly as `ApprovalProps.tla`
states it is inductive at every size, which TLA-IND had shown only from
states with at most 3 requests. The step properties follow from the guards
alone; `stepProps_next` does not use `Inv`.

Axiom audit: all 33 theorems in `Audit.lean` (25 before LEAN-LIVE) depend only on `propext`,
`Classical.choice` and `Quot.sound`. Both canaries fail to compile.

Size: 3,478 lines (machine and properties 549, lemmas 315, proofs 2,097,
guard order and witnesses 260, tools 257). Clean build: 14 s.

## Links to the other layers

| Check | Result |
|---|---|
| LEAN-GUARD vs `tla_facts.pl` (C-2t) | equal for all five entry points |
| REF-5L | 2,000 core traces × 120 calls = 240,000 steps, every result and post-store equal (5 s with trace generation) |
| LINK (2026-10-17) | 736,500 footprint views (add 504, revoke 84, request 912, approve 490,000, reject 245,000; 164 Ok): Lean `cstep` = Rust `expect`/`protocol` on every one, and the real core on each view agrees with both. About 2 s to generate, 7 s to check |
| MC-4 | TLC and Lean: 21,670 stores, 6,298,932 rejected calls, 41,706 edges, all equal. TLC about 40 s for both runs, Lean export 0.9 s, `mc3.py` 150 s |

With MC-3 (2026-10-11), the Prolog, TLC and Lean graphs of the MC_Graph
universe are one graph. MC-4 gives the same counts with TLC 1.7.4, the
version now pinned.

## Spec mutants

Since LEAN-DELTA (2026-10-17), every one of the 15 mutants below also breaks
`Delta.lean`: the model is now pinned from the code side as well as by the
invariant and step-property proofs.

The 15 `tla/mutants` ported to `Machine.lean`. Each is killed by a proof
(the files that failed to build):

| Mutant | Broken proofs |
|---|---|
| 01 live-from-dropped | Inv/Add, Inv/Approve, Inv/Reject, StepProps |
| 02 self-approval-dropped | Guard, Inv/Approve |
| 03 pending-not-decremented | Inv/Approve, Inv/Reject, StepProps |
| 04 approve-no-log-append | Inv/Approve, StepProps |
| 05 add-from-zero | Inv/Add, StepProps |
| 06 revoke-keeps-key | Inv/Revoke, StepProps |
| 07 guard-swap-rejected-revoked | Guard, Inv/Approve, Inv/Reject |
| 08 cap-off-by-one | Guard, Inv/Request |
| 09 approval-index-from-requests | Inv/Approve, StepProps |
| 10 reject-self-approval-dropped | Guard, Inv/Reject |
| 11 already-rejected-dropped | Guard, Inv/Approve, Inv/Reject, StepProps |
| 12 rejection-records-agent-rid | Inv/Reject, StepProps |
| 13 revoke-not-recorded | Inv/Revoke, StepProps |
| 14 registration-id-reused | Inv/Add |
| 15 request-rid-zero | Inv/Request, StepProps |

| 16 approve-checks-cap (liveness) | Guard, Inv/Approvable (so LEAN-LIVE), Delta |
| 17 approve-not-deciding (liveness) | Inv/Approve, Liveness, StepProps, Delta |

Every mutant also breaks `Delta.lean`. Of the 15 safety mutants, 13 leave
LEAN-LIVE (`Liveness.lean`, `LivenessWitness.lean`) building; 07 and 11
break only `LivenessWitness.lean`. Mutants 16 and 17 target LEAN-LIVE's two
lemmas. Full run with 17 mutants: under 4 min (2026-10-19).

Mutants 05, 06, 13 and 14 also restate the `rfl` field lemma in
`Lemmas.lean` that spells out the mutated effect, so the kill is an
invariant or step-property proof failing, not that lemma. Full run: 3 min.

## LEAN-LIVE (2026-10-19)

`Liveness.lean` proves TLA-LIVE-1 (`MC_Liveness.tla`'s `Live1` under
`LiveSpec`) for every behaviour `Nat → State`, for every step relation, so
both `Next` and the bounded `BNext`, with no bound on keys, accounts,
requests, registrations or `MaxPending`. `live1_sf` proves TLA-LIVE-1s
(`Live1Inf` under strong fairness). `LivenessWitness.lean`:
`unfair_violates` (an `UnfairSpec` behaviour violating `Live1`, the Lean
twin of `MC_Liveness_Unfair`) and `fair_witness` (a `LiveSpec` behaviour
with a pending request and an eligible approver from instant 3 on).
Strategy.md section 18.7. Build of the two files: about 1.5 s.
