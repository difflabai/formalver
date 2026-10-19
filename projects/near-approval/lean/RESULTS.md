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
| LEAN-DELTA | `delta_add`, `delta_revoke`, `delta_request`, `delta_approve`, `delta_reject`, `delta_refines` (2026-10-17) | proved, concrete stores of every size |
| LEAN-COVER | `Ident.cover` (per entry point `cover_add` … `cover_reject`), `Ident.cls_mem`, `Ident.wfv_of_store` (2026-10-19) | proved, every view of every concrete store, any identity types |
| LEAN-FRAME | `Ident.frame` (2026-10-19) | proved |
| LEAN-REN | `Ident.rename` (2026-10-19) | proved, any renaming injective on the footprint |

No invariant needed strengthening: `Inv` exactly as `ApprovalProps.tla`
states it is inductive at every size, which TLA-IND had shown only from
states with at most 3 requests. The step properties follow from the guards
alone; `stepProps_next` does not use `Inv`.

Axiom audit: all 30 theorems in `Audit.lean` depend only on `propext`,
`Classical.choice` and `Quot.sound`. Both canaries fail to compile.

Size: 3,478 lines (machine and properties 549, lemmas 315, proofs 2,097,
guard order and witnesses 260, tools 257). Clean build: 14 s. `Ident.lean`
(LEAN-COVER, LEAN-FRAME, LEAN-REN, 2026-10-19) adds 825 lines.

## Links to the other layers

| Check | Result |
|---|---|
| LEAN-GUARD vs `tla_facts.pl` (C-2t) | equal for all five entry points |
| REF-5L | 2,000 core traces × 120 calls = 240,000 steps, every result and post-store equal (5 s with trace generation) |
| LINK (2026-10-19) | 14,310 views, one per class of `Ident.allCls` (add 48, revoke 4, request 108, approve 12,540, reject 1,610; 12 Ok): Lean `cstep` = Rust `expect`/`protocol` on every one, the real core on each view agrees with both, and the set of views equals Lean's `allCls.map rep`. With LEAN-COVER and K-LINK-T (strategy §18.6.1) these stand for every view. Under 1 s to generate and check. The earlier hand-built domain (736,500 views, 2026-10-17) is retired |
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

Mutants 05, 06, 13 and 14 also restate the `rfl` field lemma in
`Lemmas.lean` that spells out the mutated effect, so the kill is an
invariant or step-property proof failing, not that lemma. Full run: 3 min.
