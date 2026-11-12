# shared-pool: Lean layer results

Runner: `projects/shared-pool/lean/run.sh [build|audit|canary|replay|mutants]`
(default: all; exit 0 = every check passes). Lean 4.34.1, core library only
(no Mathlib). Pin: shared-pool-controls `a4bb5c3c` (PR #1 head),
`crates/core/src/lib.rs`.

## What is proved (every size, kernel-checked)

`PoolLean/Machine.lean` transcribes the core: each call is its guard list in
the code's order (first firing guard = outcome; errors and no-ops stutter),
then `effect`. Values are `Int`, counters `Nat`, accounts a type parameter
`A` with decidable equality, so every theorem holds for every number of
metrics, recipes, terms, records and accounts, any config `validate`
accepts (`Valid`, CFG-2's checks), any times and any argument values.
Ghosts: `base`/`k0` (values and record count at the last `observe` or `new`)
and `eff` (number of effective transitions).

| ID | Theorem(s) | Statement |
|----|-----------|-----------|
| LEAN-IND | `inv_init`, `inv_step`, `reach_inv` (Inv.lean) | `Valid cfg ⇒ Inv (init cfg now)`; `Inv s ⇒ Inv (step s op)` for EVERY op (no validity premise needed on the step); so every reachable state satisfies `Inv` = INV-WF ∧ INV-LEDGER ∧ INV-HARD ∧ INV-DEP ∧ INV-VER (Props.lean) |
| LEAN-STEP | `stepProps`, `stepProps_step`, `exec_auth`, `term1`, `term1_cancel`, `stale1_no_replay`, `version_mono_run` (StepProps.lean) | every call from EVERY state (no `Inv` premise) satisfies TX-0, TX-NOOP/TX-VER, LIFE-1 (append-only, frame, status graph, fresh = Reserved with id = index), AUTH-1 (every `Ok`, no-ops included), STALE-1 (accepted ⇒ named the current version; and over any later run the same request is never accepted again), ADM-1, ADM-2, HARD-STEP (no call but `observe` raises any PV_i), ASYNC-1; TERM-1 for settle and cancel |
| (extra) | `dep1`, `obs1`, `pause1_blocks`, `pause1_transparent` (Calls.lean) | DEP-1, OBS-1, PAUSE-1 (paused ⇒ submit/dispatch change nothing; ack/cancel/settle/observe give the same result and post-state whatever the flag) |
| LEAN-LIVE1 | `live1`, `live1_exec`, `live1_reach` (Live.lean) | LIVE-1: `Valid cfg`, `Inv s`, B = 0 on every metric, `version < u32::MAX` ⇒ for every Dispatched/Active/Unknown record, `settle(executor, id, true)` passes every guard, returns `Ok` and completes the record |
| INV-HEALTHY | `healthy` (Live.lean) | `Inv s` ∧ B = 0 ⇒ for every subset of the open records, values + their completions lie in [min, max] on every metric |
| LEAN-GUARD | `Guard.guards_order`, `Guard.outcome_mem` (Guard.lean) | the outcome codes of every call's guard list are exactly `guardOrder` (written from lib.rs with line numbers; `pool-lean guards` prints it), and every outcome is one of them. Compared by hand with TLA+'s GuardOrder (`prolog/extracted/tla_facts.pl`): equal once the guards that cannot fire in an `Inv` state are dropped (`InvalidConfig` length checks, release's second `NotFound`, the `energy_terms` `Bounds` checks); that comparison is not mechanised here |
| LEAN-WIT | Witness.lean | see below, all by `decide`/`rfl` in the kernel |
| REF-5L | `pool-lean replay` (Main.lean) | all 206 traces of `conformance/traces/core.txt` (8232 calls, 1995 `Ok`), generated from the real core, replayed on the Lean machine: every result and every post-state (values, version, observed_at, paused, records) equal, initial state included |

### LEAN-WIT (Witness.lean)

F-1, the wedge (trace 0): config m(0,10,5), m(-100,100,5); t(1,0,1,target);
r(a1,x1,[-2,0],[2,-5],1,[]) with o = 0, a1 = 1, x1 = 2.

* `wcfg_valid`: the config passes `validate` (`Valid`).
* `wedge_eq`, `f1_results`, `wedge_reach`, `wedge_inv`: observe [12,5],
  submit (Ok(0)), dispatch, ack(true) reach values [10,5] with record 0
  Active; the state is reachable and satisfies `Inv`.
* `wedge_B`: B_0 = 2 (the baseline is disturbed), `wedge_healthy_now`: the
  current point is inside bounds.
* `f1_settle_true`, `f1_settle_false`: both settles by the executor fail
  `Bounds`; `f1_cancel_owner`/`_actor`: cancel fails `Pending`;
  `f1_observe`: observe fails `Pending`.
* `f1_forever` (strongest form): from the wedge, for EVERY sequence of calls
  (any caller, arguments, times, pauses, new submits), the values stay
  [10,5] and the records stay exactly [record 0 Active]. Corollaries
  `f1_never_terminal`, `f1_observe_forever` (every later observe is an
  error) and `f1_settle_forever` (every later settle of record 0 is an
  error). This is the code finding F-1, proved permanent in the model.
* Non-vacuity of the healthy side: `live1_premises` (a reachable state with
  B = 0, version < u32::MAX and a Dispatched record), `live1_instance`
  (`live1` applied to it), `healthy_settle` (the concrete settle completes
  it), `unknown_settle` (the Unknown branch), `cancelled_reach` (a
  Cancelled record), `stale_instance` (STALE-1 rejects an old version).

## Vacuity guards and hygiene

* Axiom audit (`Audit.lean`): 40/40 headline theorems depend only on
  `propext`, `Classical.choice`, `Quot.sound` (several on fewer).
* Canaries, each must FAIL to compile, and does: `canary/False.lean`
  (`False`), `canary/NotInv.lean` (every state satisfies `Inv`),
  `canary/Live1NoPremise.lean` (LIVE-1 without B = 0, false by F-1).
* Hygiene scan (comments stripped): no `sorry`, `admit`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque` in
  PoolLean/, Main.lean, Audit.lean, canary/. The build prints no
  `declaration uses 'sorry'`.

## Mutants

16 hand-written mutants of Machine.lean (`mutants/*.patch`, applied with
`patch -p1` in a copy of this directory). `run.sh mutants` tries both
`pool-lean replay` and the full `lake build` on each and reports every check
that kills it. All 16 are killed; none survives.

| Mutant | Killed by |
|--------|-----------|
| 01-observe-pending-dropped (observe ignores open records) | replay, build (Facts) |
| 02-envelope-skip-ignored (settle/release envelope counts the record itself) | replay, build (Lemmas) |
| 03-bounds-slack (check_bounds tolerates EV = PV + 1) | replay, build (Lemmas) |
| 04-version-overflow-off-by-one (`checked_add` fails one too late) | build (Facts) only |
| 05-release-adds-reserve (release applies +reserve) | replay, build (Facts) |
| 06-cancel-any-caller (cancel's authority check dropped) | replay, build (Facts) |
| 07-ack-status-swapped (accepted ↦ Unknown) | replay, build (Witness) |
| 08-submit-id-off-by-one (new record id = len + 1) | replay, build (Inv) |
| 09-guard-order-paused-stale (submit: Stale before Paused) | replay, build (Facts, Guard) |
| 10-prereq-ignores-units (prerequisite needs only 1 unit) | build (Inv) only |
| 11-unknown-not-settleable (Unknown not in flight) | replay, build (Witness) |
| 12-adm1-energy-check-dropped (ADM-1 guard dropped) | replay, build (Facts) |
| 13-observe-keeps-k0 (ghost k0 not reset by observe) | build (Inv) only |
| 14-snapshot-age-inclusive (`<` ↦ `≤` in snapshot age) | replay only |
| 15-settle-complete-uses-reserve (settle applies reserve) | replay, build (Facts) |
| 16-dispatch-ignores-pause (dispatch's pause check dropped) | replay, build (Facts) |

"build (F)" names the first module that stops compiling (lake does not
build its dependents). Facts.lean restates each call's passing guard list,
so many semantic mutants first break there; 04, 10 and 13 are caught only
by the proofs (the traces never reach u32::MAX, never need more than one
prerequisite unit, and cannot see a ghost), and 14 only by the traces.

## Run times (darwin arm64, this workspace)

| Check | Time |
|-------|------|
| `lake build` from a clean `.lake` (all 20 jobs) | 7 s |
| `run.sh build` (incremental) + hygiene scan | 1 s |
| `run.sh audit` (40 `#print axioms`) | < 1 s |
| `run.sh canary` (3 files) | 2 s |
| `run.sh replay` (206 traces, 8232 calls) | < 1 s |
| `run.sh mutants` (16 mutants, replay + full build each) | 224 s |
| `run.sh` (everything) | 227 s |

## What is NOT shown here

* Transcription fidelity is not a proof: Machine.lean is a hand
  transcription of lib.rs (ASM-LEAN-TLA analogue). REF-5L checks it against
  206 real-core traces (≤ 40 calls each, small configs plus 5 fixtures) and
  found no disagreement, which is evidence, not proof, of equivalence.
* Numeric representation (stated in Machine.lean's header): the model
  computes exactly in `Int`/`Nat`; that the code's i64/u64/u128 arithmetic
  never overflows on these paths is NUM-1/NUM-2 (Kani's job), not proved
  here. `energy` is the exact Σ w·r²; the code's `energy` Arithmetic error
  is not modelled (claimed unreachable). The envelope's fail-on-first
  partial sum is modelled by the final low/high sums (argued in the header:
  partial lows only fall and highs only rise from a bounded candidate), not
  proved against a step-by-step model.
* Times, units and versions are unbounded `Nat` in the model (the code's
  u64/u32 types bound the inputs); u64 `saturating_add` and the u32 version
  overflow are modelled exactly. `max_age`'s u32 type and all names/strings
  (validate's string checks, CFG-1's string half) are not modelled.
* Panics (ROB-1) are not modelled: the model reads out-of-range indices as
  defaults. `Inv` (INV-WF) shows every index the guards read is in range in
  every reachable state, but "no panic" for the Rust code is not proved
  here.
* RD-PREVIEW and RD-BEST (preview, best_quantity) are not modelled. NUM-1,
  NUM-2, CFG-1 and the shell (SH-*, EX-*, RT-*) are other layers' work.
* LIVE-2 (eventual termination under fairness) is a temporal property and
  is not stated in Lean; LIVE-1 is the per-state enabling half, and F-1
  (`f1_forever`) is the counterexample when B ≠ 0.
* TX-SUBMIT..TX-OBSERVE (exact results and post-states) are the model's
  definitions plus REF-5L, not separate theorems.

## Findings

* F-1 (wedge), confirmed in the Lean model and shown PERMANENT for every
  continuation (`Witness.f1_forever`): after observe [12,5] and a recovery
  hedge, record 0 can never become terminal and every observe fails.
  Reproducer: trace 0 of `conformance/traces/core.txt` (replayed by
  `run.sh replay`); the theorem is checked by `run.sh build` and audited by
  `run.sh audit` (`Pool.Witness.f1_forever`, PoolLean/Witness.lean).
* No other disagreement: the model agrees with the real core on all 206
  traces, and every property above holds at every size.
