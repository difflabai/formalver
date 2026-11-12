# shared-pool: TLA+ layer results

Pin: difflabai/shared-pool-controls `a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`
(PR #1 head). Model: `crates/core/src/lib.rs` transcribed guard by guard
(brief, "Exact core semantics"). Tools: TLC 2.19 / tla2tools 1.7.4 (rev
5a47802), OpenJDK 23.0.2, 4 workers, macOS arm64. Conformance traces:
`conformance/traces/core.txt`, sha256 `1ed10694...718b13` (206 traces, 8,232
calls). Run: `projects/shared-pool/tla/run.sh [safety|liveness|apalache|trace|mutants]`
(default: safety liveness trace). Run date 2026-11-11; the full run
`run.sh safety liveness trace apalache mutants` exits 0 in 721 s.

## Model

| File | Contents |
|---|---|
| `SharedPool.tla` | The Pool as variables (`cfg`, `values`, `version`, `observedAt`, `paused`, `records`; config is a variable no action writes, so one TLC run replays traces of 206 configs). Ghost: `base`, `k0` (values and record count at the last observe), `steps` (effective transitions), `last` (the last effective call, read only by step properties). One error operator per entry point (`SubmitErr`, `DispatchErr`, `AckErr`, `CancelErr`, `SettleErr`, `PauseErr`, `ObserveErr`, with `ReleaseErr` and `CheckBounds` shared as in the code) giving the first failing guard in code order, `"Noop"` for the core's idempotent `Ok(())`, or `"Ok"`; one action enabled exactly when it is `"Ok"`. Rejected and idempotent calls stutter (TX-0, TX-NOOP). `GuardOrder` lists each entry point's exits in order. `ValidCfg` transcribes `Config::validate`. |
| `Props.tla` | Invariants INV-WF, INV-LEDGER, INV-HARD, INV-HEALTHY, INV-DEP, INV-VER, TERM-1 (error view), LIVE-1; step properties (`StepProperty`) INV-WF config, TX-VER, LIFE-1, STALE-1, AUTH-1, ADM-1, ADM-2, HARD-STEP, DEP-1, ASYNC-1, OBS-1, TX-SUBMIT and TX-DISPATCH (time, capacity and unit guards, effect), PAUSE-1; witnesses. Each tagged `PROP: <ID>`. |
| `MCCommon.tla` | The small universe: metrics m0 ∈ [0,2] (init 1), m1 ∈ [-2,2] (init 1); term t(1, target 0, weight 1); recipes r0 "hedge" (a1/x1, reserve [-1,0], complete [1,-1], max 1) and r1 (a1/x1, reserve [1,-1], complete [-1,0], max 2, requires r0 × 1); max_age 1; accounts o, a1, x1, z. This is the brief's F-1 wedge scaled down. |
| `MC_Safety.{tla,cfg}` | TLA-SAFE and TLA-WIT: times {0,1,2} per call, expiry offsets {0,1,2,86400,86401}, observations {-1,0,2,3} × {-2,0,2} plus a short vector and one beyond MAX_VALUE, MaxRecords = 3. `VIEW` drops `version`, `steps`, `last` (keeps `version - steps`): a bisimulation quotient, argued in the module header. |
| `MC_Liveness.tla` + `MC_Liveness{,_Unfair,_F1,_F1Shape}.cfg` | LIVE-2. Bounds in the actions (submit/pause/observe while version < 4, MaxRecords = 2), no VIEW or CONSTRAINT. |
| `TraceCheck.{tla,cfg}`, `trace2tla.py` | REF-5: `trace2tla.py` (python3 -I, no deps) writes `build/TraceData.tla`; TLC replays all 206 traces in one run and also checks `Inv` and `StepProperty` on every core state and step. |
| `mutants/*.patch` | 22 spec mutants. |
| `run.sh` | The runner (TLC workers 4). |

**Scaled constants (C-5).** `MaxRecords` (MAX_RECORDS = 256) is 3 in
MC_Safety and 2 in MC_Liveness, 256 in TraceCheck. `MaxVersion` (u32::MAX)
is 2^31 - 1 everywhere because TLC integers are 32-bit; no run gets near it.
`MAX_VALUE`, `MAX_UNITS`, `MAX_WEIGHT`, the 86,400 s window and the other
limits are the real values.

**Abstractions.** Names and units of metrics and recipes are not modelled
(the core only checks their lengths). Numbers are exact integers; the core's
i64/u64 arithmetic cannot wrap on these paths for valid configs (NUM-1/2), so
`Arithmetic` is exactly "a result leaves ±MAX_VALUE" or the version bump.
Block time is an argument of each call, chosen freely (a superset of
monotone time, ASM-TIME). In the traces, 7 submit calls carry request
version u32::MAX; `trace2tla.py` maps request versions ≥ 2^31 to -1 (the
model compares them only with `version`, which never exceeds 18 in the
traces, so the outcome `Stale` is unchanged).

## Results

| Check | ID | Result | Size / time |
|---|---|---|---|
| `MC_Safety`: `InvMC` (INV-WF, INV-LEDGER, INV-HARD, INV-HEALTHY, INV-DEP, INV-VER, TERM-1, LIVE-1) and `StepProperty` | TLA-SAFE | no error | 2,306,738 distinct states (56.5M generated), depth 15, about 10 min (598 s and 623 s in two runs) |
| `Witness_Completed`, `_Prerequisite`, `_Disturbed`, `_Wedge` (state) | TLA-WIT | each violated, as required | traces of 4, 6, 2, 4 states; seconds |
| `WitStep_CancelledAfterDispatch`, `_UnknownToActive`, `_Recovery`, `_PausedSettle/Ack/Cancel/Observe` (step) | TLA-WIT | each violated, as required | seconds |
| `MC_Liveness`: LIVE-2 under WF of completion, observes in bounds (with `InvMC`) | TLA-LIVE-1 | no error | 17,964 distinct states, 8–13 s |
| `MC_Liveness_Unfair`: LIVE-2 without fairness | TLA-LIVE-1 non-vacuity | violated, as required | seconds |
| `MC_Liveness_F1`: LIVE-2 with a disturbing observe, WF of both settle outcomes | TLA-LIVE-F1 | violated, as required (F-1) | seconds |
| `MC_Liveness_F1Shape`: `Live2F1`, every record that stays in flight is eventually forever `Wedged` | TLA-LIVE-F1 | no error | 18,284 distinct states, 4–8 s |
| `TraceCheck`: 206 traces, 8,232 calls, every result and post-state equal; `Inv` and `StepProperty` on every core state | REF-5 | every trace accepted | 8,438 of 8,438 states (206 initial + 8,232 steps), 4 s |
| Inductive invariant (Apalache) | TLA-IND | not done | gap, below |
| Spec mutants (`mutants/*.patch`) | | 22 of 22 killed | 20 by trace, 2 by safety; 105 s with liveness |

The traces cover every result kind the generator requires (36 `op:result`
pairs, from `submit:prerequisite` to `observe:bounds`), so every error
operator is exercised against the real core; `GuardOrder`'s order is the
operators' order.

## F-1 (finding, confirmed by TLC)

In a disturbed state (an observe put m0 above its max), the recovery rule
admits a hedge whose completion moves m0 back out. Once its reservation has
brought m0 inside, neither settle can resolve it: `settle(true)` and
`settle(false)` both fail `Bounds` (the envelope after the step violates m0
while the current values do not), `cancel` fails `Pending`, and `observe`
fails `Pending` forever.

- `Witness_Wedge` (MC_Safety) reaches it at depth 4: observe `[3, 2]`
  (m0 = 3 > 2); submit r0 × 1 by a1 (values `[2, 2]`, Ok: energy 4 → 4,
  completion `[3, 1]` has energy 1 < 4, envelope violation 1 ≤ 1); dispatch.
- `MC_Liveness_F1` violates LIVE-2. The counterexample of the recorded run:
  pause(true), observe `[3, 2]` (while paused, PAUSE-1), pause(false), submit
  r0 × 1, dispatch, ack(true), then stuttering forever with record 0
  `Active`, although the executor is weakly fair to settling it either way.
  (TLC may print another path to the same wedge; the runner checks that the
  counterexample observed `[3, 2]` and ends stuttering.)
- `MC_Liveness_F1Shape` shows that at these bounds every LIVE-2
  counterexample is this wedge: both settles `Bounds`, cancel by owner or
  actor `Pending`, observe `Pending`, and B ≠ 0. With observes in bounds
  (B = 0) LIVE-2 holds (TLA-LIVE-1) and LIVE-1 holds in every state.
- Trace 0 of the conformance traces is the brief's unscaled reproducer on
  the real core (observe `[12, 5]`, submit, dispatch, ack, settle(true) →
  `bounds`, settle(false) → `bounds`, cancel → `pending`, observe →
  `pending`); TraceCheck replays it with equal results and states.

## Spec mutants

All 22 killed. The runner tries trace, then safety, then liveness (healthy
and F1Shape) and reports the first check that fails.

| Mutant | Killed by |
|---|---|
| 01 submit: `Stale` before `Paused` | trace |
| 02 submit: prerequisite guard dropped | trace |
| 03 cancel: owner no longer authorized | trace |
| 04 envelope ignores open records | trace |
| 05 envelope does not skip the settled / released record | trace |
| 06 recovery (ADM-2) energy check dropped | trace |
| 07 ack: repeated negative ack bumps the version | trace |
| 08 release keeps the reservation in `values` | trace (INV-LEDGER, post-state) |
| 09 observe allowed with open records | trace |
| 10 dispatch: expiry `now > exp` instead of `now >= exp` | safety (TX-DISPATCH; the traces never dispatch at `now = exp`) |
| 11 settle: any terminal record is a no-op (no `InvalidState`) | trace |
| 12 set_paused does not bump the version | trace |
| 13 `Full` off by one | safety (INV-WF: #records ≤ MaxRecords; the traces never fill 256) |
| 14 snapshot age inclusive (`>=`) | trace |
| 15 energy tolerance +1 | trace |
| 16 settle authorized for the actor instead of the executor | trace |
| 17 late positive ack (Unknown → Active) ignored | trace |
| 18 envelope checks only the upper bound | trace |
| 19 observe keeps the old ghost base | trace (INV-LEDGER on core states) |
| 20 settle rejects Unknown records | trace |
| 21 dispatch: snapshot freshness dropped | trace |
| 22 submit: no upper bound on `expires_at` | trace |

No mutant needed the liveness checks: the trace replay compares every
result and post-state of 8,232 core calls, which is the strongest check
here. Mutants 10 and 13 change behaviour only where the traces never go.

## Not covered

- **TLA-IND (gap).** No Apalache inductive check (`run.sh apalache` prints
  `skip`). The model sums over the records with `RECURSIVE` operators
  (envelope, ledger, energy, prerequisite units), which Apalache 0.47.2
  rejects ("Apalache does not support recursive operators"), and ranges over
  symbolic bounds (`1 .. NR`, `0 .. NR - 1`); an Apalache version needs
  `ApaFoldSeqLeft`/`MkSeq` sums, `DOMAIN`-based ranges and type annotations
  throughout, i.e. a rewrite of the model, which was not done. Safety is shown only within the MC bounds plus on the 8,438 core
  states of the traces; the every-size counterpart is the Lean layer's.
- **Version overflow.** The bump guard (`version = u32::MAX → Arithmetic`) is
  transcribed but never reached: no trace and no MC run gets near
  `MaxVersion`, and no mutant can be killed there. LIVE-1/LIVE-2 assume
  version < u32::MAX.
- **`Full`.** Reachable in MC_Safety (MaxRecords = 3, mutant 13 is killed by
  it), never in the traces (256 records).
- **Trace coverage of time boundaries.** The conformance traces never contain
  a dispatch at `now = expires_at` or a submit with `expires_at = now +
  86400`. MC_Safety covers both (TX-DISPATCH, TX-SUBMIT); a mutant that
  rejects the latter (stricter) would survive every check here, since no
  safety property forbids rejecting.
- **Scale.** 2 metrics, 1 term (target shape only), 2 recipes, ≤ 3 records,
  4 accounts, 3 block times; other shapes, larger configs and the real
  record limit are covered only by the traces (configs of up to 8 metrics, 6
  recipes, 46 calls). Accounts are distinct roles, no symmetry reduction.
- **Not modelled.** `preview` and `best_quantity` (RD-PREVIEW, RD-BEST), the
  NEAR shell, the executor and promise interleavings beyond "ack and settle
  are independent steps" (ASM-INTERLEAVE).
- **Refinement to the code.** The link from this model to the Rust is only
  REF-5 (traces); per-step Kani refinement (REF-1..3) is not done yet.
