# shared-pool: TLA+ layer results

Pin: difflabai/shared-pool-controls `a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`
(PR #1 head). Model: `crates/core/src/lib.rs` transcribed guard by guard
(brief, "Exact core semantics"). Tools: TLC 2.19 / tla2tools 1.7.4 (rev
5a47802), OpenJDK 23.0.2, 4 workers, macOS arm64. Conformance traces:
`conformance/traces/core.txt`, sha256 `05c0deb4...377818`: 212 traces,
8,804 calls. Traces 0-205 are the wedge, the 5 fixtures and 200 random
configs; trace 206 is `arith`, 207 `full`, 208 `release-arith` (F-2b, the
reproducer below), 209 `f2-risk` (F-2's `Bounds` form in the `risk`
fixture), 210 `f4-self` (F-4) and 211 `f6-stale` (F-6). Traces 0-208 are
byte-identical to the previous 209-trace set (sha256 `988d9a6f...1250dd`).
Run: `projects/shared-pool/tla/run.sh [safety|liveness|apalache|trace|mutants]`
(default: safety liveness trace). Run date 2026-11-11 (final runs ending
2026-11-12). Wall times of the final runs: `run.sh` (default) 573 s
(safety 522 s), `run.sh mutants` 150 s, both on the 209-trace set. The
trace check was rerun on 2026-11-12 on the 212 traces: 8 s. On the 212
traces, GitHub Actions run 43194245726 (PR #31, 2026-11-12, ubuntu-latest, `TLA_HEAP=5g`) ran
`safety liveness trace` in 23 min 7 s (safety 1,300 s, 2,306,738 distinct
states; trace 12 s) and `mutants` in 4 min 10 s: 31 of 31 killed, every
kill reason as listed below.

## Model

| File | Contents |
|---|---|
| `SharedPool.tla` | The Pool as variables (`cfg`, `values`, `version`, `observedAt`, `paused`, `records`; config is a variable no action writes, so one TLC run replays all 212 traces, of 211 distinct configs: trace 209 reuses trace 5's `risk` config). Ghost: `base`, `k0` (values and record count at the last observe), `steps` (effective transitions), `last` (the last effective call, read only by step properties). One error operator per entry point (`SubmitErr`, `DispatchErr`, `AckErr`, `CancelErr`, `SettleErr`, `PauseErr`, `ObserveErr`, with `ReleaseErr` and `CheckBounds` shared as in the code) giving the first failing guard in code order, `"Noop"` for the core's idempotent `Ok(())`, or `"Ok"`; one action enabled exactly when it is `"Ok"`. Rejected and idempotent calls stutter (TX-0, TX-NOOP). `GuardOrder` lists each entry point's exits in order. `ValidCfg` transcribes `Config::validate`. |
| `Props.tla` | Invariants INV-WF, INV-LEDGER, INV-HARD, INV-HEALTHY, INV-DEP, INV-VER, TERM-1 (error view), LIVE-1; step properties (`StepProperty`) INV-WF config, TX-VER, LIFE-1, STALE-1, AUTH-1, ADM-1, ADM-2, HARD-STEP, DEP-1, ASYNC-1, OBS-1, TX-SUBMIT and TX-DISPATCH (time, capacity and unit guards, effect), PAUSE-1; witnesses (TLA-WIT). |
| `MCCommon.tla` | Two small universes. `MCConfig`: metrics m0 ∈ [0,2] (init 1), m1 ∈ [-2,2] (init 1); term t(1, target 0, weight 1); recipes r0 "hedge" (a1/x1, reserve [-1,0], complete [1,-1], max 1) and r1 (a1/x1, reserve [1,-1], complete [-1,0], max 2, requires r0 × 1); max_age 1: the brief's F-1 wedge scaled down. `CreditHedgeConfig`: metric m0 "selloff loss" ∈ [0,2] (init 1); term t(0, target 2, excess); r0 "credit" (reserve [1], complete [0]) and r1 "hedge" (reserve [0], complete [-2]), both a1/x1, max 1; max_age 0: the `risk` fixture's credit position and selloff hedge (F-2) scaled down. Accounts o, a1, x1, z. Observation sets per check. |
| `MC_Safety.{tla,cfg}` | TLA-SAFE and TLA-WIT on `MCConfig`: times {0,1,2} per call, expiry offsets {0,1,2,86400,86401}, observations {-1,0,2,3} × {-2,0,2} plus a short vector and one beyond MAX_VALUE, MaxRecords = 3. `VIEW` drops `version`, `steps`, `last` (keeps `version - steps`): a bisimulation quotient, argued in the module header. |
| `MC_Liveness.tla` + 7 cfgs | LIVE-2 under named fairness assumptions (next section). Universe chosen per cfg (`LCfg`). Bounds in the actions (submit/pause/observe while version < 4, MaxRecords = 2), no VIEW or CONSTRAINT. |
| `TraceCheck.{tla,cfg}`, `trace2tla.py` | REF-5: `trace2tla.py` (python3 -I, no deps) writes `build/TraceData.tla`; TLC replays all 212 traces in one run and also checks `Inv` and `StepProperty` on every core state and step. |
| `mutants/*.patch` | 31 spec mutants (a patch may name the checks that must kill it in a `# checks:` header). |
| `run.sh` | The runner (TLC workers 4). |

**Scaled constants (C-5).** `MaxRecords` (MAX_RECORDS = 256) is 3 in
MC_Safety and 2 in MC_Liveness, 256 in TraceCheck (trace 207 fills all 256).
`MaxVersion` (u32::MAX) is 2^31 - 1 everywhere. `MAX_VALUE`, `MAX_UNITS`,
`MAX_WEIGHT`, the 86,400 s window and the other limits are the real values.

**TLC integer range (ASM-MODEL).** TLC integers are 32-bit signed; TLC
stops with `Overflow when computing ...` instead of wrapping (checked), so
an out-of-range computation fails a run, it cannot pass one silently. Three
consequences: (1) `MaxVersion` is 2^31 - 1, not u32::MAX, and no run gets
near it, so the version-overflow exits are not exercised. (2) Request
versions ≥ 2^31 in the traces (7 submits carry u32::MAX) are mapped to -1 by
`trace2tla.py`; the model reads a request version only through
`v = version`, and every state version in the traces is ≤ 513, so the
outcome (`Stale`) is unchanged. (3) `Energy` computes `w·r²` exactly only
while it stays below 2^31. The core computes energy in u64
(`energy_terms`, lib.rs 151; `energy`, lib.rs 171): it first rejects
values outside ±MAX_VALUE with `Bounds`, takes the residual
`r = values[m] − target` in i64 (both bounded, so |r| ≤ 2·10^6) and
converts it to u64 by shape, then forms each term `r·r·w` with
`checked_mul` and the sum with `checked_add` (`try_fold`); any overflow
returns `Err(Arithmetic)`, nothing wraps. With w up to 1,000 a term
reaches 4·10^15 and 64 terms 2.56·10^17, below u64::MAX (about
1.8·10^19), so by this arithmetic that `Arithmetic` exit does not fire
for a valid config (an argument, not a proof: NUM-1), but the values are
far beyond what TLC can represent. The traces stay
inside the range: trace 206 reaches values of 10^6 but keeps the energy
residual at most 10 (excess term with target 999,990). Energy at large
residuals (NUM-1) is Kani's job (Lean computes exactly in Int and does not
model overflow), not shown here.

**Abstractions.** Names and units of metrics and recipes are not modelled
(the core only checks their lengths). Numbers are exact integers within the
range above; the core's i64/u64 arithmetic cannot wrap on these paths for
valid configs (NUM-1/2), so `Arithmetic` is exactly "a result leaves
±MAX_VALUE" or the version bump. Block time is an argument of each call,
chosen freely (a superset of monotone time, ASM-TIME). `SumTo` is a
recursive function rather than a `RECURSIVE` operator: TLC re-evaluated the
operator's lazy function argument at every level, which cost 0.3 s a step
at 256 records (trace replay 50 s; now 6-7 s), with the same values.

## Results

| Check | ID | Result | Size / time |
|---|---|---|---|
| `MC_Safety`: `InvMC` (INV-WF, INV-LEDGER, INV-HARD, INV-HEALTHY, INV-DEP, INV-VER, TERM-1, LIVE-1) and `StepProperty` | TLA-SAFE | no error | 2,306,738 distinct states, depth 15, 522 s (56.5M generated; 598 s and 623 s before the `SumTo` change) |
| `Witness_Completed`, `_Prerequisite`, `_Disturbed`, `_Wedge` (state) | TLA-WIT | each violated, as required | traces of 4, 6, 2, 4 states; seconds |
| `WitStep_CancelledAfterDispatch`, `_UnknownToActive`, `_Recovery`, `_PausedSettle/Ack/Cancel/Observe` (step) | TLA-WIT | each violated, as required | seconds |
| `liveness` (MC_Liveness.cfg): LIVE-2, completion path, `MCConfig`, observes in bounds (with `InvMC`) | TLA-LIVE-1 | no error | 17,964 distinct states, 7 s |
| `liveness-f2-done` (MC_Liveness_F2Done.cfg): LIVE-2, completion path, `CreditHedgeConfig` (with `InvMC`) | TLA-LIVE-1 | no error | 17,553 distinct states, 5 s |
| `liveness-unfair` (MC_Liveness_Unfair.cfg): LIVE-2 without fairness | TLA-LIVE-1 non-vacuity | violated, as required | 2 s |
| `liveness-f1` (MC_Liveness_F1.cfg): disturbing observe, WF of both settle outcomes | TLA-LIVE-F1 | violated, as required (F-1) | 4 s |
| `liveness-f1-shape` (MC_Liveness_F1Shape.cfg): `Live2F1`, every record that stays in flight is eventually forever `Wedged` | TLA-LIVE-F1 | no error | 18,284 distinct states, 5 s |
| `liveness-f2` (MC_Liveness_F2.cfg): observes in bounds only, WF of settle(false) and of cancel | TLA-LIVE-F2 | violated, as required (F-2) | 4 s |
| `liveness-f2-shape` (MC_Liveness_F2Shape.cfg): `Live2F2`, every record that stays in flight is eventually forever `WedgedRelease` | TLA-LIVE-F2 | no error | 17,553 distinct states, 3 s |
| `TraceCheck`: 212 traces, 8,804 calls, every result and post-state equal; `Inv` and `StepProperty` on every core state | REF-5 (also TX-0, TX-NOOP, CFG-1 partial) | every trace accepted | 9,016 of 9,016 states (212 initial + 8,804 steps), 8 s |
| Inductive invariant (Apalache) | TLA-IND | not done | open item, below |
| Spec mutants (`mutants/*.patch`) | | 31 of 31 killed | 28 by trace, 2 by liveness, 1 by liveness-f2; 150 s |

## LIVE-2: what each liveness check shows

LIVE-2 ("every dispatched record eventually terminal under executor
fairness") depends on what the executor is assumed to do, so each check
names its fairness assumption.

- **TLA-LIVE-1 is the completion path.** With observes inside the bounds
  (B = 0) and the executor weakly fair to *completing* each record
  (`WF(SettleDone(i))`), LIVE-2 holds, in both universes. This is close to
  its own premise: LIVE-1 (an invariant, checked in every reachable state)
  says `settle(executor, id, true)` is Ok for every in-flight record while
  B = 0 and version < u32::MAX, and weak fairness of an action that stays
  enabled makes it happen. What the check adds is that LIVE-1 holds in every
  reachable state of these universes and that nothing else keeps a record
  open. It says nothing about an executor that reports nonexecution;
  `MC_Liveness_Unfair` (no fairness) must and does fail.
- **TLA-LIVE-F1** (finding F-1): with one disturbing observe, LIVE-2 fails
  even if the executor is weakly fair to settling either way; `Live2F1`
  shows every counterexample is the F-1 wedge.
- **TLA-LIVE-F2** (finding F-2): with *no* disturbing observe, an executor
  weakly fair to the honest nonexecution report (`settle(false)`, ASM-EXEC)
  and callers weakly fair to cancelling Reserved records, LIVE-2 fails;
  `Live2F2` shows every counterexample is the F-2 wedge. Weak fairness of
  settling *either* way (`SettleAny`) would hide F-2: in the wedge
  `settle(true)` stays Ok (LIVE-1), so fairness forces it, i.e. the executor
  escapes only by attesting a completion that did not happen (mutant 31
  confirms the required violation then disappears). The same assumption on
  `MCConfig` gives no violation at these bounds: F-2 needs a second open
  record whose completion relies on the first's reservation, which `MCConfig`
  with 2 records cannot build; hence the dedicated universe.

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
- `MC_Liveness_F1` violates LIVE-2 (the runner checks the counterexample
  observed `[3, 2]` and ends stuttering); `MC_Liveness_F1Shape` shows that at
  these bounds every LIVE-2 counterexample is this wedge: both settles
  `Bounds`, cancel by owner or actor `Pending`, observe `Pending`, B ≠ 0.
- Trace 0 is the brief's unscaled reproducer on the real core; TraceCheck
  replays it with equal results and states.

## F-2 (finding, confirmed by TLC)

No observe is needed. In `CreditHedgeConfig` (m0 = 1): submit credit × 1
(m0 = 2); submit hedge × 1 (admitted only because of the credit's
reservation: envelope low 2 - 2 = 0, while from m0 = 1 it would be -1 and
`Bounds`); dispatch both; the executor settles the hedge completed (m0 = 0).
The credit's job did not run, and the executor's honest `settle(false)`
fails `Bounds` (releasing the reservation gives m0 = -1 < 0 while the current
violation is 0), `cancel` fails `Pending`, `observe` fails `Pending`; only
`settle(true)`, a false attestation, is Ok.

- `MC_Liveness_F2` violates LIVE-2. TLC's path differs between runs (4
  workers); two recorded ones: (a) submit credit, dispatch it, submit hedge,
  dispatch it, settle hedge completed, stutter; (b, final run) observe `[2]`,
  observe `[1]`, submit credit, submit hedge, dispatch hedge, settle hedge
  completed (m0 = 0), dispatch credit, stutter. Both end with the credit
  `Dispatched`, the hedge `Completed`, base in bounds. The runner checks
  that end state, not the path: the credit (recipe 0) in flight, the hedge
  (recipe 1) `Completed`, base in [0, 2], stuttering.
- `MC_Liveness_F2Shape` shows every counterexample is this wedge:
  `WedgedRelease(i)` = in flight, `settle(false)` = `Bounds`, `settle(true)`
  = `Ok`, cancel by owner and actor `Pending`, observe `Pending`, B = 0,
  undoing the record's own reservation takes a metric out of [min, max], and
  a sibling record is `Completed`.
- Trace 209 (`f2-risk`) is the unscaled reproducer on the real core, in
  the supplied `risk` config (that of trace 5) with no observe: position
  × 1 (selloff loss 60 → 80), hedge × 8 (admitted with the position
  counted), both dispatched and Active; the hedge settles completed
  (selloff loss 0); then the executor's `settle(false)` for the position
  is `Bounds`, cancel by owner and actor `Pending`, observe `Pending`;
  `settle(true)` is Ok and the next observe Ok. TraceCheck replays it
  with equal results and states.
- Not covered here: the same release path also blocks `cancel` of a
  Reserved (never dispatched) credit after the hedge completed; LIVE-2 is
  about dispatched records only.

**Release `Arithmetic` is reachable (the same mechanism; conformance trace 208).**
A release undoes a reservation, which INV-HARD's envelope does not bound, so
`values - reserve·units` can leave ±MAX_VALUE after a sibling's completion
relied on that reservation. Reproduced on the pinned core (scratch crate,
path dependency on `crates/core`): metrics m0 ∈ [-10^6, 10^6], m1 ∈
[-10, 10]; term on m1; recipes A (reserve [-10^6, 0], complete 0, max 1) and
B (reserve 0, complete [15000, 0], max 100); submit A × 1 (m0 = -10^6),
submit B × 100 (envelope high 5·10^5), dispatch B, settle B completed
(m0 = 5·10^5); then `cancel(A)` → `Arithmetic`, dispatch A, `settle(A,
false)` → `Arithmetic`, observe → `Pending`, `settle(A, true)` → Ok. Replayed
through this model's TraceCheck with equal results and states. It is F-2
with `Arithmetic` in place of `Bounds`. Added to the conformance generator
as trace 208 (`release-arith`): cancel by actor and owner and the honest
`settle(false)` fail `Arithmetic` on the real core, observe is `Pending`,
only `settle(true)` resolves the record; TLC, Lean, Prolog and the shell
replay it with equal results and states.

## Error coverage of the traces (exact counts)

Counts of `op:result` over all 8,804 calls of `core.txt` (`noop` = the
core's `Ok` with the recorded state unchanged, the model's `"Noop"`):

| op | results |
|---|---|
| submit | ok 588, bounds 823, paused 377, unauthorized 218, prerequisite 149, stale 142, expired 117, energy 110, invalid_recipe 99, invalid_units 87, snapshot_expired 60, arithmetic 2, full 2 |
| dispatch | not_found 896, invalid_state 231, ok 151, paused 74, unauthorized 65, expired 44, snapshot_expired 5 |
| ack | not_found 572, noop 338, ok 72 |
| cancel | not_found 346, ok 338, pending 83, noop 48, unauthorized 43, bounds 3, arithmetic 2 |
| settle | not_found 994, invalid_state 373, ok 115, noop 108, unauthorized 75, bounds 3, arithmetic 1 |
| pause | ok 398, unauthorized 51 |
| observe | ok 391, pending 135, bounds 24, unauthorized 51 |

Trace 206 (`arith`, 11 calls): submit `arithmetic` 2 (add at 999,990 + 15;
envelope high 1,000,005), `energy` 1 (exactly 10^6), ok 3 (one with
`expires_at = now + 86400`), `expired` 1 (`now + 86401`); dispatch ok 1 (at
`expires_at - 1`) and `expired` 1 (at `expires_at`); cancel ok 1; observe
`pending` 1. Trace 207 (`full`, 515 calls): submit ok 256, cancel ok 256,
submit `full` 2 (another actor, also after an observe), observe ok 1.
Trace 208 (`release-arith`, 13 calls): cancel `arithmetic` 2 (actor and
owner), settle `arithmetic` 1 (the honest `settle(false)`), observe
`pending` 1, then `settle(true)` ok and observe ok. Trace 209 (`f2-risk`,
13 calls): submit ok 2, dispatch ok 2, ack ok 2, settle ok 2 (the hedge
completed; later the position's `settle(true)`), settle `bounds` 1 (the
position's honest `settle(false)`), cancel `pending` 2 (owner and actor),
observe `pending` 1, then observe ok 1. Trace 210 (`f4-self`, 8 calls):
recipe 0 has actor = executor = a1 and recipe 1 actor = executor = owner
o; each submits, dispatches, is acknowledged and settles its own record
ok (submit, dispatch, ack and settle ok 2 each). Trace 211 (`f6-stale`, 12
calls, max_age 50, observed at 100, record 0 in flight): at 151 submit and
dispatch `snapshot_expired` 1 each and observe `pending`; cancel ok;
observe `pending` again while record 0 is open; record 0 settles ok; then
observe ok and submit ok (submit ok 3, dispatch ok 1, ack ok 1, cancel ok
1, settle ok 1, observe `pending` 2 and ok 1 in all).

The traces compare result kinds, so two exits with the same kind in one
entry point (submit's two `Energy`, the several `Arithmetic`) are not told
apart. Exits of `GuardOrder` no trace reaches:

- Version overflow (`Arithmetic` from the bump, every entry point): no run
  gets near u32::MAX (max state version 513). Reachable in the code (F-5),
  not here.
- Submit's recovery add (`next + complete`): unreachable from a state the
  submit got that far in, since `next + complete·u` lies inside the envelope
  `check_bounds` has just accepted.
- `settle(true)`'s add and envelope `Arithmetic`: unreachable from INV
  states: `values + complete·u` lies in the envelope that INV-HARD keeps
  computable, and the envelope after the step, skipping the record, lies
  inside the one before.
- Release's (`cancel`, `settle(false)`) add `Arithmetic`: **reachable** (the
  reproducer above), in trace 208. Release's envelope `Arithmetic` is
  not covered either way.
- dispatch/ack/pause/observe have no `Arithmetic` other than the bump.

## Spec mutants

All 31 killed. Without a `# checks:` header the runner tries trace, safety,
liveness, liveness-f1-shape, liveness-f2-shape in order; the report names
the first check that fails and why.

| Mutant | Killed by |
|---|---|
| 01 submit: `Stale` before `Paused` | trace |
| 02 submit: prerequisite guard dropped | trace |
| 03 cancel: owner no longer authorized | trace |
| 04 envelope ignores open records | trace |
| 05 envelope does not skip the settled / released record | trace (`Inv`) |
| 06 recovery (ADM-2) energy check dropped | trace |
| 07 ack: repeated negative ack bumps the version | trace |
| 08 release keeps the reservation in `values` | trace |
| 09 observe allowed with open records | trace |
| 10 dispatch: expiry `now > exp` instead of `now >= exp` | trace 206 call 9 (dispatch at `expires_at`); also safety (TX-DISPATCH) |
| 11 settle: any terminal record is a no-op (no `InvalidState`) | trace (`Inv`) |
| 12 set_paused does not bump the version | trace |
| 13 `Full` off by one (`NR > MaxRecords`) | trace 207 (the 257th submit); also safety (INV-WF) |
| 14 snapshot age inclusive (`>=`) | trace |
| 15 energy tolerance +1 | trace |
| 16 settle authorized for the actor instead of the executor | trace (`Inv`) |
| 17 late positive ack (Unknown → Active) ignored | trace |
| 18 envelope checks only the upper bound | trace |
| 19 observe keeps the old ghost base | trace (`Inv`, INV-LEDGER) |
| 20 settle rejects Unknown records | trace (`StepProperty`) |
| 21 dispatch: snapshot freshness dropped | trace |
| 22 submit: no upper bound on `expires_at` | trace |
| 23 `add` rejects ±MAX_VALUE itself (strict bound) | trace 206 call 2 (submit to exactly 10^6 must be `Energy`) |
| 24 envelope overflow check dropped (`CheckBounds` without its `Arithmetic` exit) | trace 206 call 3 (envelope high 1,000,005 must be `Arithmetic`, not `Bounds`) |
| 25 `Full` one early (`NR + 1 >= MaxRecords`) | trace 207 (the 256th submit) |
| 26 submit horizon exclusive (`exp >= now + 86400` expired) | trace 206 call 4 (`now + 86400` accepted) |
| 27 submit horizon one past (only `exp > now + 86401` expired) | trace (206 call 5, `now + 86401` expired; also trace 10); also safety (TX-SUBMIT) |
| 28 dispatch expiry one early (`now + 1 >= exp`) | trace (206 call 7, dispatch at `expires_at - 1` Ok; also trace 128) |
| 29 `MC_Liveness.cfg` observes every vector (premise of TLA-LIVE-1 weakened) | liveness (temporal: F-1 becomes reachable) |
| 30 `settle(true)` returns Ok but writes nothing (record stays in flight) | liveness (temporal; invariants hold); also trace |
| 31 `MC_Liveness_F2.cfg` with weak fairness of settling either way | liveness-f2 (the required violation disappears) |

Which traces kill what (checked by replaying subsets of `core.txt`):
mutants 10, 13, 23, 24, 25 and 26 survive a replay of traces 0-205 alone
(8,438 of 8,438 states, every trace accepted), so only the new traces kill
them in the trace check (trace 206 kills 10, 23, 24, 26 at the call named in
the table; trace 207 kills 13 and 25). 27 and 28 pin the other side of the
same boundaries and were already killed by the old traces (trace 10 submits
at `now + 86401`, trace 128 dispatches at `expires_at - 1`); trace 206 kills
them too. Of the new-trace-only mutants, MC_Safety also kills 10 and 13. 23 and
24 change behaviour only near ±10^6, which MC_Safety's values (within ±5)
never reach; 25 and 26 only reject more calls, which no MC_Safety property
forbids (checked: MC_Safety passes on both, 62,118 and 443,906 distinct
states, 28 s and 197 s with 2 workers).
Mutants 29-31 carry `# checks:` headers so that liveness itself is shown to
kill them (30 is a model mutant the trace replay also kills).

**Equivalent mutant (not checked in).** "`add` ignores the upper bound"
(`AddFails` true only below -MAX_VALUE) survives every check: the trace
replay of all 212 traces (checked again 2026-11-12: 9,016 of 9,016
states, every trace accepted), MC_Safety and the liveness checks
(their values stay within ±3, where `AddFails` is false either way). It is
equivalent, not a gap: every `AddFails` in the model is followed by a
`check_bounds` on the same vector, whose envelope low ≤ value ≤ high, so an
out-of-range sum gives `Arithmetic` there with the same unchanged state; the
recovery add is unreachable (above). The same holds in the core. A
*boundary* weakening (mutant 23) is not equivalent and trace 206 kills it.

## Not covered (open items)

- **TLA-IND (open).** No Apalache inductive check (`run.sh apalache` prints
  `skip`). The model sums with recursion (`SetSum` is `RECURSIVE`, `SumTo`
  a recursive function), which Apalache 0.47.2 rejects ("Apalache does not
  support recursive operators"), and ranges over symbolic bounds
  (`1 .. NR`, `0 .. NR - 1`); an Apalache version needs
  `ApaFoldSeqLeft`/`MkSeq` sums, `DOMAIN`-based ranges and type annotations
  throughout, i.e. a rewrite of the model, which was not done. Safety is
  shown only within the MC bounds plus on the 9,016 core states of the
  212 traces (212 initial + 8,804 steps); the every-size counterpart is
  the Lean layer's.
- **Small universes.** MC_Safety: 2 metrics, 1 term (target shape only), 2
  recipes, ≤ 3 records, 4 accounts, 3 block times, 14 observation vectors.
  MC_Liveness: ≤ 2 records, submit/pause/observe only while version < 4, two
  hand-built configs (`MCConfig`, `CreditHedgeConfig`). No symmetry
  reduction. Other shapes, larger configs and the real record limit are
  covered only by the traces (configs of up to 8 metrics, 6 recipes; one
  trace of 515 calls with 256 records).
- **Version overflow.** The bump guard is transcribed but never reached
  (ASM-MODEL above); no mutant can be killed there. LIVE-1/LIVE-2 assume
  version < u32::MAX.
- **Energy at large residuals** (ASM-MODEL above).
- **Release `Arithmetic`** reachable; covered by trace 208 (F-2 section).
- **Not modelled.** `preview` and `best_quantity` (RD-PREVIEW, RD-BEST), the
  NEAR shell, the executor and promise interleavings beyond "ack and settle
  are independent steps" (ASM-INTERLEAVE).
- **Refinement to the code.** The link from this model to the Rust is only
  REF-5 (traces); per-step Kani refinement (REF-1..3) is not done yet.
- **CI memory.** The `tla` job (`.github/workflows/shared-pool.yml`) fits a
  GitHub-hosted runner at `TLA_HEAP=5g`: GitHub Actions run 43194245726 (PR #31, 2026-11-12, ubuntu-latest, `TLA_HEAP=5g`)
  passed `safety liveness trace` (MC_Safety 2,306,738 distinct states in
  1,300 s) and `mutants`. Peak RSS was not recorded.

## PROP tags

Tagged `PROP: <ID>` where the layer checks them: TLA-SAFE (MC_Safety.tla,
.cfg), TLA-WIT (Props.tla, MC_Safety.tla), TLA-LIVE-1 (MC_Liveness.tla,
MC_Liveness.cfg, MC_Liveness_Unfair.cfg, MC_Liveness_F2Done.cfg),
TLA-LIVE-F1 (MC_Liveness.tla, MC_Liveness_F1.cfg, MC_Liveness_F1Shape.cfg),
TLA-LIVE-F2 (MC_Liveness.tla, MC_Liveness_F2.cfg, MC_Liveness_F2Shape.cfg;
now in the catalogue, `property/3` of `traceability.pl`), REF-5 (TraceCheck.tla, trace2tla.py),
TX-0 and TX-NOOP (TraceCheck.tla `Replay`), CFG-1 (TraceCheck.tla `TInit`,
partial: Pool::new-accepted configs only), LIVE-2 (MC_Liveness.tla), and the
invariants and step properties in Props.tla. `run.sh` lists the layer IDs.
