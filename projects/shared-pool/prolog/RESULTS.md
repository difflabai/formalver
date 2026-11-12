# shared-pool: Prolog layer results

Pin: difflabai/shared-pool-controls `a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`
(PR #1 head). Docs transcribed: `docs/spec.md`, `docs/api.md`,
`docs/verification-handoff.md` at that pin, cited as `spec:<line>`,
`api:<line>`, `handoff:<line>`. Tools: Scryer Prolog 0.10.0
(`scryer-prolog`, every suite run as
`-g "(catch(run_tests,E,(write(E),nl,halt(2))) -> halt(0) ; halt(1))" </dev/null`)
and python3 for `extract.py` (run with `-I`, stdlib only). Conformance traces:
`conformance/traces/core.txt`, sha256
`1ed106947f6049d57f92d2092c8868c5082c0e06f2600e0c2f1138147a718b13` (206 traces,
8,232 calls, generated from the real core). Run:
`projects/shared-pool/prolog/run.sh` (optional `PROLOG_LOGS=<dir>`). Final run on
2026-11-11: exit 0 in 231.7 s, `=== ALL PROLOG CHECKS PASSED ===`.

Evidence vocabulary (near-approval strategy §12): this layer gives `check`
(C-1..C-6), `model-check` (MC-1, LIVE-2) and `test` (the MC-2 replay, the step
properties checked on the real core's traces and the step/4 unit tests).

## Layout

| File | Contents |
|---|---|
| `requirements/pool_req.pl` | 65 `requirement/3` facts (one per doc statement used); the api.md method table and authority (`method/4`, `method_core/2`); the guard tables in the order the docs list them (`guard/5`, 56 rows; each row is `doc`, `doc_condition` (the docs state the condition but not its name or position) or `code_only`); the lifecycle table (`life/5`); constants; the five fixtures with 23 claims (`fixture_claim/4`); `known_finding/2`; `finding/4` (F-1..F-6); 4 `divergence/4` and 8 `ambiguity/4` facts. |
| `requirements/threat_model.pl` | 6 adversaries, 22 threats with mitigating properties and residuals (every finding is named in a residual, which C-6 checks), and the brief's 14 ASM-* assumptions. |
| `requirements/traceability.pl` | The brief's 95-ID catalogue with layers, `prolog_evidence/2` for the 39 IDs this layer carries, and requirement → property rows. |
| `model/pool_machine.pl` | `step/4`, written from the docs. `step` walks the guard table of `pool_req.pl` in order, so the model's behaviour *is* the requirement table. 16 places are tagged `CODE-ONLY` where the docs are silent (NotFound, saturating u64 time sums, the observe length check, ack from Reserved/Active, the MAX_* bounds, actor = executor accepted, ...). Where docs and code disagree, the place carries a divergence id. Reads: `admissible/3`, `preview_allowed/3`, `best_quantity/4`. |
| `extract.py` → `extracted/code_facts.pl` | Generated from `crates/core/src/lib.rs`: constants, enums, field widths, per-function error sites, fallible calls, early `Ok` returns, caller checks, status guards and writes, and role comparisons in `Config::validate`. Also from `crates/contract/src/lib.rs` (`#[near]` methods, attributes, receivers, core calls and each one's caller source) and `crates/core/src/fixtures.rs` (fixture order, account names). The parser is narrow and fails loudly on constructs it does not know. |
| `extract.py` → `extracted/tla_facts.pl` | `GuardOrder` from `tla/SharedPool.tla` and the LIFE-1 `Edges` from `tla/Props.tla`. |
| `verification/consistency.pl` | C-1..C-6. Every problem is collected, and each check reports non-vacuity counts. |
| `verification/model_check.pl` | MC-1: breadth-first exploration of three universes through `step/4`; dead records; release-blocked states. |
| `verification/props.pl` | Invariants (INV-WF, INV-LEDGER, INV-HARD, INV-HEALTHY, INV-DEP, INV-VER), step properties (TX-0, TX-NOOP, TX-VER, AUTH-1, STALE-1, ADM-1, ADM-2, HARD-STEP, DEP-1, LIFE-1, ASYNC-1, TERM-1, OBS-1, PAUSE-1) and LIVE-1. MC-1 and MC-2 both use them. |
| `verification/{mc2,traces,util}.pl` | The MC-2 replay and the trace reader. |
| `tests/test_{requirements,model,mc1,mc2}.pl` | The suites (`run_tests`), via `tests/support/harness.pl`. |
| `mutants/{model,code}/*.patch` | 17 model mutants and 9 code mutants, each with `# expect: <suite> <test prefix>` lines. |
| `run.sh` | The runner. |

`run.sh` steps:
1. `extract.py --check`: regeneration gives no diff.
2. Each suite must exit 0 with no loader `Warning:` in its log. A discontiguous predicate silently drops clauses, so a warning fails the step.
3. Canaries: `test_requirements`, `test_model` and `test_mc2` each run with `SHARED_POOL_PROLOG_CANARY=1` and must exit 1 with only the canary test failing.
4. PROP tags: every catalogue ID with the prolog layer is tagged in a `.pl/.py/.sh` file here, and no tag is unknown.
5. Mutants: each patch is applied to a scratch copy (code mutants patch a copy of the source mirror and re-extract). Every `# expect:` suite must exit non-zero and print `FAIL <prefix>`.

## Results

| Check | ID | Result | Size / time |
|---|---|---|---|
| `extract.py --check` | C-1..C-4 inputs | extracted facts regenerate with no diff | 0.1 s |
| Authority: api.md table + spec:11 = the shell's `#[near]` attributes, receivers and caller sources + the core's caller checks. `on_result` is private and drives only settle/acknowledge, with the recipe executor. `preview` cannot mutate. Nothing is payable. | C-1 | pass | 12 methods, 12 shell methods, 6 core caller checks, 14 shell → core calls |
| Guard order: `guard/5` (docs order) = each entry point's code path (calls expanded in place) = TLA+ `GuardOrder`. api:28's reason list = the errors reachable in `candidate`. Every `Error` variant is accounted for. | C-2 | pass | 8 op kinds, 56 guards (31 doc, 19 doc_condition, 6 code_only); 5 unreachable-site rules used; TLA leg compared; a swapped pair is detected for every kind |
| Lifecycle: `life/5` = the code's status guards = TLA+ `Edges` = the props LIFE-1 graph, and = the status changes seen in the real traces | C-3 | pass, with one recorded divergence (`div-ack-noop-version`) | 36 (op, flag, status) rows, 11 edges; all 36 rows observed in the traces, 2 trace calls on the divergent row |
| Constants: docs = code (MAX_VALUE, MAX_TERMS, MAX_WEIGHT, MAX_RECORDS, 86,400 s, page 50, u32 version, u64 times); spec:13's derived bounds; the model's code-only bounds = code | C-4 | pass | 8 compared, 4 derived; MAX_METRICS 32, MAX_RECIPES 32 and MAX_UNITS 100 are code-only |
| Fixture claims on trace configs 1-5 (STOCK, CASH, RISK, GPU/Friday, self-authorization, spec:46 release) | C-5 | pass, with 2 known findings reproduced (F-2, F-4) | 23 claims. STOCK-SUM over 41 calls; CASH-SUM over 40 (until the first observe). RISK-HEADROOM on 46 states, 474 admissible requests. Release search: 1,308 / 1,308 / 36 / 28 / 86 admitted pairs (gpu / friday / inventory / hiring / risk) and 22,128 releases tried, plus 448 releases on 179 trace states. |
| Traceability: the catalogue = the brief (95 IDs); every requirement traced; every threat mitigated; every finding named in a threat; prolog evidence for each prolog property | C-6 | pass | 95 properties, 65 requirements, 22 threats, 6 findings, 14 assumptions |
| MC-1 `wedge` (trace 0's config) | MC-1, LIVE-2 | no violation; F-1 dead in-flight records found | 3,740 states, 113,172 edges, complete; 228 states with a dead in-flight record |
| MC-1 `healthy` (2 recipes, a prerequisite, freshness) | MC-1, LIVE-2 | no violation; no dead or release-blocked record | 3,856 states, 98,056 edges, complete; 10 error kinds reached |
| MC-1 `reliance` (F-2, scaled down) | MC-1, LIVE-2 | no violation; 150 release-blocked states with B = 0 | 630 states, 14,236 edges, complete |
| MC-1 suite total | | | 33.9 s |
| MC-2: every trace replayed through `step/4` from the code's pre-state; result and post-state compared exactly; invariants, step properties and LIVE-1 checked on the code's own states | MC-2, TX-*, INV-*, LIVE-1 | 0 divergences, 0 violations | 206 traces, 8,232 calls; every op kind Ok and 13 error kinds; 2.5 s |
| step/4 unit tests (doc-cited), including the F-1..F-6 witnesses and the RD-PREVIEW/RD-BEST model checks | TX-*, RD-* | 29 pass | 0.5 s |
| Requirements suite (C-1..C-6 and their non-vacuity tests) | C-* | 12 pass | 9.9 s |
| Canaries | vacuity | each of the three suites exits 1 with only the canary failing | |
| Planted faults (in `test_mc2`): each step-property checker fires on a corrupted real call and stays silent on the real one (TX-0, TX-NOOP, TX-VER, AUTH-1, STALE-1, ADM-1, ADM-2, HARD-STEP, DEP-1, LIFE-1, ASYNC-1, TERM-1, OBS-1, PAUSE-1); a corrupted trace shows as a divergence with its trace id and index. In `test_model`: the INV-* and LIVE-1 checkers fire on corrupted states. | vacuity | pass | |
| PROP tags | | every prolog-layer catalogue ID is tagged; no unknown tag | 39 of 95 |
| Mutants | | 26 of 26 killed | 168.8 s |

MC-1 bounds. The exploration state is pool + clock + ghost. Time is monotone
(ASM-TIME) over each universe's time set: wedge {100, 200}, healthy {100, 150,
250}, reliance {100, 250}. Callers are each recipe's actor and executor, the
owner and a stranger `z`. Submits are generated at the current version and at a
stale one, with units up to the recipe's maximum. Observation vectors are fixed
per universe; wedge includes the disturbing [12, 5].

Record caps are 3 (wedge) and 2 (healthy, reliance). A state where a further
submit would have been Ok is marked truncated and never certified dead. The
visited key drops the version and the effect counter. These are bisimilar,
because guards read the version only by equality and against u32::MAX. INV-VER
is therefore checked per edge (TX-VER). Exploration stops at the first
violation.

## Findings

This layer reproduces all six of the brief's findings.

**F-1 (wedge; high).** MC-1 `wedge` certifies dead in-flight records in 228
states (records 0-2). The shortest witness is `observe(o, [12,5])`,
`submit(a1, 0, 1)`, `dispatch`. After it, the record can never become terminal:
`settle` fails `Bounds` both ways, and `cancel` and `observe` fail `Pending`.
Trace 0 replays exactly through `step/4` (MC-2). The `test_model` unit test
replays it call by call and shows that, without the disturbing observe, the same
reservation is rejected. Divergence `div-F1-inverse`: spec:46 and handoff:31
attribute a failing inverse to a dependent commitment, and F-1 has none.

**F-2 (release blocked in a healthy state; high).** spec:46 claims that "in the
supplied fixtures, physical availability and risk-credit timing prevent ordinary
unsafe reliance on unexecuted work". C-5 checks this per fixture with a
two-record search from the fixture's init state. It holds for gpu, friday,
inventory and hiring, and on every pre-observe state of their traces. It fails
for risk, with 20 counterexamples.

The first counterexample is a credit position (recipe 0 × 1), then a hedge
(recipe 3 × 7). The hedge is admissible only because the position's +20 on
metric 0 is counted (60 + 20 − 70 ≥ 0). Releasing the position then takes
metric 0 below its minimum: 60 − 70 < 0 while the hedge is open (cancel), or
10 − 20 < 0 once it has filled (`settle(false)`). Both releases fail `Bounds`.
No observe is involved, and no metric is out of bounds (B = 0).

MC-1 `reliance`, the same shape scaled down, finds 150 states with B = 0 where
the executor's honest `settle(false)` of an in-flight position is rejected. The
step/4 witness in `test_model` (risk fixture: position × 1, hedge × 7, hedge
completed) shows two more things. `settle(true)` still succeeds, so LIVE-1 is
unaffected. Admitting a further position frees the old one, but only by moving
the same blocked liability to the new record. Divergence
`div-F2-fixture-release` (spec:46; spec:66; handoff:23). C-5 lists F-2 under
`findings` and fails if it ever stops reproducing; mutant m17 shows this.

Reproducer: `test_model` "F-2 witness", or C-5's `findings` line in
`test_requirements` (first counterexample `rel(p(0,1,3,7), release(0),
other(reserved), via(cancel)) - err(bounds)`). The core reproducer is
`.context/shared-pool/repro/spec-divergence/src/bin/f_risk_fixture_wedge.rs`.

**F-3 (slot exhaustion; low).** step/4 witness: one actor runs 256 submit +
cancel cycles at no cost, leaving every record Cancelled. After that, `submit`
fails `Full`, `observe` is Ok, and `submit` still fails `Full`. The traces never
reach `Full` (it needs 256 records), so this is a model witness only. C-2 checks
the guard's position against the code.

**F-4 (self-authorization; low).** `extract.py` records the role comparisons
in `Config::validate` as `code_role_checks(validate, [])`. C-5 claim
CASH-SELF-ENFORCED (spec:64 read as a property of the wrapper) is the known
finding. CASH-SELF, which checks the hiring fixture's own account names from
`fixtures.rs`, holds. step/4 witness: a config with actor = executor validates,
and that account settles its own work. Ambiguity `amb-self-executor`. Mutant c09
(validate rejects actor = executor) makes C-5 fail with
`known_finding_not_reproduced`.

**F-5 (version saturation; low).** step/4 witness: at version = u32::MAX,
`settle` both ways, `acknowledge` and `set_paused(false)` all fail
`Arithmetic`. The paused pool cannot be unpaused, and the in-flight record
blocks `observe` (`Pending`).

**F-6 (stale snapshot; low).** step/4 witness on the risk fixture (max_age 300,
observed at 100). With one record in flight, at now = 401 `dispatch` and
`submit` fail `SnapshotExpired` and `observe` fails `Pending`. Only the
executor's settle unblocks the pool.

### Docs vs code

- `div-ack-noop-version` (spec:39 lists Dispatched/Unknown → Unknown; api:26
  says every successful state transition changes version): `acknowledge`
  returns `Ok` without a version bump when the status would not change, and for
  Reserved or Active records. C-3 finds exactly this one row (ack, false,
  Unknown), and the traces show it twice. Mutant m02 (the model bumps) is
  killed by MC-2.
- `div-cancel-terminal-name` (spec:43; api:15): cancelling a Completed or
  dispatched record is rejected, as the docs require, but with `Pending`, which
  does not say "already completed".
- `div-F1-inverse` and `div-F2-fixture-release`: see F-1 and F-2.

The model follows the code's reading of each ambiguity. Each one is recorded,
and the model tags it `CODE-ONLY`:
- interval violation amount (spec:21)
- freshness boundary (spec:19, 37)
- recovery error name (spec:23)
- ack from Reserved/Active (spec:38-39, 44)
- reconcile as a non-mutating call (api:13)
- what counts as a "state transition" (api:26)
- observe vector length (spec:54)
- actor = executor (spec:9, 50, 64)

## Mutants

All 26 are killed. "Killed" means every `# expect:` suite exits non-zero and
prints `FAIL <prefix>`.

| Mutant | What it changes | Killed by |
|---|---|---|
| m01-hard-ok-nonstrict | ADM-1/HARD-STEP: a disturbed state accepts E ≥ P instead of E > P | test_model (submit reasons), test_mc2 |
| m02-ack-noop-dropped | a repeated acknowledgment bumps version (div-ack-noop-version) | test_model, test_mc2 |
| m03-freshness-strict | the snapshot is stale at exactly observed_at + max_age | test_model (boundaries), test_mc2 |
| m04-expiry-horizon-strict | expires_at = now + 86400 is rejected | test_model (two tests) |
| m05-recovery-nonstrict | ADM-2: recovery accepts a completion that does not lower energy | test_mc2 |
| m06-prerequisite-strict | DEP-1: a prerequisite needs more than the required units | test_model (CASH-PREREQ), test_mc2 |
| m07-envelope-skip-dropped | the record being released is counted twice in the envelope | test_model (STOCK), test_mc2 |
| m08-dispatch-expiry-inclusive | dispatch at exactly expires_at is accepted | test_model |
| m09-energy-strict | ADM-1: a reservation that keeps energy equal is rejected | test_model (F-1 witness), test_mc2 |
| m10-cancel-owner-dropped | AUTH-1: the owner can no longer cancel | test_model, test_mc2 |
| m11-settle-caller-actor | AUTH-1: settle checks the actor instead of the executor | test_model (TERM-1), test_mc2 |
| m12-observe-pending-dropped | F-1 hidden: observe ignores open records | test_model (F-1), test_mc2 (F-1), test_mc1 (wedge) |
| m13-in-flight-reserved | LIFE-1: settle accepts a Reserved record | test_mc2 |
| m14-status-change-no-bump | TX-VER: a status change does not advance version | test_model, test_mc2 |
| m15-release-adds | TERM-1: cancellation adds the reservation instead of subtracting it | test_model, test_mc2, test_mc1 (healthy) |
| m16-guard-order-paused-stale | C-2: the specified submit order checks Stale before Paused | test_requirements (C-2), test_model, test_mc2 |
| m17-release-no-bounds | F-2 hidden: cancel and settle(false) skip the bounds check | test_requirements (C-5), test_mc2, test_mc1 (reliance) |
| c01-submit-stale-before-paused | core checks Stale before Paused | test_requirements (C-2) |
| c02-dispatch-caller-executor | dispatch authorizes the executor | test_requirements (C-1) |
| c03-settle-unknown-dropped | settle no longer accepts Unknown | test_requirements (C-3) |
| c04-max-records-255 | MAX_RECORDS = 255 | test_requirements (C-4) |
| c05-settle-private | `settle` becomes `#[private]` | test_requirements (C-1) |
| c06-pause-no-bump | set_paused no longer advances version | test_requirements (C-2) |
| c07-cancel-owner-dropped | the core no longer lets the owner cancel | test_requirements (C-1) |
| c08-fixture-self-executor | a hiring recipe's actor is its executor | test_requirements (C-5, CASH-SELF) |
| c09-validate-rejects-self-executor | F-4 fixed upstream: validate rejects actor = executor | test_requirements (C-5: `known_finding_not_reproduced`) |

## What is not shown

- **Independence (ASM-SPEC).** Unlike near-approval's M4, the author of this
  layer had read the code, because the shared brief transcribes it. Doc-backed
  facts cite their doc line and code-only facts are labelled, but no independent
  reviewer has checked the transcription (`status.toml` `spec_reviewer` is
  empty).
- **Bounds.** MC-1 explores three small universes (at most 3 records, 2-3
  times, fixed observation vectors). C-5's release search covers two records
  from each fixture's init state, plus the trace states before the first
  observe. It does not search reliances that need three or more records or that
  arise after an observe. "No counterexample" for gpu, friday, inventory and
  hiring is bounded evidence, not a proof.
- **MC-2 coverage.** The traces reach every op kind's Ok and 13 error kinds.
  They never reach `Full` or `Arithmetic` (those need 256 records or values near
  ±1e6), and never a version near u32::MAX. Those guards are checked only by C-2
  (order) and the step/4 unit tests. No trace config has actor = executor. F-3,
  F-4 and F-5 therefore have model witnesses only (plus, for F-4, the extracted
  fact).
- **Reads.** RD-PREVIEW and RD-BEST are checked on the model only: preview
  allowed ⇔ submit Ok over a request grid, and best_quantity against brute
  force. They are not compared with the code's `preview` or `best_quantity`;
  Kani and near-tests cover that.
- **C-2 unreachable sites.** The alignment may skip five kinds of code error
  site that cannot fire from an INV state. Each rule names what discharges it:
  - `add_length`: CFG-2, INV-WF.
  - `energy_terms`, `energy_sum`: NUM-1.
  - `recovery_add`: INV-HARD.
  - `release_record`: no property (release looks up again a record it has just
    found).
  The other layers prove these; this layer assumes them.
- **TLA leg.** C-2 and C-3 compare `GuardOrder` and `Edges` as written in the
  TLA+ files. That the TLA+ operators follow `GuardOrder` is the TLA layer's
  REF-5.
- **Extraction (ASM-TOOLS).** `extract.py` is a narrow regex/brace parser over
  this pin's sources. A construct outside its grammar is an error, but a
  semantically different construct inside it could be misread. Code mutants
  c01-c09 show that it sees the changes they make.
- **Shell.** C-1 checks attributes, receivers and which core call receives the
  predecessor. Runtime behaviour belongs to near-tests and sandbox.
- **Strings.** Name, unit and owner length validation (1..128) is not modelled;
  trace configs carry no names.
- **MC-1 canary.** `test_mc1` (about 34 s) has no canary run. Its non-vacuity
  comes from the counts it asserts (F-1 dead records in wedge, F-2
  release-blocked states in reliance, zero of both in healthy) and from
  mutants m12, m15 and m17.
