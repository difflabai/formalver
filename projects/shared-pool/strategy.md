# Shared Pool Controls Formal Verification Strategy

## Target

[`difflabai/shared-pool-controls`](https://github.com/difflabai/shared-pool-controls)
v1.0.0 (PR #1, merged) is a NEAR contract that admits agent work against one shared pool of
bounded metrics. The pool holds metric values, an immutable policy, and up
to 256 commitment records. The policy has metrics with hard bounds,
weighted potential terms, and recipes. Each recipe names one actor and one
executor, with reservation and completion effects, a unit cap, and
prerequisites on earlier recipes. `pool-core` admits a request only if the
reservation does not raise the potential and keeps every metric's
hard-bound envelope, over the open completions, no worse than now. The
actor dispatches, the contract calls the recipe's fixed executor, and the
executor settles the record as completed or not executed. The owner pauses
the pool and, when no record is open, replaces the measured values
(`observe`).

| | |
|---|---|
| Pinned commit | `a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`, head of PR #1 (branch `feat/shared-pool-controls`, 2026-11-12 UTC, "Address review: reconcile griefing, broken doc link, CI robustness"). PR #1 has merged (`b9e994f`), and the pin is on upstream `main`. |
| Verified version | shared-pool-controls v1.0.0 (`6f61616`, "Mark the contract as v1.0.0"). `crates/core/src/lib.rs`, `crates/contract` and `crates/executor` are byte-identical between the pin and v1.0.0; the version number is only in the root `Cargo.toml`. The pin is kept (§13). Upstream PR #4 (v1.1) proposes fixes for the findings; v1.1 is not verified here. |
| Crates | `pool-core` (`crates/core/src/lib.rs`, 492 lines): every decision; zero dependencies in the default build; `#![forbid(unsafe_code)]`; serde and borsh optional. `pool-contract`: a near-sdk 5.29.1 shell (predecessor → caller, block time in whole seconds, core errors → panics, a promise to the executor, a private callback, views). `pool-executor`: the synthetic executor (`execute`, `status`, `finish`, `confirm_not_executed`, fault modes). `crates/sandbox`: upstream's near-workspaces tests. |
| Toolchain | Upstream `rust-toolchain.toml` 1.98. Release profile: codegen-units 1, `opt-level = "z"`, LTO, `panic = "abort"`, `overflow-checks = true` (ASM-COMPILE). |
| TCB via `Cargo.lock` | near-sdk 5.29.1, borsh 1.8.1, serde_json 1.0.154, and their dependencies |
| Mirror | git submodule `projects/shared-pool/source-mirror` (`upstream_path = ""`) |
| Upstream docs | `docs/spec.md`, `docs/api.md`, `docs/verification-handoff.md`, cited as `spec:<line>`, `api:<line>`, `handoff:<line>` at the pin |

The split matches near-approval's. Every decision is in `pool-core`, which
has no dependencies, so Kani can target the deployed logic itself. The
shell is thin enough to cover with tests on the host, on the wasm, and on a
local chain.

**Status (2026-11-13, pin `a4bb5c3`, the contract code of v1.0.0).** Every
layer is built and passes locally. Kani proves, within small bounds, the
transition contracts, the step properties, INV preservation, the
numerics, the reads and the refinement links REF-1..3 on the real
`pool-core` (§6). TLA+, Lean, Prolog and the shell tests replay the same
212 real-core traces (§10). The sandbox compares the chain with a host
`pool-core` oracle. CI passed on GitHub (PR #31) for every layer but
Kani. Kani is split by memory (§14). CI runs plain mode, the plain-mode
mutants and the 53 harnesses that peaked at 13 GB or less on GitHub's
16 GB hosted runner. The other 36 harnesses ran there on swap, slowly,
and some never finished (runs 43469880167 and 43488691444). They, and
the 16 mutants sized by them, were run locally instead, on a 64 GB
Apple M1 Max at commit `89f99d6`, and recorded with a fingerprint of the
Kani inputs. CI checks that record rather than running them again
(`kani/RESULTS.md`, Local record). Two high findings, F-1 and F-2, show
that the settlement liveness the docs rely on does not hold. Nothing is
verified: there is no spec reviewer (§12). Next: the split's first green
CI run, and the findings upstream (§13).

---

## 1. What we establish

For `pool-core` at the pin (v1.0.0's code), and for the shell built as cargo-near builds
it (`--cfg near`, see NT-F1), under the assumptions of §5.14:

| Claim | Properties |
|---|---|
| **(a) Admission.** An accepted `submit` came from the recipe's actor at the current version. Its prerequisites were met by completed units. It did not raise the potential, and in a disturbed state its completion strictly lowers it. It left every metric's envelope over the open completions no worse than the current violation. From a healthy baseline, every subset of open completions lands in bounds. | AUTH-1, STALE-1, DEP-1, ADM-1, ADM-2, HARD-STEP, INV-HARD, INV-HEALTHY |
| **(b) Atomicity and authority.** A rejected call changes nothing in the core, the shell, or the wasm. Only the executor settles. Only the owner pauses and observes. The actor or owner cancels. The caller is the predecessor. `new` and `on_result` are private. | TX-0, SH-5, RT-REVERT, AUTH-1, SH-1, RT-PRED, SH-2, SH-3, RT-PRIVATE |
| **(c) Lifecycle and accounting.** Records are append-only and follow the status graph; terminal statuses are absorbing. Values equal the last observed baseline plus the reservations and completions since. An unknown outcome keeps its reservation. The version counts effective transitions. | LIFE-1, TERM-1, INV-LEDGER, ASYNC-1, INV-VER |
| **(d) Settlement.** In a healthy state, while the version is below u32::MAX, the executor can always settle an in-flight record as completed. **False:** "every dispatched record eventually becomes terminal". F-1 breaks it after a disturbing observe, and F-2 breaks it in a healthy state. | LIVE-1; LIVE-2 fails |

**What "establish" means today.** (a), (c), LIVE-1 and the core half of
(b) (TX-0, AUTH-1) are proved at every size for a Lean transcription of
the core, and checked on the real core's states over 212 traces. All but
TX-0 are also model-checked in TLA+ within small bounds. The shell and
runtime half of (b) (SH-*, RT-*) is tested, not proved, on the host, two
wasm builds and a local chain. SH-5 holds only on the `--cfg near` build
(NT-F1). Kani proves (a), (c), LIVE-1, TX-0 and AUTH-1 on the real
`pool-core`, but only within its bounds: 1 metric, 1 term, 2 recipes and
2 records per step, INV-WF to INV-DEP in every reachable state with at
most 3 records, and INV-VER along 2-operation traces (§6). None is
verified (§12).

**Not established:** that a deployment runs this code (ASM-DEPLOY);
that no code path transfers funds, deploys code or adds keys (source review
only, NT-F3); executor honesty or true observations (ASM-EXEC, ASM-OWNER;
F-2 shows the honest executor is the one that gets stuck); that a policy
models the world (spec:31); receipt order across shards; optimality of
`best_quantity` (spec:27); eventual completion (handoff:29).

### Tiers

| Tier | Layers | State | Result |
|---|---|---|---|
| **1. Code-level core** | Kani (§6) | built | Bounded proofs on the real `pool-core`: every transition contract, the step properties, INV preservation up to 3 records, the numerics, the reads, and REF-1..3, which tie each TLA+ step to the code. Small shapes and anchored values (§6). |
| **2. Models and operational** | TLA+ (§17), Lean (§18), Prolog (§8), near-tests and sandbox (§9) | built | Every-size safety for the model (Lean). Liveness and its failures over all event sequences in small universes (TLC). An independent reading of the docs (Prolog). The shell on the host and two wasm builds. Runtime assumptions on a local chain. TLA+, Lean, Prolog and the shell are tied to the real core by the traces (§10); the sandbox by a host `pool-core` oracle (§9.2). |
| **3. Unbounded on the code** | Verus (§7) | deferred | Removes the transcription gap between the Lean model and the code. |

Tier 1 is done within its bounds. CI runs the 53 harnesses that fit its
hosted runner. The other 36 come from the local record, which CI checks
(§14). Next: the split's first green CI run, and the spec review (§13).
Revisit Tier 3 after upstream decides on F-1 and F-2, since a fix
changes what a proof covers.

### Upstream's obligations (handoff:9-23)

| Obligation | Properties | State |
|---|---|---|
| CFG | CFG-1, CFG-2 | Bounded proof (Kani). Lean takes `validate` as its premise. |
| NUM | NUM-1, NUM-2, ROB-1 | Bounded proof (Kani): `energy` over the whole value range and at 64 terms, `add` at ±1,000,000, no core panic within the step bounds. Trace 206 tests the boundary. |
| AUTH | AUTH-1, SH-1, RT-PRED | Proved (model), bounded proof (Kani), tested. F-4: actor = executor is allowed. |
| ADM | ADM-1, ADM-2, HARD-STEP, INV-HARD | Proved (model), model-checked, bounded proof (Kani). |
| ATOM | TX-0, SH-5, RT-REVERT | Proved (model), bounded proof (Kani), tested. Messages lost on the documented build (NT-F1). |
| STALE | STALE-1 | Proved (model), bounded proof (Kani). |
| ASYNC | ASYNC-1, INV-LEDGER | Proved (model), bounded proof (Kani). RT-CALLBACK. |
| TERM | TERM-1 | Proved (model), bounded proof (Kani). EX-4. |
| DEP | DEP-1, INV-DEP | Proved (model), bounded proof (Kani). |
| BIND | LIFE-1, SH-6, EX-2 | Proved (model), bounded proof (Kani), tested. |
| STOCK, CASH | C-5 | Hold on the fixtures (bounded check). |
| RISK | C-5 | Fails: F-2. |
| Liveness (handoff:31) | LIVE-1, LIVE-2 | LIVE-1 (healthy, version < u32::MAX) proved (model), and by Kani with up to 3 records. LIVE-2 fails: F-1, F-2. |

---

## 2. Scope

| In scope | Detail |
|---|---|
| `pool-core` | `Config::validate`, `Pool::new`, `energy_terms`, `energy`, `submit`, `dispatch`, `acknowledge`, `cancel`, `settle`, `set_paused`, `observe`; the private `add`, `envelope`, `check_bounds`, `candidate`, `release`; the reads `preview` and `best_quantity`; all 16 `Error` variants; `MAX_METRICS` 32, `MAX_RECIPES` 32, `MAX_TERMS` 64, `MAX_RECORDS` 256, `MAX_VALUE` 1,000,000, `MAX_WEIGHT` 1,000, `MAX_UNITS` 100, and the 86,400 s expiry window |
| `pool-contract` | The 12 `#[near]` methods (`new`, `get_pool`, `get_commitments`, `preview`, `submit`, `dispatch`, `reconcile`, `on_result`, `settle`, `cancel`, `set_paused`, `observe`); events; promise shapes; Borsh state; deposits; the wasm surface. Two builds: upstream `scripts/build.sh` (plain cargo) and `--cfg near` (as cargo-near builds). |
| `pool-executor` | The counterparty settlement depends on (EX-*) |
| NEAR runtime | Tested, not proven: predecessor identity, `#[private]`, callbacks and `PromiseError`, per-receipt atomicity, receipt interleaving, gas at the largest state |
| Docs as requirements | `spec.md`, `api.md`, `verification-handoff.md`, transcribed in Prolog (§8) |

**Out of scope:** `crates/demo`, `ui/`, `scenarios/` and upstream's HTTP
smoke checks; deployment (none exists; code replacement, spec:56, is
ASM-DEPLOY); storage staking (no layer runs an account at its storage-stake
minimum; §9.2, §9.3); policy design and economics; executor honesty and
owner truth; broker fills, physical delivery and token custody
(handoff:40).

---

## 3. Threats and trust assumptions

Transcribed in `prolog/requirements/threat_model.pl`. C-6 checks that
every threat has a mitigation or residual, and every finding a residual.

### 3.1 Adversaries

| ID | Adversary | Capabilities |
|---|---|---|
| ADV-ACTOR | A recipe actor, or anyone holding its key | `submit`, `dispatch` and `cancel` with any arguments, in any order; reads all state |
| ADV-ANY | Any NEAR account | Every public method, including `reconcile` (api:13) and `preview` with any proposed actor |
| ADV-RELAY | A contract between a key holder and the pool | Its calls are attributed to it, not to the signer (spec:11) |
| ADV-EXEC | The recipe's executor | Attests completion or nonexecution. Trusted only for the truth of that (ASM-EXEC). |
| ADV-OWNER | The owner | Pause, observe, cancel. Trusted for the truth of observations (ASM-OWNER). Not assumed powerless (spec:56). |
| ADV-DEPLOY | A full-access key on the deployment account | Can replace the code (spec:56). Out of scope (ASM-DEPLOY). |

### 3.2 Threats → mitigating properties

| T | Threat | Mitigated by | Residual |
|---|---|---|---|
| T-ATTRIB | A call attributed to an actor that did not make it | AUTH-1, SH-1, RT-PRED, C-1; ASM-PRED | none |
| T-INIT | Foreign or repeated initialization | SH-2, RT-PRIVATE, C-1; ASM-PRIVATE | none |
| T-FORGE | Execution evidence forged through the callback or a non-executor settle | SH-3, RT-PRIVATE, AUTH-1, C-1; ASM-CALLBACK | none |
| T-REPLAY | An accepted request replayed (there is no nonce) | STALE-1, TX-VER, INV-VER | none |
| T-OVERCOMMIT | An admission lets some subset of open completions break a bound, or worsens a disturbed metric | HARD-STEP, INV-HARD, INV-HEALTHY, TX-SUBMIT | none |
| T-ENERGY | An admission raises the potential | ADM-1, ADM-2 | none |
| T-OVERFLOW | Overflow in values, envelopes, energy or version | NUM-1, NUM-2, ROB-1, C-4; ASM-COMPILE | F-5 |
| T-PARTIAL | A rejected call leaves part of its effect | TX-0, SH-5, RT-REVERT; ASM-ATOMIC | none |
| T-DOUBLE | A record settles twice, or both ways | TERM-1, LIFE-1, EX-4, C-3 | none |
| T-UNKNOWN | An unknown acknowledgment releases a reservation whose job may have run | ASYNC-1, RT-CALLBACK, SH-3, INV-LEDGER | ASM-EXEC |
| T-PREREQ | Dependent work admitted before its prerequisites complete | DEP-1, INV-DEP, C-5 | none |
| T-SELF | A worker authorizes its own acceptance | C-5, AUTH-1 | F-4 |
| T-PAUSE | Admission while paused, or pausing blocks settlement | PAUSE-1, C-2 | none |
| T-OBS | `observe` with open records, changing policy, or deleting history | OBS-1, INV-WF | ASM-OWNER |
| T-BIND | The executor runs another recipe or quantity, or a duplicate runs twice | EX-1, EX-2, SH-6, LIFE-1 | none |
| T-RECONCILE | Anyone churns the version with `reconcile` to make requests `Stale` | SH-7, TX-NOOP, C-3 | At most two bumps per record; docs disagree (§4.3) |
| T-DEPOSIT | A mutating method keeps an attached deposit | SH-10, C-1 | NT-F2 |
| T-GROWTH | Unbounded storage or gas | INV-WF, RES-1, SH-9, C-4 | none |
| T-SLOTS | One actor exhausts the 256 lifetime records | INV-WF, TX-SUBMIT, C-4 | F-3 |
| T-FRESHNESS | A long-open record blocks the only snapshot refresh | TX-SUBMIT, TX-DISPATCH, OBS-1 | F-6 |
| T-WEDGE | A record can never become terminal, and the pool can never be observed again | detected by LIVE-1, LIVE-2, MC-1, RT-WEDGE, TLA-LIVE-F1, LEAN-WIT, C-5 | F-1, F-2 |
| T-REDEPLOY | Code replaced through a full-access key | ASM-DEPLOY | out of scope |

For T-SLOTS, T-FRESHNESS and T-WEDGE, the listed properties detect or
bound the threat. They do not prevent it.

### 3.3 Trust assumptions (TCB)

The 14 assumptions, with their levels and what checks each, are the table
in §5.14 (`threat_model.pl`'s `assumption/3`). They are in `status.toml`
as `[assumptions.<ID>]`, next to the properties (§12). PRED, PRIVATE,
CALLBACK and ATOMIC (high) and INTERLEAVE (med, one shard) are tested on
the real runtime. COMPILE is checked by `check-pin.sh`. TIME (high) and
EXEC, OWNER and DEPLOY (policy) are untested. TOOLS, MODEL and LEAN-TLA
(med) rest on the layers' own controls. SPEC (low) rests on a reviewer who
has not been named.

---

## 4. Findings

Every core finding but F-5 has a conformance trace of the pinned core:
F-1 trace 0, F-2 trace 209 (the `Bounds` form) and trace 208 (F-2b), F-3
trace 207, F-4 trace 210 and F-6 trace 211 (§10.1). TLA+, Lean, Prolog
and the shell (host and both wasm builds) replay each with equal results
and post-states. F-5 needs version u32::MAX, 2³² − 1 effective
transitions, out of reach of a trace (the highest trace version is 513);
its evidence is a Prolog witness, a Lean mutant, the sandbox and Kani's
`h_version_max_*` (from states at u32::MAX). F-1 and
F-3 also run on a local chain (RT-WEDGE, RES-1), and part of F-5 on the
wasm (RT-REVERT). Kani witnesses each core finding on the real core
within its bounds, in the sense §6 gives: F-1 by a trace from `Pool::new`,
F-4 by a configuration, F-2, F-2b and F-5 from constructed states, F-3 by
one cycle and the exact limit, F-6 by its mechanism. The §4.2 findings are
tests on the pinned builds.
Severity rates the harm to the property the docs promise.

### 4.1 Open: core

| ID | Finding | Reproducer and layers | Contradicts |
|---|---|---|---|
| F-1 (high) | **Disturbed-state hedge wedge.** An `observe` puts a metric outside [min, max]. The recovery rule (spec:23) then admits a hedge whose reservation brings the point inside, but whose completion moves it back out. From then on `settle(true)` and `settle(false)` both fail `Bounds`, and `cancel` and `observe` fail `Pending`, forever. The record never becomes terminal, and the pool can never be observed again. | **Trace 0.** Metrics m(0,10,5), m(−100,100,5); term t(1,0,1,target); recipe r(a1,x1,[−2,0],[2,−5],1,[]). `observe [12,5]`; submit 1 → `ok(0)`, values [10,5]; dispatch; `ack(true)` → Active; `settle` true and false → `Bounds`; the owner's `cancel` → `Pending`; `observe` → `Pending`. <br>**TLA+:** `Witness_Wedge` (4 states); TLA-LIVE-F1; `MC_Liveness_F1Shape` shows that, in the small universe, every LIVE-2 counterexample is this wedge. <br>**Lean:** `f1_forever` (for every later call sequence, the record stays Active and every observe fails). <br>**Prolog:** MC-1 `wedge` has 228 dead states. <br>**near-tests:** `wedge.rs` (from Dispatched, Unknown and Active; host and both builds). <br>**Sandbox:** RT-WEDGE. The executor commits "completed", its `settle(true)` fails `Bounds`, and the record stays Active. The executor then refuses `finish(cancelled)` ("terminal outcome conflict") and `confirm_not_executed` ("job exists"). The two contracts disagree permanently. | spec:46: a checked inverse "can fail if another commitment depends on its contribution". handoff:31 makes liveness conditional on resolving dependencies. Here no other commitment is open, so there is nothing to resolve (`div-F1-inverse`). |
| F-2 (high) | **Healthy-state release wedge in the supplied `risk` fixture.** No observe; every metric in bounds. A credit position is reserved (recipe 0, +20 on selloff loss). A selloff hedge (recipe 3, −10 per unit on completion) is admitted only because the position's +20 is counted: 60 + 20 − 70 ≥ 0 at 7 units. The hedge completes, and selloff loss is 10. The position's job never ran, so the executor honestly calls `settle(false)`. Releasing the +20 gives 10 − 20 < 0, so it fails `Bounds`. `cancel` and `observe` fail `Pending`. Only `settle(true)`, an attestation of work that did not happen, ends the record. The same check blocks `cancel` of a Reserved position. LIVE-1 is unaffected. <br>**F-2b** (found by the TLA+ layer): a release is not bounded by the envelope. After a sibling relied on the reservation, `values − reserve·units` can leave ±1,000,000. Then `cancel` (actor and owner) and the honest `settle(false)` fail `Arithmetic`. | **Trace 209** (`f2-risk`, 13 calls, the supplied `risk` config of trace 5, no observe): position × 1 (recipe 0, selloff loss 60 → 80), hedge × 8 (recipe 3, admitted with the position counted: 80 − 80 = 0), both dispatched and Active; the hedge settles completed (selloff loss 0). Then the executor's `settle(false)` for the position → `Bounds`, `cancel` by the owner and by the actor → `Pending`, `observe` → `Pending`; `settle(true)` → Ok, then `observe` → Ok. Equal under TLC, Lean, Prolog (MC-2) and the shell. <br>**Prolog:** `test_model` "F-2 witness" (position × 1, hedge × 7, hedge completed). C-5's release search finds 20 counterexamples in `risk` and none in `gpu`, `friday`, `inventory` or `hiring`. The first is `rel(p(0,1,3,7), release(0), other(reserved), via(cancel)) - err(bounds)`. MC-1 `reliance`: 150 release-blocked states with B = 0. <br>**TLA+:** TLA-LIVE-F2 (weak fairness of the honest `settle(false)` and of `cancel`); `MC_Liveness_F2Shape` shows that, in its small universe (`CreditHedgeConfig`), every LIVE-2 counterexample is this wedge. <br>**F-2b: trace 208** (`release-arith`, 13 calls), equal under TLC, Lean, Prolog and the shell. | spec:46: "In the supplied fixtures, physical availability and risk-credit timing prevent ordinary unsafe reliance on unexecuted work." spec:46 also says "resolve dependent work first", yet the dependent hedge is resolved and the release still fails. handoff:23 (RISK) is the related obligation, not contradicted. `div-F2-fixture-release`. |
| F-3 (low) | **Lifetime slot exhaustion.** One actor fills all 256 lifetime records with free submit-and-cancel cycles. After that, `Full` is permanent for every actor. `observe` does not prune (spec:54), and nothing else does. | **Trace 207** (`full`, 515 calls): submit `ok` 256, cancel `ok` 256, then submit `full` 2 (another actor, also after an observe). TLC TraceCheck (it also kills TLA+ mutants 13 and 25), REF-5L, MC-2, near-tests `traces.rs` and `sh4`. Sandbox RES-1: submit #257 is rejected `Full`. | Not explicit. handoff:34: "256 lifetime records bound ordinary growth". |
| F-4 (low) | **A principal can attest its own work.** `Config::validate` accepts a recipe whose actor is its executor, or the owner. That account can then submit, dispatch and settle its own work as completed. | **Trace 210** (`f4-self`, 8 calls): `validate` accepts recipe 0 with actor = executor = a1 and recipe 1 with actor = executor = the owner o. a1 submits, dispatches and settles record 0 completed, and o does the same with record 1; every call is Ok. Equal under TLC, Lean, Prolog and the shell. <br>**Prolog:** `test_model` "F-4 witness" (step/4). `extract.py` records `code_role_checks(validate, [])`. Code mutant c09 (validate rejects actor = executor) makes C-5 fail. | spec:64: "No worker can authorize its own acceptance through the wrapper". spec:50: "the independent operator". `amb-self-executor`. |
| F-5 (low) | **Version saturation freezes every transition.** At version = u32::MAX, every transition fails `Arithmetic`, including settling in-flight records and `set_paused(false)`. Reaching it takes 2³² − 1 effective transitions. | **No trace:** reaching version u32::MAX takes 2³² − 1 effective transitions; the highest version in the traces is 513. <br>**Prolog:** `test_model` "F-5 witness" (step/4 from a paused state at version u32::MAX with record 0 Dispatched: `settle` both ways, `ack` and `set_paused(false)` fail `Arithmetic`, `observe` fails `Pending`). <br>**Lean:** mutant 04 (version overflow one too late) is killed by the proofs. <br>**TLA+:** no witness; `VerErr` transcribes the bump, but `MaxVersion` is 2³¹ − 1 and no run gets near it (§17.5). <br>**Sandbox:** RT-REVERT patches version = u32::MAX into the state: `set_paused` and `submit` fail, and storage is unchanged. <br>**Kani:** `h_version_max_<op>`: from every INV state at version u32::MAX within the step bounds, every effective call of each kind fails `Arithmetic` and changes nothing. Reaching u32::MAX from `Pool::new` is not shown. | None. handoff:34 documents "Version overflow is an explicit rejection". The effect on in-flight records is not documented. |
| F-6 (low) | **An open record blocks the only snapshot refresh.** With `max_age > 0`, one record open longer than `max_age` freezes the pool. `observe` needs every record terminal, so it fails `Pending`. `submit` and `dispatch` fail `SnapshotExpired` until the executor settles. | **Trace 211** (`f6-stale`, 12 calls): max_age 50, observed at 100; record 0 dispatched and Active. At now = 151, `submit` and `dispatch` fail `SnapshotExpired` and `observe` fails `Pending`; with the other record cancelled, `observe` still fails `Pending` while record 0 is open. Once the executor settles record 0, `observe` and then `submit` are Ok. Equal under TLC, Lean, Prolog and the shell. <br>**Prolog:** `test_model` "F-6 witness" on the risk fixture: max_age 300, observed at 100, one record in flight. At now = 401, `dispatch` and `submit` fail `SnapshotExpired`, and `observe` fails `Pending`. | Not explicit. spec:19, 37 and 54 state the two rules separately. |

### 4.2 Open: shell, build and runtime

| ID | Finding | Reproducer | Contradicts |
|---|---|---|---|
| NT-F1 = SB-1 (medium; diagnostics, not safety) | The documented build (`scripts/build.sh`, plain `cargo build`) omits `--cfg near`. near-sdk 5.29.1 then compiles its fallbacks: `env::panic_str` becomes `eprintln!` + `panic!()`, and the wasm does not import `panic_utf8`. Every on-chain failure becomes a bare `unreachable` trap. State still reverts, but a caller cannot tell `Pending` from `Bounds` from `Unauthorized`. | `nt_f1_upstream_build_drops_every_panic_message`; sandbox `sb1_upstream_build_loses_panic_messages` | api:40; SH-5. Upstream's sandbox `fail` helper (`crates/sandbox/tests/integration.rs:36`) only asserts `is_failure()`. Fix: `cargo near build` or `RUSTFLAGS="--cfg near"`. |
| NT-F2 (low) | `reconcile` is a `&self` method, so near-sdk generates no deposit check. It accepts an attached deposit and keeps it. | `nt_f2_reconcile_accepts_and_keeps_an_attached_deposit` | api:3: "All mutating methods are nonpayable" |
| NT-F3 (informational) | Both contracts, in both builds, import 15 host functions that deploy, delete accounts, add keys, transfer, stake, or use gas keys or global contracts. near-sdk's generic `Promise` code links them. Source review finds only `function_call` actions, and no wasm call in the suite (more than 50,000) reached one. The import surface alone cannot rule out an escape hatch. | `near-tests/run.sh surface`: SURF-2 fails with exactly the recorded imports (expected-fail) | None; weakens the evidence for ASM-DEPLOY |
| NT-F4 (low) | A promise result that is not a JSON string makes `#[callback_result]` panic. The record stays where it was instead of becoming Unknown. The pinned executor always returns strings. | `sh3_non_string_promise_results_fail_the_callback` | api:34: "unexpected strings become Unknown in the wrapper" |

### 4.3 Docs vs code

| ID | Docs | Code | Resolution |
|---|---|---|---|
| `div-ack-noop-version` | spec:39 lists "Dispatched/Unknown -> Unknown". api:26: "Every successful state transition changes version". | Returns `Ok` with no version bump when the status would not change. The comment says why: `reconcile` is permissionless, so a no-op bump would let anyone invalidate every in-flight request. | The code is right; the docs should change. C-3 finds exactly this row, and the traces reach it twice. TLA+ mutant 07 and Prolog m02 pin it. |
| `div-cancel-terminal-name` | spec:43, api:15 | Cancelling a Completed or dispatched record is rejected, but with `Pending`. That name suggests an open commitment. | Rename, or document it. |

`div-F1-inverse` and `div-F2-fixture-release` are F-1 and F-2.

Where the docs are silent, the Prolog model follows the code and records
the gap (`ambiguity/4`). There are eight: the violation amount of an
interval (spec:21); the freshness boundary (spec:19, 37); the recovery
error's name (spec:23); acknowledgment from Reserved or Active (spec:38-39,
44); whether `reconcile` mutates (api:13); what a "state transition" is
(api:26); the observe vector length (spec:54); actor = executor (spec:9,
50, 64).

### 4.4 Rejected

| ID | Claim | Why rejected |
|---|---|---|
| L-1b | In a disturbed state, a reservation that cured the violation cannot be cancelled by the actor or the owner, and the executor's `settle(false)` fails `Bounds`. | This is documented behaviour. spec:41-42 make cancel and nonexecution a checked inverse. spec:46: "There is no forced administrative release that bypasses these checks." HARD-STEP forbids every call but `observe` from raising a violation. On the pinned core, `settle(true)` still returns Ok and completes the record. The case where neither settle works is F-1. |

**Observations, not findings.** At version = u32::MAX, `preview` says
allowed but `submit` panics `Arithmetic` (RD-PREVIEW excludes that
version). A rejected `submit` rewrites `STATE` with the same bytes (gas
only). `dispatch` and `reconcile` call `value_return("null")` before
`promise_return`, and the promise wins. Anyone's `reconcile` bumps a
record's version at most twice.

---

## 5. Property catalogue

The IDs below are exactly the 97 `property/3` IDs of
`prolog/requirements/traceability.pl`. C-6
(`prolog/verification/consistency.pl`) now compares `traceability.pl`
with this section, not with the brief: the IDs are the first cell of every
table row between this heading and the next `## ` heading, and each row's
*Layer(s)* must equal `property/3`'s layer list, in order. None may be
missing, extra or repeated on either side. A missing file, a missing
section or an empty ID set fails C-6. The `prolog` CI job runs it. Every
table row in this section starts with a bare ID, and the section has no
other tables.

**Notation.**
- **Point violation:** `PV_i(v) = max(0, min_i − v_i) + max(0, v_i − max_i)`.
- **Open and in flight:** a record is *open* unless Completed or
  Cancelled. It is *in flight* when Dispatched, Active or Unknown.
- **Envelope:** computed over the open records (optionally skipping one
  and adding one): `low_i = v_i + Σ min(0, complete_i·u)` and
  `high_i = v_i + Σ max(0, complete_i·u)`. Its violation is
  `EV_i = max(0, min_i − low_i) + max(0, high_i − max_i)`.
- **Ghosts:** `base` and `k0` are the values and record count at the last
  `observe` or `new`. `B_i = PV_i(base)`, and *healthy* means B = 0.

**Columns.** *Layer(s)* is `property/3`'s layer list. *Evidence* names
the artifact. Its §12 kind follows from the layer: Lean is model-proof, TLC
and MC-1 model-check, replays and tests test, Prolog C-* and the wasm
surface (SH-11) check, and Kani bounded-proof. *Status* values:
- `proved (model)`: a Lean theorem about the transcription, at every size.
- `model-checked`: TLC or MC-1, within bounds. `tested`: on the real code.
- `checked`: a Prolog consistency check, or SH-11's comparison of the
  built wasm with `wasm-surface.expected`. `bounded proof (Kani)`: a Kani
  proof on the real core for every input within the harnesses' bounds
  (§6), and nothing outside them. `fails: F-n`: false, with a reproducer.
  No row is verified (§12).

### 5.1 Configuration and numerics

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| CFG-1 | `Pool::new` is Ok iff `validate` is Ok, and the initial state satisfies INV | kani, lean | Kani `h_init`, `h_validate`, `h_init_inv`, `h_init_inv_2` (a composition, §6); Lean `inv_init` (`Valid cfg ⇒ Inv (init cfg now)`; strings not modelled); TLC TraceCheck on the configs the core accepted | bounded proof (Kani, a composition); proved (model) without the string checks |
| CFG-2 | `validate` ⇒ references in range, vectors of length n, prerequisites strictly earlier and distinct, values bounded | kani, lean | Kani `h_validate` (raw configurations, §6); Lean takes these checks as the definition `Valid`; no theorem about the Rust | bounded proof (Kani) |
| NUM-1 | Valid config and bounded values ⇒ `energy_terms` and `energy` are Ok and exact | kani, lean | Kani `h_energy` (any value in ±1,000,000), `h_energy_exact`, `h_energy_max` (64 terms, 2.56·10^17 exact); Lean computes exactly in `Int` and does not model overflow; TLC cannot represent large energies (§17.5) | bounded proof (Kani) |
| NUM-2 | `add` fails closed exactly when the exact result leaves ±1,000,000 | kani, lean | Kani `h_step_submit_tx`, `h_step_cancel_tx`, `h_step_settle_tx` (every `Arithmetic` exit of `add`, values at both extremes); Trace 206: `arithmetic` from `add` at 999,990 + 15 and from the envelope at 1,000,005; TLA+ mutants 23 and 24 | bounded proof (Kani); boundary tested |
| ROB-1 | No core panic from any INV state, for any arguments | kani | Kani: every harness that calls the core (panic, overflow, bounds and unwinding checks); Lean shows every index the guards read is in range (INV-WF), but does not model panics | bounded proof (Kani) |

### 5.2 Transition contracts

Each contract gives the exact result (the first failing guard, in the
code's order), the exact post-state, and the frame.

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| TX-0 | Every `Err` leaves the Pool unchanged | kani, tla, lean, prolog | Kani `h_step_<op>_tx`, `h_version_max_<op>`, `h_full_*`; Lean `stepProps` (every call, every state); TLC TraceCheck; MC-2 | proved (model); tested on 212 traces; bounded proof (Kani) |
| TX-SUBMIT | `submit`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_submit_tx`, `_post`, `h_full_255`, `h_full_256`; REF-5, REF-5L, MC-2 on every replayed submit; TLC `StepProperty` (time, capacity and unit guards, effect); C-2 guard order | tested on 212 traces; model-checked in part; bounded proof (Kani) |
| TX-DISPATCH | `dispatch`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_dispatch_tx`, `_post`; REF-5, REF-5L, MC-2; TLC `StepProperty`; C-2 | tested on 212 traces; model-checked in part; bounded proof (Kani) |
| TX-ACK | `acknowledge`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_ack_tx`, `_post`; REF-5, REF-5L, MC-2; C-2, C-3 | tested on 212 traces; bounded proof (Kani) |
| TX-CANCEL | `cancel`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_cancel_tx`, `_post`; REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; bounded proof (Kani) |
| TX-SETTLE | `settle`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_settle_tx`, `_post`; REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; bounded proof (Kani) |
| TX-PAUSE | `set_paused`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_pause_tx`, `_post`; REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; bounded proof (Kani) |
| TX-OBSERVE | `observe`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | Kani `h_step_observe_tx`, `_post`; REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; bounded proof (Kani) |
| TX-NOOP | Idempotent Ok paths change nothing, version included | kani, tla, lean, prolog | Kani `h_step_<op>_tx`, `h_version_max_<op>`; Lean `stepProps`; TLC TraceCheck; MC-2 | proved (model); tested; bounded proof (Kani) |
| TX-VER | Every other Ok increments the version by exactly 1 | kani, tla, lean, prolog | Kani `h_step_<op>_tx`, `h_version_max_<op>` (F-5); Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |

### 5.3 Step properties

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| AUTH-1 | Effective submit and dispatch ⇒ caller = actor; cancel ⇒ actor or owner; settle ⇒ executor; pause and observe ⇒ owner | kani, tla, lean, prolog | Kani `h_step_<op>_tx`; Lean `exec_auth` (every Ok, no-ops included); TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani). F-4: actor = executor is accepted |
| STALE-1 | Submit Ok ⇒ request version = version; versions never repeat, so an accepted request cannot replay | kani, tla, lean, prolog | Kani `h_step_submit_tx`, `h_bmc_from_init_s_submit` (no replay along 2-operation traces); Lean `stale1_no_replay`, `version_mono_run`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| ADM-1 | Submit Ok ⇒ energy(post) ≤ energy(pre) | kani, tla, lean, prolog | Kani `h_step_submit_tx`; Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| ADM-2 | Submit Ok in a violating state ⇒ energy(post + completion) < energy(pre) | kani, tla, lean, prolog | Kani `h_step_submit_tx`; Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| HARD-STEP | Every Ok except observe: PV_i(post) ≤ PV_i(pre) for every metric | kani, tla, lean, prolog | Kani `h_step_<op>_post`; Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| DEP-1 | Submit Ok ⇒ prerequisites met by Completed units | kani, tla, lean, prolog | Kani `h_step_submit_tx`; Lean `dep1`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| LIFE-1 | Status graph Reserved → Dispatched or Cancelled, Dispatched → Active or Unknown, Unknown → Active, in flight → Completed or Cancelled; terminals absorbing; append-only; id, recipe, units and expiry immutable | kani, tla, lean, prolog | Kani `h_step_<op>_post`; Lean `stepProps`; TLC `StepProperty`; C-3; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| ASYNC-1 | Acknowledge never changes values; Active and Unknown keep the reservation | kani, tla, lean, prolog | Kani `h_step_<op>_post`; Lean `stepProps`; TLC `StepProperty`; MC-2; RT-CALLBACK | proved (model); model-checked; tested; bounded proof (Kani) |
| TERM-1 | The same terminal repeated is an Ok no-op; the opposite terminal is `InvalidState` (settle; cancel of a Completed record gives `Pending`, §4.3) | kani, tla, lean, prolog | Kani `h_step_<op>_post`; Lean `term1`, `term1_cancel`; TLC invariant (error view); MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| OBS-1 | Observe Ok ⇒ no open record, config unchanged | kani, tla, lean, prolog | Kani `h_step_observe_tx`; Lean `obs1`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |
| PAUSE-1 | Paused ⇒ submit and dispatch have no effect; settle, ack, cancel and observe are unaffected | kani, tla, lean, prolog | Kani `h_step_<op>_tx`, `_post`; Lean `pause1_blocks`, `pause1_transparent`; TLC `StepProperty` and the `WitStep_Paused*` witnesses; MC-2 | proved (model); model-checked; tested; bounded proof (Kani) |

### 5.4 Invariants

These hold in every reachable state. Lean proves their conjunction `Inv`
with `inv_init`, `inv_step` and `reach_inv`.

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| INV-WF | Values have length n and are bounded; `records[j].id = j`; recipe in range; 1 ≤ units ≤ max_units; at most 256 records; config never changes | tla, lean, kani, prolog | Lean `reach_inv`; TLC MC_Safety and every trace state; MC-1, MC-2; Kani induction: `h_init_inv*`, `h_step_<op>_inv`, `_inv_0`, `_inv_1`, `_inv_3` | proved (model); model-checked; tested; bounded proof (Kani, at most 3 records) |
| INV-LEDGER | values = base + Σ reservations of records since k0 not Cancelled + Σ completions of Completed records since k0 | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-1, MC-2; Kani induction: `h_init_inv*`, `h_step_<op>_inv`, `_inv_0`, `_inv_1`, `_inv_3` | proved (model); model-checked; tested; bounded proof (Kani, at most 3 records) |
| INV-HARD | The envelope over the open records is computable and EV_i ≤ B_i | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-1, MC-2; Kani induction: `h_init_inv*`, `h_step_<op>_inv`, `_inv_0`, `_inv_1`, `_inv_3` | proved (model); model-checked; tested; bounded proof (Kani, at most 3 records) |
| INV-HEALTHY | B = 0 ⇒ every subset of open completions lands in bounds | tla, lean, kani, prolog | Lean `healthy`; TLC; MC-1, MC-2; Kani induction: `h_init_inv*`, `h_step_<op>_inv`, `_inv_0`, `_inv_1`, `_inv_3` | proved (model); model-checked; tested; bounded proof (Kani, at most 3 records) |
| INV-DEP | Every record's prerequisites are met by Completed records of lower index | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-1, MC-2; Kani induction: `h_init_inv*`, `h_step_<op>_inv`, `_inv_0`, `_inv_1`, `_inv_3` | proved (model); model-checked; tested; bounded proof (Kani, at most 3 records) |
| INV-VER | The version equals the number of effective transitions | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-2 per edge; Kani `h_bmc_from_init_*` (2-operation traces from `Pool::new`) | proved (model); model-checked; tested; bounded proof (Kani, 2-operation traces) |

### 5.5 Reads

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| RD-PREVIEW | `preview.allowed` ⇔ `candidate` Ok; allowed and version < u32::MAX ⇒ submit Ok; no mutation, no panic | kani, near-tests, prolog | Kani `h_preview`, `h_preview_post`; Prolog `test_reads` (COV-2): the real core's `preview` (allowed, reason, candidate, energies) on 36,797 requests at 1,246 trace states (`reads.txt`) equals the model's; the generator checks that `submit` agrees with each of those previews on the real core; Prolog `preview_allowed` over a request grid (model); near-tests: the shell's `preview` equals the core's after every SH-8 host call (the shell half) | bounded proof (Kani, core half); tested (shell half; core half also by differential against the model) |
| RD-BEST | `best_quantity` is sound and minimal as documented | kani, prolog | Kani `h_best` with `h_preview`, `h_step_submit_*` and `h_energy` (a composition, §6); Prolog `test_reads` (COV-2): the real core's `best_quantity` on the same 36,797 requests equals the model's `best_quantity/4`; Prolog `best_quantity` against brute force on small cases (model) | bounded proof (Kani, a composition); tested by differential against the model |

### 5.6 Liveness

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| LIVE-1 | INV, B = 0 and version < u32::MAX ⇒ `settle(executor, id, true)` is Ok for every Dispatched, Active or Unknown record | lean, tla, prolog | Lean `live1` at every size; canary `Live1NoPremise.lean` fails to compile; TLC invariant in MC_Safety; Prolog on every trace state; Kani `h_live1` (3 records) | proved (model); model-checked; tested; bounded proof (Kani, 3 records) |
| LIVE-2 | Every dispatched record eventually becomes terminal under executor fairness | tla, prolog | TLA-LIVE-F1 and TLA-LIVE-F2 violated; TLA-LIVE-1 holds on the completion path; MC-1 (dead records in `wedge`, release-blocked in `reliance`, none in `healthy`); traces 0 (F-1) and 209 (F-2) on the real core; RT-WEDGE; Kani `h_wedge` reaches F-1 from `Pool::new` | fails: F-1, F-2 |

### 5.7 Contract shell

Mocked runtime (`near-tests/`), on the host and on two wasm builds.
SH-11 is the surface check of both builds (`near-tests/wasm-surface.sh`).

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| SH-1 | caller = predecessor; now = block time in whole seconds | near-tests | `sh1_caller_is_the_predecessor_not_the_signer`, `sh1_now_is_the_block_timestamp_in_whole_seconds`; 15% relayed calls in SH-8; mutants m02, m10 | tested |
| SH-2 | `new` is private and initializes once | near-tests | `sh2_new_is_private_and_initialises_once`; mutant m09 | tested |
| SH-3 | `on_result` is private, and maps the status string as documented | near-tests | `sh3_on_result_is_private`, `sh3_on_result_maps_the_status_string`; mutants m01, m03, m04, m08, m14 | tested; NT-F4 |
| SH-4 | `submit` = core `preview` then `submit`; a rejected submit writes nothing | near-tests | `sh4_rejected_submit_returns_the_decision_and_writes_nothing` (15 rejection cases, `Full` and `Arithmetic` included); mutant m13 | tested |
| SH-5 | A core `Err` panics with exactly the error string and changes nothing | near-tests | `sh5_core_errors_are_panics_with_the_error_string`; SH-8 | fails on the documented build: NT-F1; tested on `--cfg near` |
| SH-6 | `dispatch` promise shape: `execute{id,recipe,units}` to the executor, 30 Tgas, then `on_result` | near-tests | `sh6_dispatch_promise_shape`; mutant m11 | tested |
| SH-7 | `reconcile` guard and promise shape: `status{id}` 10 Tgas, then `on_result`, by anyone, no state write | near-tests | `sh7_reconcile_guard_and_promise_shape`; mutants m05, m15 | tested |
| SH-8 | Borsh state round trip: the shell equals the core, with a reload before every call | near-tests | `sh8_store_diff_host` (80,000 calls), `sh8_store_diff_wasm` (12,000 calls per build), `conformance_traces_through_the_shell` (8,804 calls × 3 paths) | tested |
| SH-9 | Views: `get_pool`, `get_commitments` pages of at most 50 | near-tests | `sh9_views_and_paging_at_256_records`; mutant m06 | tested |
| SH-10 | Nonpayable methods reject deposits | near-tests | `sh10_mutating_methods_reject_attached_deposits`; mutant m12 | tested; NT-F2 (`reconcile` keeps deposits) |
| SH-11 | Export surface, both builds: `pool_contract` exports exactly the 12 documented methods plus `contract_source_metadata` and `memory`, and `pool_executor` its 7 methods plus the same two; no upgrade, migrate or reset export | near-tests | `wasm-surface.sh` SURF-1 against `wasm-surface.expected` (`run.sh surface`) | checked; NT-F3 (the imports do not exclude transfer, deploy or add-key actions: source review only) |

### 5.8 Executor

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| EX-1 | Only the lock executes | near-tests | `ex1_only_the_lock_executes`, `ex1_executor_wrappers`; mutant m17 | tested |
| EX-2 | Payload binding and dedupe: a replay returns the recorded status; another payload fails | near-tests | `ex2_payload_binding_and_dedupe`; mutants m16, m21 | tested |
| EX-3 | Only the operator finishes, confirms or sets the mode | near-tests | `ex3_only_the_operator_attests`; mutant m18 | tested |
| EX-4 | A conflicting terminal outcome is rejected | near-tests | `ex4_terminal_conflict_rejected`; mutant m19 | tested |
| EX-5 | Notify calls `lock.settle{id,completed}`, 40 Tgas | near-tests | `ex5_notify_calls_lock_settle`, end-to-end flows; mutant m20 | tested |

### 5.9 Runtime (sandbox, real wasm)

Every row ran on both builds (§9.2).

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| RT-PRED | Calls through a relay are attributed to the relay | sandbox | `rt_pred_relay_is_the_caller` | tested |
| RT-PRIVATE | `new` and `on_result` reject foreign callers | sandbox | `rt_private_new_and_on_result` | tested |
| RT-CALLBACK | `execute` panic → Unknown; "cancelled" → Cancelled and released; "active" → Active | sandbox | `rt_callback_status_mapping` | tested |
| RT-REVERT | A core error leaves storage byte-identical and emits nothing | sandbox | `rt_revert_core_errors_write_nothing` | tested |
| RT-RACE | Settle before the execute callback; the late ack is ignored | sandbox | `rt_race_settle_before_callback`, `rt_race_executor_key_settles_while_callback_in_flight`, `rt_race_operator_finish_vs_callback` | tested on one shard; the operator's `finish` cannot overtake the callback there |
| RT-WEDGE | F-1 end to end | sandbox | `rt_wedge_f1_end_to_end` | F-1 reproduced (witness) |
| RES-1 | Gas at the maximum-size state stays under 300 Tgas | sandbox | `res_1_gas_at_max_state`, `res_1_min_prepaid_gas_and_executor_cap` | tested: worst pool receipt 12.56 Tgas; least prepaid gas that succeeds: `dispatch` 70, `reconcile` 46, the executor's `finish` 43 Tgas; executor measured at its 256-job cap |

### 5.10 Requirement checks and Prolog model checks

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| C-1 | Authority matrix: docs = shell attributes and caller sources = core caller checks | prolog | 12 methods, 12 shell methods, 6 core caller checks, 14 shell → core calls | checked |
| C-2 | Guard order: docs = code = TLA+ `GuardOrder` | prolog | 8 op kinds, 56 guards (31 doc, 19 doc_condition, 6 code_only) | checked |
| C-3 | Lifecycle: docs = code = TLA+ `Edges` = the traces | prolog | 36 rows, 11 edges, all 36 rows observed in the traces | checked; one divergence (`div-ack-noop-version`) |
| C-4 | Constants: docs = code | prolog | 8 compared, 4 derived | checked |
| C-5 | Fixture conservation (STOCK, CASH, RISK, self-authorization) | prolog | 23 claims on trace configs 1-5; a two-record release search per fixture | checked; F-2 and F-4 reproduced |
| C-6 | Traceability: `traceability.pl` = this section (IDs and layer lists); requirements, threats and findings traced | prolog | `verification/consistency.pl` reads the first cell and the *Layer(s)* cell of every table row of §5 from this file. Requirements suite, 2026-11-12: 97 IDs, 97 rows, 97 equal layer lists | checked |
| MC-1 | Small model check of `step/4` | prolog | `wedge` 3,740 states, `healthy` 3,856, `reliance` 630; all complete | model-checked |
| MC-2 | Replay of every trace through `step/4` | prolog | 212 traces, 8,804 calls, 0 divergences | tested |

### 5.11 TLA+

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| TLA-SAFE | `InvMC` and `StepProperty` in every reachable state and step of MC_Safety | tla | 2,306,738 distinct states, depth 15 | model-checked |
| TLA-IND | `Inv` is inductive (Apalache) | tla | not done: Apalache 0.47.2 rejects the model's recursive sums | open |
| TLA-LIVE-1 | LIVE-2 on the completion path: observes in bounds, executor weakly fair to completing | tla | `MC_Liveness` (17,964 states), `MC_Liveness_F2Done` (17,553); `MC_Liveness_Unfair` must fail and does | model-checked |
| TLA-LIVE-F1 | F-1 as a LIVE-2 counterexample (must be violated) | tla | `MC_Liveness_F1` violated; `MC_Liveness_F1Shape` holds (18,284 states) | violated, as required (F-1) |
| TLA-LIVE-F2 | F-2 as a LIVE-2 counterexample: healthy observations, a fair honest executor (must be violated) | tla | `MC_Liveness_F2` violated; `MC_Liveness_F2Shape` holds (17,553 states) | violated, as required (F-2) |
| TLA-WIT | Completed, prerequisite, disturbed and wedge states, and seven step shapes, are reachable | tla | 4 state and 7 step witnesses | each violated, as required |
| REF-5 | The TLA+ model accepts every real-core trace | tla | TraceCheck, 9,016 of 9,016 states | tested |

### 5.12 Lean

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| LEAN-IND | `Inv` holds initially and after every call | lean | `inv_init`, `inv_step`, `reach_inv` | proved (model) |
| LEAN-STEP | Every call from every state satisfies the step properties | lean | `stepProps`, `stepProps_step`, `exec_auth`, `term1`, `term1_cancel`, `stale1_no_replay`, `version_mono_run` | proved (model) |
| LEAN-LIVE1 | LIVE-1 at every size | lean | `live1`, `live1_exec`, `live1_reach` | proved (model) |
| LEAN-WIT | F-1 witness, permanent for every continuation, and healthy-side non-vacuity | lean | `Witness.lean`, `f1_forever` | proved (model) |
| REF-5L | The Lean machine agrees with the real core on every trace | lean | `pool-lean replay`: 212 traces, 8,804 calls (2,547 Ok), every result and post-state equal | tested |
| LEAN-GUARD | Each call's guard list is the code's order | lean | `Guard.guards_order`, `Guard.outcome_mem`; compared with TLA+ `GuardOrder` by hand | proved (model) |

### 5.13 Kani refinement links

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| REF-1 | Guard exactness: the core's error is the TLA+ error operator's, so Ok exactly when the action is enabled | kani | Kani `h_ref_<op>` (7) against `tla.rs`, a hand transcription of `SharedPool.tla`; 46 `ref` covers; plain mode on the 212 traces (8,804 calls); mutant 31 (§17.2) | bounded proof (Kani, step bounds) |
| REF-2 | Effect exactness: on Ok, the abstraction of the post-state is the TLA+ action's post-state | kani | Kani `h_ref_<op>` (7), as REF-1 | bounded proof (Kani, step bounds) |
| REF-3 | Rejected and idempotent calls stutter in the model | kani | Kani `h_ref_<op>` (7), as REF-1 | bounded proof (Kani, step bounds) |

### 5.14 Assumptions

The levels are those of `threat_model.pl`: high, med, low, or policy.

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| ASM-PRED | The predecessor cannot be forged | assumption | RT-PRED (relay attribution on near-sandbox), SH-1 | trusted (high); tested |
| ASM-PRIVATE | `#[private]` ⇔ predecessor = current account | assumption | RT-PRIVATE, SH-2, SH-3 | trusted (high); tested |
| ASM-CALLBACK | The callback sees the executor's return or `PromiseError` | assumption | RT-CALLBACK, SH-3 | trusted (high); tested |
| ASM-ATOMIC | A panicking receipt writes nothing | assumption | RT-REVERT (storage byte-identical, no event); RES-1 (the same for receipts that run out of prepaid gas) | trusted (high); tested |
| ASM-INTERLEAVE | Receipts can run between `dispatch` and `on_result`; ack and settle are independent model steps | assumption | RT-RACE (one shard) | trusted (med); tested in part |
| ASM-TIME | The block timestamp is monotone | assumption | none; TLA+ and Lean allow any time per call (a superset); MC-1 assumes it | trusted (high); untested |
| ASM-EXEC | The executor is honest: `settle(false)` only on definitive nonexecution | assumption | none; F-2: the honest report is the one that fails | policy |
| ASM-OWNER | Observations are true | assumption | none | policy |
| ASM-DEPLOY | No code replacement; the deployment lock is out of scope | assumption | none; NT-F3: the import surface cannot rule out an escape hatch | policy |
| ASM-TOOLS | Scryer, TLC, Lean, Kani and the extractors are sound for what is used | assumption | canaries, witnesses and mutants in every runner; the Lean axiom audit; Kani: `h_canary` fails as required, 164 covers, 30 mutants killed; two Kani 0.68.0 hazards found and worked around (§6) | trusted (med) |
| ASM-SPEC | The specs, and the Prolog transcription of the docs, mean what we intend | assumption | `[review] spec_reviewer` (empty); the Prolog author had read the code (§8) | open: no reviewer (low) |
| ASM-MODEL | The small scopes are representative: Kani's bounds, TLC's universes and 32-bit integers, MC-1's universes | assumption | Lean at every size (model); traces at 256 records and ±1,000,000; Kani's bounds, stated per harness (§6), with energy over the whole value range | trusted (med) |
| ASM-LEAN-TLA | The Lean and TLA+ models transcribe the code | assumption | REF-1..3 (TLA+, Kani, within the step bounds), REF-5, REF-5L, MC-2, C-2 | trusted (med); tested on 212 traces; bounded proof per step for TLA+ (REF-1..3) |
| ASM-COMPILE | `overflow-checks = true` in the release profile | assumption | `tools/scripts/check-pin.sh` (`release_overflow_checks = true`) | trusted (high); checked |

---

## 6. Kani on the real core

Results, bounds, deviations and run log: `kani/RESULTS.md`. Kani 0.68.0
with CBMC 6.11.0, on the pin (v1.0.0's code). Runs A to N, 2026-11-12 and
2026-11-13, one harness at a time on a shared 10-core, 64 GB macOS arm64
machine. The 36 harnesses and 16 mutants that do not fit CI's hosted
runner were run again at commit `89f99d6`, two at a time, on a 10-core,
64 GB Apple M1 Max. That run is recorded in `kani/local`, and CI checks
the record (§14; `kani/RESULTS.md`, Local record).

**Design.** `projects/shared-pool/kani/` is a standalone crate whose only
dependency is `pool-core` from the mirror, with `default-features = false`.
Kani checks the code that is deployed, not a transcription. `src/spec.rs`
is an executable specification written from the brief, not from the code:
each call's exact result in guard order, its exact post-state and frame,
`envelope`, `energy`, `validate`, and the invariants with their ghost
(`base`, `k0`, effective steps). Harness bodies are dual-mode, as in
near-approval §6.1: symbolic under Kani, which is the proof, and random in
plain `cargo test --release`, which is a test that takes seconds. Each
step harness is four CBMC runs, so that each fits in memory: `_tx` (exact
result, TX-0, TX-NOOP, TX-VER), `_post` (exact post-state and the step
properties), `_inv` (INV preservation) and `_cov` (the covers).
`src/tla.rs` transcribes `tla/SharedPool.tla` for REF-1..3 (§17.2).

**Results.** 89 of 89 harnesses as required: 88 `ok`, and `h_canary`
FAILED on its own assertion only. 164 of 164 covers SATISFIED, each in
some harness of its family; they include every exit of every step and the
findings. Plain mode: 27 of 27 tests. Mutants: 31 (30 of the core, one of
`tla.rs`); the 30 that must be killed fail plain mode and the Kani harness
each names, and mutant 20, which is equivalent, survives both. No property
failed: within the bounds the code agrees with the specification on every
result, post-state and read. Kani found no new defect. `run.sh all` was
not run end to end in one invocation (its Kani part is about 7.5 hours);
each result is the harness's last run on the final sources.

| Group | Harnesses | Shows |
|---|---|---|
| Configuration | `h_validate`, `h_init`, `h_init_inv`, `h_init_inv_2` | CFG-2: `validate` equals the specification on raw configurations. CFG-1, as a composition: `new` is Ok iff `validate` is, and its pool satisfies INV. F-4. |
| Numerics | `h_energy`, `h_energy_exact`, `h_energy_max` | NUM-1: `energy_terms` and `energy` are Ok on bounded values and exact (64 terms: 2.56·10^17) |
| Steps | `h_step_<op>_{tx,post,inv,cov}` (28) | TX-*, NUM-2, ROB-1 and the §5.3 step properties from 2-record states; INV preserved |
| Induction | `h_step_<op>_inv_{0,1,3}` (21) | INV preserved from 0, 1 and 3 records as well |
| Traces | `h_bmc_from_init_po`, `h_bmc_from_init_s_<op>` (8) | Exact post-states along 2-operation traces from `Pool::new`; INV-VER; STALE-1's no-replay |
| Limits | `h_version_max_<op>` (7), `h_full_255`, `h_full_256`, `h_slot_cycle_0`, `h_slot_cycle_2` | TX-VER and TX-NOOP at u32::MAX (F-5); `Full` exactly from 256 records; F-3's submit, cancel, submit cycle |
| Reads | `h_preview`, `h_preview_post`, `h_best` | RD-PREVIEW; RD-BEST as a composition with `h_preview`, `h_step_submit_*` and `h_energy` |
| Liveness, findings | `h_live1`, `h_wedge`, `h_wedge_healthy` | LIVE-1 with up to two other open records; F-1 from `Pool::new`; F-2 from healthy INV states |
| Refinement | `h_ref_<op>` (7) | REF-1..3 (§17.2) |
| Canary | `h_canary` | Asserts that no submit is ever accepted; must FAIL |

**Bounds.** Every result holds for every input within these bounds, and
says nothing outside them.
- **Steps, REF-1..3, `h_preview`, `h_version_max_*`:** 1 metric, 1 term,
  2 recipes (recipe 1 may require recipe 0), and an INV pre-state with
  exactly 2 records in any statuses. Values, bounds and targets anchored
  at −1,000,000, 0 and 1,000,000, each ±4; deltas −3..3; `max_units` 1..3;
  weights 1, 2 or 1,000. Accounts `o_`, `a1`, `x1` and `z_` in every role
  and as every caller. Times, versions, expiries and the paused flag free.
  Arguments the code only compares (recipe, units, ids) narrow.
- **INV:** true initially and preserved from exactly 0, 1, 2 and 3
  records, so INV-WF to INV-DEP hold in every reachable state with at most
  3 records. INV-VER only along 2-operation traces. `h_live1`: 3 records.
- **`h_energy`:** 2 metrics, 2 terms, any value in ±1,000,000, any weight.
  `h_energy_max`: 64 terms, concrete.
- **`h_validate`, `h_init`:** raw configurations of up to 2 metrics, 2
  terms, 3 recipes and 2 requirements per recipe, strings of 0 or 2 bytes,
  each field in range, at an edge or out of range.
- **`h_full_*`:** 255 and 256 Cancelled records.
- **Runner:** flags `--no-memory-safety-checks --no-assertion-reach-checks
  -Z stubbing`, unwinding assertions on; 1,800 s per harness (7,200 s for
  `h_step_*_inv_3`); memory cap 40 GB. Peaks reached 39.0 GB (`h_wedge`),
  and 33 harnesses peaked above 14 GB. The harness times sum to 26,921 s
  (7.5 h). These peaks split the harnesses for CI (§14). CI's `kani` job
  runs the 53 that peaked at 13 GB or less, in 8 groups, on the hosted
  runner. The other 36, in 21 groups, are in the local record, which CI
  checks; they run in CI only on a `KANI_RUNNER` of at least 49 GB.

**Deviations.** `RESULTS.md` lists 26 deviations from the plan. All but
two came from CBMC running out of memory or time. None weakens an
assertion: each narrows the inputs (stated in the bounds), replaces a
library function by a model that can only make a harness fail, rewrites a
specification function into an equal one, or splits a property into
harnesses whose conclusions combine. The main ones are a fixed-capacity
model of `Vec::with_capacity_in` and `Vec::reserve` (1); fixed shapes and
record counts (7); PAUSE-1 for the transparent operations at the
specification level (18); fixed roles for F-1, and INV states for F-2
(19); traces rebuilt with constant shapes after each operation (20);
`h_full_255`'s records as one constant array (21); and a free `validate`
in `h_init` and free `candidate` and `energy` in `h_best`, each pinned
down by other harnesses (23, 24).

**Findings on the real core.** Each core finding has a cover that must be
SATISFIED, but they show different things. F-1: a trace from `Pool::new`
(`h_wedge`). F-4: a configuration that `validate` accepts (`h_validate`).
F-2, F-2b and F-5: from constructed states (`h_wedge_healthy`, the cancel
and settle covers, `h_version_max_*`); Kani does not show that those
states are reachable from `Pool::new`. F-3: one submit, cancel, submit
cycle from `Pool::new` and from quiet 2-record states, and the exact limit
at 255 and 256 records; not the 256 cycles as one trace. F-6: its guards
fire; the scenario as a whole is not reached.

**Tool issues** (Kani 0.68.0). Two soundness hazards were found and worked
around. A static that a harness writes can share storage with a constant
of equal bytes: `h_best`'s stub changed `RawVec`'s zero capacity, and the
harness failed. The models' statics now carry a distinct tag. A scan of
every harness's goto program for named statics read outside their own
functions found no other case. A reference to a field of a local array of structs, at an
index CBMC does not fold, read unconstrained values in the function it
was passed to, and three `h_ref_*` harnesses failed. `tla.rs`'s lookups
now return copies. A third issue is harmless: with `--stop-on-fail`,
Kani's JSON parser panics, so the mutant runs read CBMC's text output.

**What is not shown.** Steps over more metrics, terms or recipes, or from
4 or more records (other than a submit at 255 or 256 Cancelled records);
values strictly between the anchors and the extremes, outside energy; the
reachability of F-2, F-2b, F-3 and F-5 from `Pool::new`; RD-BEST and CFG-1
other than as compositions; LIVE-2 (TLA+'s); REF-1..3 outside the step
bounds, and the agreement of `tla.rs` with the `.tla` other than on the
traces; memory safety of std (the core forbids `unsafe`); the shell, the
executor and NEAR (§9). Plain mode, the traces and Lean at every size
cover parts of this, as tests or for the model.

---

## 7. Verus (deferred)

**Decision: not started.** The Lean layer already proves the model at
every size (§18). Verus would close only the gap between that model and
the code (ASM-LEAN-TLA), which REF-5L and Kani already narrow. Fixing F-1
or F-2 will change the admission or release rules, so a proof of today's
code would be redone.

**Fit,** compared with near-approval's `approval-core`, where Verus path A
worked:
- **Vec-heavy state.** `Pool` holds `Vec<i64>` values and
  `Vec<Commitment>` records. `Config` holds `Vec`s of metrics, terms and
  recipes; each recipe has two `Vec<i64>` effects, a `Vec<(u32, u32)>` of
  prerequisites and three `String`s. Every spec needs a `Seq` view of
  each, with INV-WF's length and bound facts carried through every
  function.
- **Energy arithmetic.** Values are `i64`, units `u32`, and energy a
  `u64` built with `checked_mul` and `checked_add`. One term reaches
  4·10^15, and 64 terms 2.56·10^17 (spec:13). Each checked operation needs
  a nonlinear bound, which is where Z3 is weakest.
- **Loops over metrics and records.** Most of the code is iterator chains
  (`zip`, `map`, `collect`, `try_fold`, `filter`, `sum`, `any`,
  `min_by_key`) and a mutating closure in `envelope`. vstd's iterator specs
  are thin. In near-approval, one `filter_map` chain had to become a loop
  upstream before Verus could take the code (trust-framework PR #20).
- **Strings.** Callers are compared as `String` against `&str`.

**Cost of a twin.** About 18 functions over 492 lines. The iterator chains
become loops with invariants, upstream or in `REWRITES.toml` with a Kani
equivalence harness each. Lemmas for INV-HARD and ADM-2 go over
`Seq<int>`. That is at least near-approval's path A (8-13 days), likely
more for the arithmetic.

**Revisit** after upstream decides on F-1 and F-2 (PR #4, v1.1, proposes
fixes; not verified here), and only if "formally verified" will be
claimed for the code rather than the model.

---

## 8. Prolog

Results: `prolog/RESULTS.md`. Scryer Prolog 0.10.0. The final run
(2026-11-12, 212 traces, with the COV-2 reads) exits 0 in 510.5 s.

| File | Contents |
|---|---|
| `requirements/pool_req.pl` | 65 `requirement/3` facts, one per doc statement used; the api.md method table; `guard/5` (56 rows in the docs' order, each `doc`, `doc_condition` or `code_only`); the lifecycle table; constants; five fixtures with 23 claims; `finding/4` (F-1..F-6); 4 divergences; 8 ambiguities |
| `requirements/threat_model.pl` | 6 adversaries, 22 threats, 14 assumptions (§3) |
| `requirements/traceability.pl` | `property/3`, which is §5; `trace_row/2`, which maps requirements to properties |
| `model/pool_machine.pl` | `step/4`, written from the docs. It walks the guard table in order, so the model's behaviour is the requirement table. 16 places are tagged `CODE-ONLY`. Reads: `admissible/3`, `preview_allowed/3`, `best_quantity/4`. |
| `extract.py` → `extracted/` | Facts from the core and contract `lib.rs`, `fixtures.rs`, `SharedPool.tla` and `Props.tla`. A narrow parser that fails loudly on unknown constructs. `run.sh` fails on a regeneration diff. |
| `verification/`, `tests/`, `mutants/` | C-1..C-6, MC-1, MC-2, the COV-2 reads differential and the property checkers; five suites; 20 model, 2 requirements (r01, r02), 9 code and 2 reads mutants (d01, d02: a mutated core, through a rebuilt generator) |

**Results.**
- **C-1..C-6 pass** (§5.10). C-5 reproduces F-2 and F-4, and fails if
  either stops reproducing (mutants m17, c09). C-6 compares
  `traceability.pl` with §5: requirements mutant r01 drops the TLA-IND
  row, r02 adds `tla` to NUM-2's layers, and only that comparison kills
  them. The requirements suite (15 tests) takes 11.0 s.
- **MC-1** uses monotone time and record caps of 3 (`wedge`) and 2
  (`healthy`, `reliance`), in 34.8 s. `wedge`: 3,740 states, 113,172
  edges, 228 dead states (F-1). `healthy`: 3,856 states, 98,056 edges,
  nothing dead or blocked, 10 error kinds reached. `reliance`: 630 states,
  14,236 edges, 150 release-blocked states with B = 0 (F-2).
- **MC-2** replays 212 traces (8,804 calls) from the code's pre-states,
  with 0 divergences; the whole `test_mc2` suite (19 tests) takes 6.3 s.
  Every op kind returns Ok, and all 15 error kinds the code can return
  from an INV state occur. The invariants, step properties and LIVE-1 hold
  on every core state.
- **Unit tests:** 29 `step/4` tests pass (0.5 s), including the F-1..F-6
  witnesses and the RD checks on the model.
- **Reads differential (COV-2).** `test_reads` rebuilds each of the 1,246
  states of `conformance/traces/reads.txt` and compares the real core's
  `preview` (allowed, reason, candidate, energies) and `best_quantity` on
  36,797 requests with the model: 0 divergences (3 tests, about 36 s).
  1,678 requests are allowed; every error `candidate` can return from these
  states occurs; 5,739 have a best quantity, 1,617 of them after an energy
  tie (taken to the larger units). Mutants m19 (preview ignores paused) and
  m20 (best_quantity ignores the request's version) are killed only by
  this suite. Reads mutant d01 (the core's ties broken to the smaller
  units) gives 1,617 divergences. Reads mutant d02 (the core's `preview`
  allows a `Paused` request) stops the generator: `preview` and `submit`
  disagree. This is testing, not proof.
- **Canaries and mutants.** Each of three suites exits 1 with only its
  canary failing. 33 of 33 mutants are killed (400.5 s summed).

**What it does not show.**
- **Independence (ASM-SPEC).** Unlike near-approval's M4, this layer's
  author had read the code. Doc-backed facts cite their line, and
  code-only facts are labelled, but no independent reviewer has checked
  either.
- **Bounds.** MC-1 has at most 3 records, 2 or 3 times, and fixed
  observation vectors. C-5's release search covers two records from each
  fixture's init state. RD-PREVIEW's core half and RD-BEST are tested by
  a differential against the model on 36,797 recorded requests at 1,246
  trace states (testing, not proof); other states and requests are not
  covered. C-2 skips five kinds of code error site that cannot fire from an
  INV state.
- **Extraction (ASM-TOOLS).** A construct inside `extract.py`'s grammar
  could be misread. Code mutants c01-c09 show it sees their changes.

---

## 9. Shell, runtime and deployment

### 9.1 `near-tests/` (mocked runtime)

Results: `near-tests/RESULTS.md` (2026-11-11). Toolchain 1.98, near-sdk
5.29.1 with `unit-testing`; the mocked runtime is near-vm-runner 0.37.4
`VMLogic`.
- **Host path.** Calls the `#[near]` methods as Rust functions. State is
  read first and written only on success; a panic discards every write.
- **Wasm path.** Runs the real wasm in wasmi 2.0, with every `env` import
  forwarded to the same `VMLogic`. This covers what near-sdk generates only
  for wasm32: init-once, `#[private]`, deposit checks, JSON and
  `#[callback_result]`. Two builds: `Plain` (exactly `scripts/build.sh`)
  and `Near` (`RUSTFLAGS="--cfg near"`). Forbidden host calls trap. A
  receipt router runs the pool and executor wasm side by side.
- **Oracle.** `pool_core::Pool` and `docs/api.md`, never the contract.

| File | Tests | Covers |
|---|---|---|
| `tests/shell.rs` | 14 | SH-1..SH-7, SH-9, SH-10, NT-F1, NT-F2, NT-F4 |
| `tests/store_diff.rs` | 2 | SH-8: 2,000 × 40 host calls, 300 × 40 per wasm build, 46 required outcomes |
| `tests/traces.rs` | 1 | all 212 traces (8,804 calls) on the host and both builds |
| `tests/executor.rs` | 8 | EX-1..EX-5, end to end through the router |
| `tests/wedge.rs` | 3 | F-1 through the shell; a control without the observe; F-1 with the executor |
| `tests/lockfile.rs` | 1 | 280 packages resolve exactly as in the mirror |

All 29 tests pass in about 30 s. `run.sh test` and `run.sh all` first run
`check-tags.py` (stdlib Python, under a second), which fails the run
unless every test has its own PROP tag line, every tag is a `property/3`
ID, and each near-tests property is tagged on a test that checks it (SH-11
on the surface check SURF-1). Each of the 21 mutants (15 contract, 6
executor) is applied to a copy of the source, and both builds are rebuilt.
All 21 are killed (9 min).

**Wasm surface.** `near-tests/wasm-surface.sh` compares both builds with
`wasm-surface.expected`. SURF-1 (exports, and each import classed as
promise, forbidden or other) passes; it is SH-11's check. SURF-2 fails as
expected, with exactly the recorded forbidden imports (NT-F3).
`pool_contract` exports the 12 methods, `contract_source_metadata` and
`memory`. Only the `--cfg near` build imports `panic_utf8` (NT-F1).

### 9.2 Sandbox (real wasm, local chain)

Results: `sandbox/RESULTS.md`. near-sandbox 2.13.4 through
near-workspaces 0.23.0, the versions upstream `crates/sandbox` pins. Every
test keeps a host `pool_core::Pool` in step with the chain and compares the
whole `get_pool` state after each step. 342 shared registry packages match
the mirror. Built with rustc 1.98.1, `cargo build --target
wasm32-unknown-unknown --release --locked`; a rebuild gives the same hashes:

| Variant | Wasm | sha256 | Bytes |
|---|---|---|---|
| upstream | pool_contract | `8ddc9280c63157636fede6f201ebff30ef528307092ad21914730c00df380f7c` | 393744 |
| upstream | pool_executor | `ca76c3caf0505ab7fdb43ab3ecaef6234472eec94bb4256679e69c5a4785b0e5` | 237589 |
| cfg-near | pool_contract | `af617a8f00a10d0a049fb8092ae2f22463204faf71cf770a1b166d2c5b903c02` | 389435 |
| cfg-near | pool_executor | `760618725144241959be7c0b7a432c413d16b156a0a4aec7c875940c65b74cc6` | 233200 |

- **Variants.** RT-* pass on both; they differ only in the failure text
  (SB-1).
- **RT-RACE.** On one shard, a `settle` from inside `execute` always lands
  before the callback, and the late ack is a no-op (version +2, not +3).
  The operator's `finish` cannot overtake the callback there: a gap.
- **RES-1.** The largest state, built with real transactions: 32 metrics,
  64 terms, 32 recipes with full prerequisites, 256 records. `STATE` is
  45,613 bytes of Borsh, `storage_usage` 439,584 bytes, and `get_pool`
  53,221 bytes of JSON. The worst pool receipt is submit #256 at 12.56
  Tgas (margin 287.4); each record adds about 0.023 Tgas.
- **RES-1, prepaid gas.** At that state, the least whole-Tgas prepaid gas
  that succeeds is 70 Tgas for `dispatch` (executor at 31 jobs), 46 for
  `reconcile` (34 jobs) and 43 for the executor's `finish` (at 256 jobs).
  Every amount from 40 Tgas up to one below each minimum fails with
  "Exceeded the prepaid gas." and changes nothing: both contracts' raw
  storage byte-identical, no event,
  the record's status kept. A 300 Tgas `dispatch` then succeeds. 70 Tgas
  leaves under 1 Tgas spare.
- **RES-1, executor cap.** All 256 records were dispatched through the
  pool, so the executor holds 256 jobs. `execute` #256 burns 2.52 Tgas of
  30, `status` 1.77 of 10, `finish` of the last job 2.87; at the cap a new
  job fails "full".
- `run.sh` took 438 s with warm caches, before the second RES-1 test. That
  test adds about 4.5 minutes per variant (RESULTS.md, Run times).
- **Not shown:** multiple shards and congestion; other protocol versions'
  gas; that RES-1's state is the worst case, for gas or for the minimum
  prepaid gas; storage staking; any live deployment. Only `dispatch`,
  `reconcile` and `finish` were run with less than 300 Tgas, in whole
  Tgas.

### 9.3 Deployment

Out of scope: no deployment of this pin exists. If one is made, follow
near-approval §5.10 (code hash, lock at deploy, owner as a multisig), fund
the pool and executor accounts above their storage stake (the executor's
`finish` grows its state by 3 bytes per job), and build with cargo-near or
`--cfg near` (NT-F1). The import surface does not rule out code
replacement (NT-F3).

---

## 10. Correspondence

### 10.1 The conformance traces

`conformance/` is a standalone crate over the pinned `pool-core`.
`cargo run --release -- --out traces/core.txt` writes the traces, and
`--check traces/core.txt` regenerates them and fails on any difference.
`--reads-out` and `--reads-check` do the same for `traces/reads.txt`.
The format is Prolog terms, documented at the top of `src/main.rs`, with
accounts `o`, `a1`, `a2`, `x1`, `x2` and `z`.

`traces/core.txt` (sha256 `05c0deb4…377818`) holds 212 traces of 8,804
calls, 2,547 of them Ok (no-ops included):

| Traces | Content |
|---|---|
| 0 | the F-1 wedge |
| 1-5 | the five upstream fixtures: each scenario, then 40 random calls |
| 6-205 | random configs (1-3 metrics, 1-3 recipes), 40 calls each |
| 206 | `arith`: `Arithmetic` at the 10^6 bound; the expiry horizon edges |
| 207 | `full`: 256 records, then `Full` (F-3) |
| 208 | `release-arith`: the release `Arithmetic` of F-2b |
| 209 | `f2-risk`: F-2's `Bounds` form in the supplied `risk` fixture |
| 210 | `f4-self`: F-4, actor = executor and owner = executor |
| 211 | `f6-stale`: F-6, `SnapshotExpired` while `observe` is `Pending` |

The traces come from the real core, so a disagreement is either a model
bug or a finding in the code. Every replay compares each result and the
whole post-state.

`traces/reads.txt` (COV-2, sha256 `5545add5…59325ef`, 2.9 MB) holds the
real core's two reads at 1,246 states of those traces: every state of
traces 0-5 and 206-211 (but `full`, 207), every 10th state of the others,
and each final state; a state equal to the one read just before it, at the
same time, is skipped. Each state has 18-61 requests (36,797 in all): every
recipe's actor with units 0, 1, 2, max_units, max_units + 1, 100, 101 and
10^6; a recipe index past the end; for one recipe, every account as
caller, version + 1 and (above 0) version − 1, expiry at now − 1, now,
now + 86,400 and now + 86,401, and with a max age, now at the freshness
edge and 1 s past it. Each line records `preview`
(allowed, reason, candidate, before, after) and `best_quantity`. The
generator fails if a read class is never reached (every `candidate`
error, both Energy and both Arithmetic exits, a tie, a best below the
largest allowed units) or if `submit` on a copy of the pool disagrees with
a `preview`. Prolog `test_reads` compares every line with the model (§8).

| Replayer | ID | Result |
|---|---|---|
| TLA+ `TraceCheck` (`trace2tla.py`) | REF-5 | 9,016 of 9,016 states; `Inv` and `StepProperty` on every core state and step |
| Lean `pool-lean replay` | REF-5L | 212 traces equal |
| Prolog `step/4` | MC-2 | 0 divergences |
| Shell: host and both wasm builds | SH-8 (`traces.rs`) | every result and post-state equal |

**Coverage.** The `op:result` counts over all 8,804 calls, from
`tla/RESULTS.md` (`noop` means Ok with the state unchanged):

| Op | Results |
|---|---|
| submit | ok 588, bounds 823, paused 377, unauthorized 218, prerequisite 149, stale 142, expired 117, energy 110, invalid_recipe 99, invalid_units 87, snapshot_expired 60, arithmetic 2, full 2 |
| dispatch | not_found 896, invalid_state 231, ok 151, paused 74, unauthorized 65, expired 44, snapshot_expired 5 |
| ack | not_found 572, noop 338, ok 72 |
| cancel | not_found 346, ok 338, pending 83, noop 48, unauthorized 43, bounds 3, arithmetic 2 |
| settle | not_found 994, invalid_state 373, ok 115, noop 108, unauthorized 75, bounds 3, arithmetic 1 |
| pause | ok 398, unauthorized 51 |
| observe | ok 391, pending 135, bounds 24, unauthorized 51 |

### 10.2 What the traces do not establish

- **Equivalence.** 8,804 equal calls are evidence that the models
  transcribe the code, not a proof (ASM-LEAN-TLA). REF-1..3 (Kani, §17.2)
  add a bounded proof per step for TLA+, within the step bounds; Lean and
  Prolog have only the traces.
- **Exits no trace reaches:** the version-overflow bump (the highest state
  version is 513); `settle(true)`'s add and envelope `Arithmetic`;
  submit's recovery add; release's envelope `Arithmetic`. Kani's `_tx`
  parts assert the exact result of every exit, these included, within the
  step bounds (§6).
- **Not told apart:** exits of one kind (submit's two `Energy` exits).
  Of the core findings only F-5 has no trace (the version-overflow bump
  above).
- **Small random configs:** bounds within [−5, 10] and effects within ±3.

### 10.3 The chain and staleness

| Link | Checked by |
|---|---|
| docs ↔ code facts | C-1..C-4 (`extract.py`) |
| docs ↔ TLA+ guard order and edges | C-2, C-3 |
| brief ↔ real core | Kani: `spec.rs`, written from the brief, equals the core within the bounds (§6) |
| Prolog `step/4`, TLA+, Lean ↔ real core | MC-2, REF-5, REF-5L (traces); REF-1..3 for TLA+ (Kani, within the step bounds) |
| Prolog reads ↔ real core `preview`, `best_quantity` | COV-2 (`reads.txt`, `test_reads`) |
| Lean guard lists ↔ TLA+ `GuardOrder` | LEAN-GUARD, compared by hand |
| real core ↔ shell (host, both wasm builds) | SH-8 |
| wasm ↔ NEAR runtime | sandbox RT-*, with the host core as oracle |
| deployed code ↔ pin | none (out of scope) |

**Staleness.** `check-pin.sh shared-pool` checks the gitlink, recomputes
the 16 `[source_hashes]`, and requires `overflow-checks = true`. The
`conformance` job runs `--check`; `extract.py` and both lockfile checks
fail on drift. On a pin bump, a changed `crates/core/src/lib.rs`
invalidates every core property, the traces and all three models. A
changed `crates/contract/src/lib.rs` or `Cargo.lock` invalidates SH, EX, RT
and RES. Changed docs invalidate the Prolog requirements.

---

## 11. Layout

```text
formalver/
├── Cargo.toml          # exclude += shared-pool/{source-mirror,kani,conformance,near-tests,sandbox}
├── .gitmodules         # + projects/shared-pool/source-mirror
├── .github/workflows/shared-pool.yml     # §14
├── tools/scripts/      # check-pin.sh, check-status.sh (shared with near-approval); check-kani-record.py (§14)
└── projects/shared-pool/
    ├── strategy.md  status.toml  wasm-surface.expected
    ├── source-mirror/                   # submodule → shared-pool-controls @ pinned_commit
    ├── conformance/{src,traces}/        # generator; traces/core.txt checked in
    ├── kani/{src,mutants}/              # §6; run.sh, RESULTS.md
    ├── kani/local/                      # §14; the local record of the 36 large harnesses and 16 mutants, run-local.py, record.py
    ├── tla/                             # §17; *.tla, *.cfg, mutants/, run.sh, trace2tla.py
    ├── lean/{PoolLean,canary,mutants}/  # §18; run.sh
    ├── prolog/{requirements,model,verification,extracted,tests,mutants}/  # §8
    ├── near-tests/{src,tests,mutants}/  # §9.1; run.sh, run-mutants.sh, wasm-surface.sh, check-tags.py
    └── sandbox/                         # §9.2; run.sh
```

Each layer has a `RESULTS.md` and a `run.sh`. `run.sh` exits 0 only when
every check passes, vacuity guards included.

---

## 12. `status.toml` conventions

near-approval §12 applies unchanged (status values, keys, evidence per
layer, ceilings, tables), enforced by `check-status.sh shared-pool`.
Specific to this project:

| Topic | Convention |
|---|---|
| `release_overflow_checks = true` | In `[project]`. `check-pin.sh` fails unless upstream keeps `overflow-checks = true` (ASM-COMPILE). |
| Pin and version | `pinned_commit` is PR #1's head, on upstream `main` since PR #1 merged. The `pinned_commit` comment names the verified version, v1.0.0 (`6f61616`), whose `crates/core/src/lib.rs`, `crates/contract` and `crates/executor` are byte-identical to the pin (§13). `[project]` records it as data: `verified_release = "v1.0.0"`, `verified_release_commit` (the full SHA of `6f61616`) and `identical_paths` (the three paths). `check-pin.sh` fetches that commit and fails unless each path is the same git tree or blob, mode included, at both commits (§14). |
| Properties | The 83 non-ASM rows of §5, under `[modules.<m>.properties]`, one module per §5 subsection: `config_numerics` (§5.1), `transitions` (§5.2), `step_properties` (§5.3), `invariants` (§5.4), `reads` (§5.5), `liveness` (§5.6), `contract_shell` (§5.7), `executor` (§5.8), `runtime` (§5.9), `requirements` (§5.10), `tla_model` (§5.11), `lean_model` (§5.12) and `kani_refinement` (§5.13). IDs equal `traceability.pl`'s. `layer` is the first layer of the row's *Layer(s)* cell. `cross` holds the row's other layers, plus any other layer whose files carry the ID's `PROP:` tag. |
| Kani rows | Every property with `layer = "kani"` carries the Kani result (§6): `in-progress` (no spec reviewer, and Kani's ceiling is `verified-with-assumptions`), `bounded-proof` evidence, the harnesses first in `harness`, the bounds in `kani_bound`, and in `kani_run` where each of its Kani harnesses is checked now: "CI kani job" (the 53 that fit the hosted runner, rerun whenever a change reaches the Kani layer) or "local record" (the 36 that peaked above 13 GB, run at `89f99d6` and recorded in `kani/local`; CI checks the record, §14). The other layers' results stay in `cross` and `harness`. What Kani does not show is not claimed for it: LIVE-2, and the reachability of F-2, F-2b, F-3 and F-5 from `Pool::new`. The §5.4 invariants list `tla` first, so TLC is their primary layer; their Kani induction is in `harness`, `kani_bound` and `kani_run`, as is LIVE-1's `h_live1`. |
| Layer names | `near-tests/` carries `unit` (`shell.rs`, `executor.rs`, `wedge.rs`) and `difftest` (`store_diff.rs`, `traces.rs`). The surface check is `wasm-check`. The conformance generator is not a layer: each replay is recorded under the layer that runs it (REF-5 `tla`, REF-5L `lean`, MC-2 `prolog`, SH-8 `difftest`). REF-5 is `model-check`, a TLC run. REF-5L is a replay, test-class evidence (§5.12 says tested), recorded as `model-check` because `lean` allows no `test`; its `harness` says so. |
| False properties | LIVE-2 stays `unverified` with `finding = "F-1, F-2"`. SH-5 is `in-progress` with `finding = "NT-F1"`: it holds on the `--cfg near` build that §1 scopes, and is false on `scripts/build.sh`. Every row whose §5 Statement or Status cell names a finding carries `finding` too: the witnesses below, and the caveats on AUTH-1, SH-3 and SH-10. status-lint ignores the key; it is for readers. |
| Finding witnesses | TLA-LIVE-F1, TLA-LIVE-F2, LEAN-WIT, RT-WEDGE and C-5's known findings pass while their finding reproduces. When upstream fixes one, its witness fails as stale. Invert it into the property it guarded; do not delete it. |
| `[assumptions.<ID>]` | The 14 rows of §5.14. `statement` is §5.14's; `level` is `threat_model.pl`'s, the same as §5.14's. `checked_by` lists properties only: those of `assumption_checked_by/2` and of §5.14's *Evidence* cell that have a result. A check that is not a property (`check-pin.sh`, the wasm surface) is named in `observed`. `source` cites the NEAR pages near-approval read, or the upstream docs as `spec:<line>`. |
| Property `assumptions` | The ASMs the row's claim rests on: its tools and models (TOOLS, SPEC, MODEL, LEAN-TLA), the runtime behaviour it relies on, and the environment it assumes (TIME for MC-1 and LIVE-2, which cites MC-1; an honest executor, EXEC, for LIVE-2, TLA-LIVE-F2 and MC-1's release-blocked states). Where a §3.2 threat's residual is an ASM, every property that mitigates the threat lists it: EXEC on ASYNC-1, RT-CALLBACK, SH-3 and INV-LEDGER (T-UNKNOWN), OWNER on OBS-1 and INV-WF (T-OBS). The in-bounds observations of LIVE-1, TLA-LIVE-1 and TLA-LIVE-F2 are premises of those claims, not OWNER. No property lists DEPLOY: T-REDEPLOY's only mitigation is the assumption itself, and no §5 row checks a deployment (§9.3). |

---

## 13. Milestones

| # | Deliverable | State |
|---|---|---|
| M0 | Submodule at the PR #1 head; `status.toml` with 16 `[source_hashes]` and `release_overflow_checks`; conformance generator and traces | Done |
| M1 | Kani on the real core (§6) | Done: 89 harnesses, 164 covers, 31 mutants, REF-1..3. In the workflow (§14): CI runs the 53 harnesses that fit the hosted runner, and checks the local record of the other 36 and of 16 mutants (run at `89f99d6`). |
| M1.5 | TLA+ (§17) | Done, except TLA-IND (open). REF-1..3 done with M1 (§17.2). |
| M1.6 | Lean (§18) | Done |
| M3 | Shell: `near-tests/`, wasm surface | Done |
| M4 | Prolog (§8) | Done |
| M5 | Verus | Deferred (§7) |
| M6 | Sandbox | Done, on one shard |
| M7 | Deployment | Out of scope |
| CI | `.github/workflows/shared-pool.yml` (§14) | Green on PR #31 (run 43194245726) for every layer but Kani. Runs 43469880167 and 43488691444 ran all 29 Kani groups on the 16 GB hosted runner. Every other job was green, but 4 and then 2 of the 29 groups did not finish on swap, so `kani` and `covers` failed (§14). The workflow now splits Kani: `kani` runs the 8 groups that fit in memory, and `kani-record` checks the local record of the other 21. The split has not run in CI yet. |

**Pin decision (2026-11-13).** PR #1 merged (`b9e994f`), and upstream
marked the contract v1.0.0 in `6f61616`. `git diff a4bb5c3 6f61616 --
crates/core/src/lib.rs crates/contract crates/executor` is empty; the
version number is only in the root `Cargo.toml`. The pin stays at
`a4bb5c3`. Moving it would renumber the conformance traces (v1.0.0's
`fixtures.rs` adds a `station` fixture first) and change the wasm hashes,
with no change in the verified code. The results are labelled "verified:
shared-pool-controls v1.0.0 (contract code byte-identical to the pin
`a4bb5c3`)". The label names the code the layers checked; no
`status.toml` row is `verified` until a spec reviewer signs (§12). The
`pin` job fetches upstream `6f61616` and fails unless the three paths are
byte-identical to the pin (`check-pin.sh`, from `status.toml`; §12, §14).
Upstream PR #4 (v1.1) proposes fixes for the findings; v1.1 is not
verified here.

**Next, in order.**
1. The split's first green CI run (§14): commit the local record (the
   run at `89f99d6`, `kani/local/record.py`), then `kani`, `kani-record`
   and `covers` must pass on PR #31.
2. Report F-1..F-6, NT-F1..NT-F4 and the two doc divergences upstream.
3. When v1.1 (PR #4) merges, re-pin to it: regenerate the traces,
   recompute the hashes, rerun every layer, invert the finding witnesses
   (§12), and update the findings. The re-pin changes the Kani inputs,
   so `kani-record` fails until `kani/local/run-local.py --record` has
   been run at the new commit (hours on a 64 GB machine; the record's
   `provenance.txt` has this run's start and end) and the record
   committed.
4. A named reviewer who wrote neither `pool-core` nor the models signs off
   the specs (`[review] spec_reviewer`).

Closed from this list: the Kani layer with REF-1..3 (§6, §17.2); the Kani
jobs and the v1.0.0 byte-identity check in the workflow (§14), and their
first run; Kani on the hosted runner alone (on swap, or with a larger
`KANI_RUNNER`), replaced by the local record of the 36 harnesses and 16
mutants that do not fit it (§14, OQ-11);
re-pinning to PR #1's merge, replaced by the byte-identity decision above;
pointing C-6 at §5 instead of the brief (§5); a
conformance trace of F-2's `Bounds` form on the `risk` fixture (trace
209; traces 210 and 211 add F-4 and F-6), which TLA+, Lean, Prolog and the
shell all replay; and the §5 properties and assumptions in `status.toml`
(83 properties and 14 assumptions, §12).

---

## 14. CI (`.github/workflows/shared-pool.yml`)

The workflow is authoritative. Jobs run on pull requests and pushes to
`main` that touch the project. Changes only to documentation (`*.md`,
`docs/`) do not trigger them, except `strategy.md`: C-6 reads its §5, so
the path filters include it again. `sandbox` runs only on
`workflow_dispatch` with `sandbox: true`, and `kani-mutants` and
`kani-mutants-large` only with `mutants: true`. `kani` and `kani-large`
take hours, so they and `covers` run only when the change reaches the
Kani layer: `kani/` (not its Markdown, nor `kani/local/*.py`, the local
runner and recorder; a change to the record's data counts), the gitlink or
`.gitmodules`, `conformance/traces/core.txt`, `tools/versions.env`, a
`.cargo/config[.toml]` at the root, in `projects/` or in
`projects/shared-pool/` (cargo reads those above the crate too), the
scripts they call, or the workflow (the `pin` job's `kani` output; a
manual run sets it with the `kani` input, default on). Every input of the
local record's fingerprint is among these paths. `plain`, `mutants` and
`kani-record` take minutes and run on every change.

Kani's runners. The repository is public, so GitHub's hosted
`ubuntu-latest` has 4 CPUs and 16 GB (15.6 GB usable). The workflow
splits the Kani work by the peaks `kani/RESULTS.md` measured on the 64 GB
Mac:

| Where | Harnesses | Mutants under Kani |
|---|---|---|
| Hosted runner, in memory | `kani`: the 53 harnesses that peaked at 13 GB or less, in 8 groups | `kani-mutants` (manual): the 15 sized at 13 GB or less by their named harness's peak |
| Local record, checked by `kani-record` (or `KANI_RUNNER`) | `kani-large`: the 36 that peaked above 13 GB (31 above 16 GB, `h_wedge` at 39.0 GB), in 21 groups | `kani-mutants-large`: the other 16 (mutant 21 is sized by `h_full_255`, since it takes `h_full_256` past the record limit) |

On the hosted runner the large groups ran on swap, slowly, and some
never finished (below). So they and the large mutants run on a local
machine. `kani/local/run-local.py` runs
`kani-large`'s groups and `kani-mutants-large`'s mutants from the
workflow's lists, with `run.sh` unchanged and each job's matrix timeout,
and `kani/local/record.py` records a run that passed in `kani/local`
(`provenance.txt`, `jobs.tsv`, `covers.tsv`; `kani/local/README.md`).
The record holds the run's commit, a fingerprint of the Kani inputs, and
each job's result, time, peak and limit. The inputs are every file under
`kani/` except `kani/local` and the Markdown (so a new file there, such as
`kani/.cargo/config.toml`, counts), with the git object ids of
`kani/src`, `Cargo.toml`, `Cargo.lock`, `mutants`, `run.sh` and
`.gitignore` on lines of their own; the core's gitlink and
`conformance/traces/core.txt`; the repository's cargo configuration
above `kani/` (none at the record's commit; `run-local.py` copies it into
its lanes); and `tools/versions.env`'s `KANI` and `CBMC`. `run-local.py`
refuses to run when the environment or a cargo configuration file
outside its lanes sets something that changes a verdict but not the
fingerprint (`KANI_FLAGS`, `RUSTFLAGS`, a profile, and the like). The
current record is the run at `89f99d6` on a 10-core, 64 GB Apple M1 Max
(`kani/RESULTS.md`, Local record, which renders it).

`kani-record` runs on every change, in about a minute and without the
submodule: the self-test `tools/scripts/test-check-kani-record.sh`, then
`tools/scripts/check-kani-record.py`. It fails when:
- the record's fingerprint is not the commit's. The message names the
  changed inputs and says "re-run the local Kani record";
- the data do not match their digest, or the fingerprint is not the hash
  of the record's input lines or (where the clone has it) of the
  record's commit;
- a recorded harness is not `ok`, or a recorded mutant is not as its
  patch expects;
- the `kani` groups and the record do not cover `run.sh list` exactly
  once, or `kani-mutants` and the record `mutants/*.patch`;
- a `kani-large` or `kani-mutants-large` timeout is below the limit the
  record ran that job under (the workflow is not in the fingerprint; a
  warning when this run's large jobs verify it);
- a hosted entry peaked above 13 GB;
- `kani/RESULTS.md` has no block, or its block is not the record's table.

`covers` adds the record's harnesses and covers to the groups'. CI checks
that the record is consistent and belongs to the commit's inputs, not
that the run took place as recorded (§15).

`kani-large` and `kani-mutants-large` run only when the `KANI_RUNNER`
repository variable names a runner other than `ubuntu-latest` and the run
is not routed to `ubuntu-latest`: the `pin` job's `large` output. That
runner needs at least 49 GB, 1.25 times `h_wedge`'s peak. They have no
swap step. Their runner-size step fails a group whose peak is above the
runner's memory plus swap, or, on a hosted runner, above its memory. A
stale record is then only a warning if the run verifies everything it
records: `kani-large` its harnesses and `kani-mutants-large` (manual,
`mutants: true`) its mutants. Otherwise it fails as before. So a change
to the Kani inputs needs a new record whatever `KANI_RUNNER` is: until it
is re-made, `kani-record` fails on every pull request and push, and only
a manual run with `kani` and `mutants` on `KANI_RUNNER` passes without
it. When `kani-large` runs, `covers` uses the groups' logs
alone. The Kani jobs take `KANI_RUNNER`, then
`CI_RUNNER`, then `ubuntu-latest`, as near-approval's do. Routed runs
(Dependabot, automated agents) always get `ubuntu-latest`, and so the
record. On hosted Linux, `kani` and `kani-mutants` add a swap file of
`KANI_SWAP_GB` (default 16, bounded by free disk). It is a margin for a
Linux peak above the macOS one: macOS resident memory leaves out
compressed pages. A group that runs out of time fails, it is not
skipped. Per group, `KANI_TIMEOUT` is three times its slowest measured
harness (at least 1,800 s) and `KANI_MAX_GB` 1.5 times its peak. On a
runner with less memory than the group's peak, each harness may instead
use an equal share of 330 of the job's 360 minutes. No loop-bounds job:
near-approval's U-1 serves its cutoff, and this project claims none;
`run.sh` keeps unwinding assertions on.

Before the split, all 29 groups ran on the hosted runner. Run
43469880167 had memory plus swap at 1.25 times each group's peak, and the
measured timeouts. Every job but `kani` and `covers` passed. 25 of the
29 groups passed: 85 of the 89 harnesses as required, `h_canary` failing
on its own assertion. In memory, harnesses took 0.9 to 2.1 times their
time on the Mac (median 1.4); on swap, 1.0 to 4.3 times (median 1.6),
and `h_step_submit_inv_3` used 3,586 of its 3,600 s. Four did not
finish, the four with the largest SAT instances:
- `h_energy_max` (226 million clauses), out of time at 1,800 s;
- `h_bmc_from_init_s_submit` (100 million), out of time at 3,600 s;
- `h_validate` (72 million), out of time at 2,400 s;
- `h_bmc_from_init_po` (160 million), whose runner shut down after 33
  minutes with no log. `covers` then failed for lack of that log.

Run 43488691444 (commit `89f99d6`) had memory plus swap at twice each
group's peak, and on swap each harness's share of 330 of the job's 360
minutes. 27 of the 29 groups passed (87 harnesses), but two still did
not finish. `h_bmc_from_init_s_submit`'s runner lost contact after 52
minutes on swap. `h_bmc_from_init_po` ran for over 3 hours before the
run was cancelled. Hours per run, and runners lost on swap, led to the
local record.

| Job | Runs | Fails on |
|---|---|---|
| `pin` | `tools/scripts/check-pin.sh shared-pool`, which also fetches upstream `6f61616` (`verified_release_commit`) by SHA and compares `identical_paths` (§12, §13); the changed paths, for the `kani` output | gitlink ≠ `pinned_commit`; `[source_hashes]` drift; no `overflow-checks = true`; `crates/core/src/lib.rs`, `crates/contract` or `crates/executor` not the same tree or blob as at `6f61616`, or that commit not fetchable. Every job but `status-lint` needs it. |
| `status-lint` | `tools/scripts/check-status.sh shared-pool` | evidence not allowed for its layer; a status without its artifact; a status above its ceiling |
| `conformance` | `cargo run --release --locked -- --check traces/core.txt`, then `-- --reads-check traces/reads.txt` | the checked-in traces or reads differ from the generator's output; a read class not reached; `preview` and `submit` disagree |
| `tla` | `tla/run.sh safety liveness trace` (about 10 min), then `run.sh mutants` | a check failing; a witness or required violation passing; a mutant surviving |
| `lean` | `lean/run.sh` (about 4 min) | a `sorry` or forbidden construct; an extra axiom; a canary compiling; a REF-5L difference; a mutant surviving |
| `prolog` | `prolog/run.sh` (about 9 min) | a suite failing; a loader warning; extraction drift; a canary passing; a mutant surviving |
| `near-unit` | `near-tests/run.sh all`: the PROP-tag check, tests, surface, and the 21 mutants (about 9 min) | a tag problem (`check-tags.py`); a test failing; lockfile drift; a surface diff (SURF-2 stays expected-fail); a mutant surviving |
| `sandbox` | `sandbox/run.sh` (about 7 min warm) | any failure; lockfile drift |
| `plain` | `kani/run.sh plain`: the harness bodies with a random source, 27 tests, and REF-1..3 on every trace call (10 s of tests; not proof); 15 min limit | a test failing; a cover that a body evaluates never firing |
| `mutants` | `kani/run.sh mutants`: the 31 mutants in plain mode (about 4 min); 30 min limit | a must-kill mutant passing plain mode; mutant 20 (`must-survive`) failing it |
| `kani` | `kani/run.sh kani <group>` with `KANI_DEFER_COVERS=1`, a matrix of the 8 groups (53 harnesses) that peaked at 13 GB or less, on the hosted runner unless `KANI_RUNNER` or `CI_RUNNER` is set (see above); per group `KANI_TIMEOUT` and `KANI_MAX_GB`; logs uploaded | a harness failing, out of time or out of memory; `h_canary` passing, or failing on anything but its own assertion; a runner whose memory plus swap is below the group's peak; a runner that shuts down |
| `kani-large` | as `kani`, for the 21 groups (36 harnesses) that peaked above 13 GB; only when `KANI_RUNNER` is set, is not `ubuntu-latest`, and the run is not routed (the `pin` job's `large`); no swap step | as `kani`; a hosted runner with less memory than the group's peak |
| `kani-record` | every change: `tools/scripts/test-check-kani-record.sh`, then `tools/scripts/check-kani-record.py` on the local record in `kani/local` (see above; `--stale-ok-harnesses` when `kani-large` runs, `--stale-ok-mutants` when `kani-mutants-large` runs) | the record's fingerprint not the commit's ("re-run the local Kani record"), unless this run's large jobs verify all it records; data not matching the digest, or a fingerprint not its input lines' or its commit's; a recorded harness not `ok` or a recorded mutant not as its patch expects; `kani` plus the record not `run.sh list` once each, or `kani-mutants` plus the record not `mutants/*.patch` once each; a large entry's timeout below the record's limit for it; a hosted entry above 13 GB; a missing or stale `kani/RESULTS.md` block |
| `covers` | after `kani`, `kani-large` and `kani-record`: every harness of `run.sh list` in exactly one group's logs or (without `KANI_RUNNER`) the local record, then `tools/scripts/check-covers.sh` over every group's `covers.tsv` and the record's covers (89 harnesses, 164 covers) | a harness in no group nor the record, or in two; a family's cover satisfied in none of its harnesses |
| `kani-mutants` | `kani/run.sh mutants --kani <NN>-*`, one job per mutant for the 15 sized at 13 GB or less, with the named harness's peak and three times its time, at least 1,800 s (manual, `mutants: true`) | a mutant whose plain or Kani result differs from its header (`killed-by`, `must-survive`) |
| `kani-mutants-large` | as `kani-mutants`, for the other 16, only when `KANI_RUNNER` is set, is not `ubuntu-latest`, and the run is not routed (manual, `mutants: true`); otherwise they are the local record's | as `kani-mutants`; a hosted runner with less memory than the mutant's peak |

---

## 15. Risks

| Risk | Mitigation |
|---|---|
| The pin is not the v1.0.0 commit itself. | Its contract code is byte-identical to v1.0.0's (§13), and the `pin` job fails if that stops being true (§14). Both commits are on upstream `main`; `pin` fails loudly if either cannot be fetched. |
| A fix for F-1 or F-2 changes admission or release. | Every model follows the code's guard order, and the traces regenerate from the core. Witnesses flip and must be inverted (§12). |
| Three hand-written models share a transcription error. | All replay the same real-core traces; C-2 compares guard orders; every layer has mutants; REF-1..3 tie TLA+ to the code per step, within the step bounds. |
| The Prolog author read the code (ASM-SPEC). | Doc citations on every fact; a named independent reviewer. |
| Kani is slow on `Vec`-heavy state: 7.5 h for the 89 harnesses, one at a time, with peaks up to 39 GB. | Fixed small shapes, step parts, per-loop unwinding (§6); plain mode runs in seconds; `kani` runs 8 groups in parallel, only when the Kani layer's inputs change. The 36 harnesses that peaked above 13 GB ran slowly on the hosted runner's swap, and some never finished (runs 43469880167 and 43488691444), so they and 16 mutants come from the local record (§14). |
| CI does not run the 36 large harnesses and 16 mutants; it checks their local record (§14). | The record names the commit, the tool versions and the machine, and fingerprints the Kani inputs: any change to them fails `kani-record` until the run is repeated. A digest catches edited data, and the check refuses a record whose results are not as required, or whose jobs are not exactly the large groups'. It cannot show that the run took place as recorded; that rests on whoever ran it, as the measurements in `kani/RESULTS.md` do. Anyone with 64 GB can repeat it (`kani/local/run-local.py --record`) and compare, and `KANI_RUNNER` runs the large groups in CI. |
| Kani's bounds are small: 1 metric, 1 term, 2 recipes and 2 records per step. | Plain mode at larger shapes, Lean at every size, the traces at 256 records and ±1,000,000 (ASM-MODEL). |
| Kani or CBMC is unsound for a construct the harnesses use. Two hazards were found in Kani 0.68.0. | Canary, covers and mutants; both hazards worked around and documented (`kani/RESULTS.md`, Tool issues), with a scan of every goto program for the first (ASM-TOOLS). |
| TLC's 32-bit integers | Overflow aborts a run, so no run passes silently. Lean covers large values, and Kani's `h_energy` the core's energy over the whole value range. |
| One-shard sandbox | RT-RACE records what one shard cannot show. The models treat ack and settle as independent steps. |
| The import surface cannot exclude code replacement (NT-F3). | Source review and dynamic absence. Deployment stays out of scope. |
| TLC memory on a GitHub-hosted runner. | Closed: at `TLA_HEAP=5g` the `tla` job passed safety (2,306,738 states, 1,300 s), liveness, trace and all 31 mutants on PR #31's first run. Peak RSS not recorded. |

---

## 16. Open questions

| # | Question |
|---|---|
| OQ-1 | PR #1 merged and the pin stays at `a4bb5c3`, byte-identical to v1.0.0 in the contract code (§13). When PR #4 (v1.1) merges, re-pin to it at once, or keep v1.0.0 as the verified version until v1.1 has been through every layer? |
| OQ-2 | F-1 and F-2 are upstream's call. Options: refuse a hedge whose completion re-violates a metric its own reservation cured; allow a nonexecution release after a completed sibling relied on it; or stop counting unexecuted reservations as headroom. Each layer's witness flips with the fix. Upstream PR #4 (v1.1) proposes fixes; they are not verified here. |
| OQ-3 | NT-F1: build with cargo-near or `--cfg near`, and have upstream's sandbox tests assert failure messages. |
| OQ-4 | NT-F3: is source review plus dynamic absence enough for the 15 linked host functions, or is a static call graph of the wasm needed? |
| OQ-5 | F-4: should `validate` reject actor = executor, and an actor or executor that is the owner? |
| OQ-6 | F-3: a per-actor record cap, pruning on observe, or a documented limit? F-6: a refresh path that does not need every record terminal? |
| OQ-7 | TLA-IND: rewrite the model for Apalache, or accept LEAN-IND as the every-size safety result? |
| OQ-8 | L-1b: confirm with upstream that a reservation that cured a violation is meant to be uncancellable. |
| OQ-9 | Docs: update spec:39 and api:26 for the no-op acknowledgment, and api:34 for non-string results (NT-F4); state a minimum prepaid gas per method in api.md (none is given). Measured at the maximum-size state (§9.2, RES-1): `dispatch` needs at least 70 Tgas, `reconcile` 46 Tgas and the executor's `finish` 43 Tgas; 70 Tgas leaves under 1 Tgas spare for `dispatch`, so the documented figure needs headroom. |
| OQ-10 | Who reviews the specs? |
| OQ-11 | Closed (2026-11-13): Kani in CI, swap or a large runner? Neither, by default. On the 16 GB hosted runner, the 53 harnesses that peaked at 13 GB or less run in memory. The other 36 (31 above 16 GB, up to 39 GB) ran on swap there, up to 4.3 times slower than on the Mac. In run 43469880167 four of them did not finish; in run 43488691444, with memory plus swap at twice the peak and the job's whole time, two still did not (one lost its runner, one ran over 3 hours). They and 16 mutants are run locally and recorded, and CI checks the record (§14). `KANI_RUNNER` (at least 49 GB) still runs them in CI when it is set. |

---

## 17. TLA+ over every event sequence

Kani proves one step of the real core within bounds (§6). That says
nothing about liveness or safety at depth. The TLA+ model is checked over
all event sequences in small universes, and tied to the real core by the
traces (REF-5) and, within the step bounds, step by step (REF-1..3,
§17.2). Results:
`tla/RESULTS.md`. TLC 2.19 (tla2tools 1.7.4), OpenJDK 23.0.2, 4 workers;
final runs ended 2026-11-12.

### 17.1 The model (`tla/`)

| File | Contents |
|---|---|
| `SharedPool.tla` | The pool as variables (`cfg`, `values`, `version`, `observedAt`, `paused`, `records`). No action writes the config, so one run replays traces of many configs. Ghosts: `base`, `k0`, `steps`, `last`. One error operator per entry point gives the first failing guard in code order, `"Noop"` or `"Ok"`. An action is enabled exactly when it gives `"Ok"`, so rejected and idempotent calls stutter. `GuardOrder` lists each entry point's exits. `ValidCfg` transcribes `validate`. |
| `Props.tla` | The INV-* invariants, TERM-1, LIVE-1. `StepProperty`: TX-VER, LIFE-1, STALE-1, AUTH-1, ADM-1, ADM-2, HARD-STEP, DEP-1, ASYNC-1, OBS-1, TX-SUBMIT and TX-DISPATCH in part, PAUSE-1. The witnesses. |
| `MCCommon.tla` | Two universes. `MCConfig` is the F-1 wedge scaled down (m0 ∈ [0,2], m1 ∈ [−2,2], a hedge and a dependent recipe, max_age 1). `CreditHedgeConfig` is the `risk` fixture's credit and hedge scaled down (F-2). Accounts o, a1, x1, z. |
| `MC_Safety.{tla,cfg}` | TLA-SAFE and TLA-WIT on `MCConfig`. Times {0,1,2}, expiry offsets {0,1,2,86400,86401}, 14 observation vectors, MaxRecords = 3. A `VIEW` drops `version`, `steps` and `last` (a bisimulation quotient). |
| `MC_Liveness.tla` + 7 cfgs | LIVE-2 under named fairness. MaxRecords = 2. Submit, pause and observe are allowed only while version < 4. |
| `TraceCheck.{tla,cfg}`, `trace2tla.py` | REF-5: all 212 traces in one run. |
| `mutants/*.patch` | 31 spec mutants |

### 17.2 The refinement link

REF-1..3 are bounded proofs on the real core (`kani/RESULTS.md`, REF-1..3
and deviation 26). `kani/src/tla.rs` transcribes `SharedPool.tla`
operator by operator from the `.tla` text, not from `spec.rs` or the
code: the state image, the abstraction α (a `Pool` and its ghost `base`
and `k0`, mapped to the TLA+ variables), the error operators `SubmitErr`
to `ObserveErr` in `GuardOrder`'s order, and the actions. The
`h_ref_<op>` harnesses use the step harnesses' generators, so they share
their bounds: every INV pre-state with 1 metric, 1 term, 2 recipes and
exactly 2 records, and every operation of the step domains (§6). For each
call they assert:

- **REF-1 (guard exactness):** the core's error is the error operator's
  value on α(pre), and the core is Ok exactly when the operator gives
  "Ok" (the action is enabled) or "Noop" (an idempotent call).
- **REF-2 (effect exactness):** when the operator gives "Ok", α(post) is
  the action's post-state, configuration and ghost included; submit
  returns the new record's index.
- **REF-3 (stutter):** every other call leaves α unchanged.

Run M (`kani/run.sh ref`, exit 0) and its rerun N: 7 of 7 `ok`, 55 to 351
s each, at most 12.4 GB (N's exact peak).
The 46 `ref` covers, every operator value the step domain reaches, are
SATISFIED; `Full` needs 256 records and is reached only on the traces.
Plain mode runs the same check on every sample of the step tests and on
every call of the 212 traces (`h_ref_traces`, 8,804 calls: "Ok" 2,053
times, "Noop" 494, and each of the 15 errors the traces contain). Mutant
31, an error in `tla.rs`'s `ReleaseErr`, is killed by `h_ref_cancel`.

**Limits.** The proofs hold within the step bounds only; other shapes and
record counts are tested, in plain mode and on the traces. `tla.rs` is a
hand transcription of the `.tla`. It meets TLC only on the traces, where
both agree with the core (REF-5), and so with each other. The history
variables `steps` and `last` are not mapped, and `Init` is linked by
CFG-1 and the traces, not by a REF harness.

### 17.3 What is checked

LIVE-2 depends on what the executor is assumed to do, so each liveness
check names its fairness assumption:

| Check | Assumption | Result |
|---|---|---|
| TLA-LIVE-1 | Observes in bounds (B = 0); the executor is weakly fair to completing each record. | LIVE-2 holds in both universes. This is close to its premise: LIVE-1 keeps `settle(true)` enabled, and fairness makes it happen. The check adds that LIVE-1 holds in every reachable state, and that nothing else keeps a record open. Without fairness (`MC_Liveness_Unfair`) it must fail, and it does. |
| TLA-LIVE-F1 | One disturbing observe; the executor is weakly fair to settling either way. | LIVE-2 is violated. `Live2F1` shows that, at these bounds, every counterexample is the F-1 wedge. |
| TLA-LIVE-F2 | No disturbing observe; weak fairness of the honest `settle(false)` and of cancelling Reserved records. | LIVE-2 is violated. `Live2F2` shows that, at these bounds, every counterexample is the F-2 wedge. Fairness to settling either way would hide F-2: `settle(true)` stays Ok in the wedge, so fairness would force a false attestation (mutant 31). `MCConfig` cannot build F-2 with 2 records; hence `CreditHedgeConfig`. |

### 17.4 Results

- **TLA-SAFE:** 2,306,738 distinct states, depth 15, 522 s (56.5M states
  generated).
- **TLA-WIT:** `Witness_Completed`, `_Prerequisite`, `_Disturbed` and
  `_Wedge` are violated with traces of 4, 6, 2 and 4 states. So are the
  step witnesses `WitStep_CancelledAfterDispatch`, `_UnknownToActive`,
  `_Recovery` and `_PausedSettle/Ack/Cancel/Observe`.
- **Liveness:** as in §5.11. `MC_Liveness_F2`'s path varies between runs
  with 4 workers. The runner checks the end state: the credit in flight,
  the hedge Completed, the base in bounds, then stuttering.
- **F-2b** was found here, then checked on the pinned core and added to
  the generator as trace 208.
- **REF-5:** 9,016 of 9,016 states (212 initial + 8,804 steps), in 8 s.
- **REF-1..3 (Kani):** 7 of 7 `h_ref_*` harnesses `ok`, 46 of 46 covers
  SATISFIED, within the step bounds (§17.2).
- **Mutants:** 31 of 31 killed (28 by the trace check, 2 by liveness, 1 by
  `liveness-f2`): 150 s locally on the 209-trace set, and 4 min 10 s on
  the 212 traces in CI (GitHub Actions run 43194245726 (PR #31, 2026-11-12, ubuntu-latest, `TLA_HEAP=5g`)). Mutants 10, 13, 23, 24, 25 and 26
  survive traces 0-205 alone; traces 206 and 207 kill them. One equivalent
  mutant is not checked in: "`add` ignores the upper bound". The envelope
  check after every `add` gives `Arithmetic` there.
- **Run times:** `run.sh` (default: safety, liveness, trace) takes 573 s
  locally (10 cores, 209-trace set; trace check on 212 traces 8 s) and
  23 min 7 s on a hosted runner (safety 1,300 s), the `run.sh mutants` 150 s
  locally and 4 min 10 s in CI.

### 17.5 Limits

- **TLC integers are 32-bit.** TLC stops with "Overflow" rather than
  wrapping, so a run cannot pass silently. `MaxVersion` is 2^31 − 1 and no
  run gets near it, so F-5's exits are never exercised. The 7 request
  versions of u32::MAX in the traces are mapped to −1; they still give
  `Stale`, because the highest state version is 513. `w·r²` is exact only
  below 2^31, while the core's energy reaches 4·10^15, so energy at large
  residuals (NUM-1) is Kani's (`h_energy`, `h_energy_max`, §6).
- **Scaled constants.** MaxRecords is 3 in MC_Safety, 2 in MC_Liveness,
  and 256 in TraceCheck. `MAX_VALUE`, `MAX_UNITS`, `MAX_WEIGHT` and the
  86,400 s window keep their real values.
- **TLA-IND is open.** Apalache 0.47.2 rejects the recursive sums and the
  symbolic ranges. Fixing that is a rewrite (`ApaFoldSeqLeft` sums,
  `DOMAIN`-based ranges, type annotations), and `run.sh apalache` prints
  `skip`. Every-size safety comes from Lean instead.
- **Small universes.** MC_Safety has 2 metrics, 1 term, 2 recipes, at
  most 3 records, 4 accounts, 3 block times and 14 observation vectors.
  There is no symmetry reduction.
- **Not modelled:** `preview`, `best_quantity`, the shell, the executor,
  and promise interleavings beyond independent ack and settle steps.

---

## 18. Lean: the core's model at every size

Results: `lean/RESULTS.md`. Lean 4.34.1, core library only (no Mathlib).

Every other layer is bounded somewhere. The Lean layer proves the
transcribed core's safety for every number of metrics, recipes, terms,
records and accounts, any config `validate` accepts, and any times and
arguments.

### 18.1 The model (`lean/`)

`PoolLean/Machine.lean` transcribes `lib.rs`. Each call is its guard list
in code order, then `effect`. The first guard that fires is the outcome;
errors and no-ops stutter. Values are `Int`, counters `Nat`, and accounts a
type parameter with decidable equality. Ghosts: `base` and `k0` (values and
record count at the last `observe` or `new`) and `eff` (effective
transitions). `Inv` (`Props.lean`) is INV-WF ∧ INV-LEDGER ∧ INV-HARD ∧
INV-DEP ∧ INV-VER. The other modules are `Inv`, `StepProps`, `Calls`,
`Live`, `Guard`, `Witness`, `Facts`, `Lemmas` and `Text`; `Main.lean` is
the `pool-lean` executable.

### 18.2 What is proved

| ID | Theorems | Statement |
|---|---|---|
| LEAN-IND | `inv_init`, `inv_step`, `reach_inv` | `Valid cfg ⇒ Inv (init cfg now)`; `Inv s ⇒ Inv (step s op)` for every op |
| LEAN-STEP | `stepProps`, `stepProps_step`, `exec_auth`, `term1`, `term1_cancel`, `stale1_no_replay`, `version_mono_run` | From every state, with no `Inv` premise: TX-0, TX-NOOP, TX-VER, LIFE-1, AUTH-1, STALE-1 (never accepted again in any later run), ADM-1, ADM-2, HARD-STEP, ASYNC-1; TERM-1 for settle and cancel |
| (also) | `dep1`, `obs1`, `pause1_blocks`, `pause1_transparent`, `healthy` | DEP-1, OBS-1, PAUSE-1, INV-HEALTHY |
| LEAN-LIVE1 | `live1`, `live1_exec`, `live1_reach` | `Valid cfg`, `Inv s`, B = 0 and version < u32::MAX ⇒ `settle(executor, id, true)` passes every guard and completes each in-flight record |
| LEAN-GUARD | `Guard.guards_order`, `Guard.outcome_mem` | Every call's outcome codes are exactly `guardOrder`, written from `lib.rs` with line numbers |
| LEAN-WIT | `Witness.lean` | F-1 and healthy-side witnesses, by `decide` and `rfl` in the kernel |
| REF-5L | `pool-lean replay` | 212 traces, 8,804 calls (2,547 Ok); every result and post-state equal, the initial state included |

**LEAN-WIT, on trace 0's config.** `wcfg_valid` shows the config is
`Valid`. `wedge_eq`, `f1_results`, `wedge_reach` and `wedge_inv` reach
values [10,5] with record 0 Active, a reachable `Inv` state, and `wedge_B`
gives B₀ = 2. There, `f1_settle_true` and `f1_settle_false` fail `Bounds`,
and `f1_cancel_owner`, `f1_cancel_actor` and `f1_observe` fail `Pending`.
`f1_forever`: for every later sequence of calls, the values stay [10,5]
and the records stay exactly [record 0 Active] (corollaries
`f1_never_terminal`, `f1_observe_forever`, `f1_settle_forever`).
`live1_premises`, `live1_instance`, `healthy_settle`, `unknown_settle`,
`cancelled_reach` and `stale_instance` show the healthy side is not
vacuous.

### 18.3 Hygiene gate and mutants

- **Axiom audit** (`Audit.lean`): 40 of 40 headline theorems use only
  `propext`, `Classical.choice` and `Quot.sound`.
- **Canaries** must fail to compile, and do: `canary/False.lean`,
  `canary/NotInv.lean` (every state satisfies `Inv`) and
  `canary/Live1NoPremise.lean` (LIVE-1 without B = 0, false by F-1).
- **Scan.** With comments stripped, there is no `sorry`, `admit`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
- **Mutants.** 16 mutants of `Machine.lean` each go through the replay
  and the full `lake build`, and all are killed. Mutants 04 (version
  overflow off by one), 10 (a prerequisite needs one unit) and 13 (observe
  keeps `k0`) are caught only by the proofs; 14 (snapshot age inclusive)
  only by the traces.
- **Run times.** `lean/run.sh [build|audit|canary|replay|mutants]`. A clean
  build takes 7 s, the mutants 224 s, and everything 227 s.

### 18.4 Gaps

- **Transcription.** `Machine.lean` is transcribed by hand. REF-5L found
  no disagreement on 212 traces. That is evidence, not proof.
- **Numbers.** The model computes exactly in `Int` and `Nat`; fixed-width
  overflow in the code is NUM-1 and NUM-2 (Kani). The code's `energy`
  `Arithmetic` error is not modelled (claimed unreachable; Kani's NUM-1
  shows `energy` Ok on bounded values of 2 metrics and 2 terms, and at the
  64-term worst case). The envelope's
  fail-on-first partial sums are modelled by the final sums: argued, not
  proved.
- **Types.** Times, units and versions are unbounded `Nat`. u64
  `saturating_add` and the u32 version overflow are exact. `max_age`'s
  u32 type and all strings are not modelled.
- **Panics (ROB-1).** Not modelled. `Inv` shows every index the guards
  read is in range, but not that the Rust never panics; Kani checks that
  on the real core within its bounds.
- **Not stated in Lean:** RD-PREVIEW, RD-BEST and the shell. (The
  Prolog layer tests the two reads of the real core against its model,
  COV-2, §8.) LIVE-2
  (LIVE-1 is its per-state half, and `f1_forever` its counterexample).
  TX-SUBMIT..TX-OBSERVE as separate theorems: they are the model's
  definitions plus REF-5L.
