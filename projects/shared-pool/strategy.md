# Shared Pool Controls Formal Verification Strategy

## Target

[`difflabai/shared-pool-controls`](https://github.com/difflabai/shared-pool-controls)
PR #1 is a NEAR contract that admits agent work against one shared pool of
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
| Pinned commit | `a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`, head of PR #1 (branch `feat/shared-pool-controls`, 2026-11-12 UTC, "Address review: reconcile griefing, broken doc link, CI robustness"). **Not on upstream `main`.** Re-pin when the PR merges (§13). |
| Crates | `pool-core` (`crates/core/src/lib.rs`, 492 lines): every decision; zero dependencies in the default build; `#![forbid(unsafe_code)]`; serde and borsh optional. `pool-contract`: a near-sdk 5.29.1 shell (predecessor → caller, block time in whole seconds, core errors → panics, a promise to the executor, a private callback, views). `pool-executor`: the synthetic executor (`execute`, `status`, `finish`, `confirm_not_executed`, fault modes). `crates/sandbox`: upstream's near-workspaces tests. |
| Toolchain | Upstream `rust-toolchain.toml` 1.98. Release profile: codegen-units 1, `opt-level = "z"`, LTO, `panic = "abort"`, `overflow-checks = true` (ASM-COMPILE). |
| TCB via `Cargo.lock` | near-sdk 5.29.1, borsh 1.8.1, serde_json 1.0.154, and their dependencies |
| Mirror | git submodule `projects/shared-pool/source-mirror` (`upstream_path = ""`) |
| Upstream docs | `docs/spec.md`, `docs/api.md`, `docs/verification-handoff.md`, cited as `spec:<line>`, `api:<line>`, `handoff:<line>` at the pin |

The split matches near-approval's. Every decision is in `pool-core`, which
has no dependencies, so Kani can target the deployed logic itself. The
shell is thin enough to cover with tests on the host, on the wasm, and on a
local chain.

**Status (2026-11-12, pin `a4bb5c3`).** TLA+, Lean, Prolog, the shell
tests and the sandbox are built and pass locally. TLA+, Lean, Prolog and
the shell tests replay the same 212 real-core traces (§10). The sandbox
compares the chain with a host `pool-core` oracle. Kani is in progress;
CI passes on GitHub (PR #31) for every layer but Kani, whose jobs are
pending. Two high
findings, F-1 and F-2, show that the settlement liveness the docs rely on
does not hold. Nothing is verified: there is no spec reviewer, and the pin
is an unmerged PR head. Next: land Kani, report the findings on PR #1, and
re-pin when it merges (§13).

---

## 1. What we establish

For `pool-core` at the pin, and for the shell built as cargo-near builds
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
(NT-F1). Kani on the real code is pending. None is verified (§12).

**Not established:** that a deployment runs this code (ASM-DEPLOY);
that no code path transfers funds, deploys code or adds keys (source review
only, NT-F3); executor honesty or true observations (ASM-EXEC, ASM-OWNER;
F-2 shows the honest executor is the one that gets stuck); that a policy
models the world (spec:31); receipt order across shards; optimality of
`best_quantity` (spec:27); eventual completion (handoff:29).

### Tiers

| Tier | Layers | State | Result |
|---|---|---|---|
| **1. Code-level core** | Kani (§6) | being built | Planned: bounded proofs of every transition contract on the real `pool-core`, and REF-1..3 to tie each TLA+ step to the code. No result yet. |
| **2. Models and operational** | TLA+ (§17), Lean (§18), Prolog (§8), near-tests and sandbox (§9) | built | Every-size safety for the model (Lean). Liveness and its failures over all event sequences in small universes (TLC). An independent reading of the docs (Prolog). The shell on the host and two wasm builds. Runtime assumptions on a local chain. TLA+, Lean, Prolog and the shell are tied to the real core by the traces (§10); the sandbox by a host `pool-core` oracle (§9.2). |
| **3. Unbounded on the code** | Verus (§7) | deferred | Removes the transcription gap between the Lean model and the code. |

Finish Tier 1, then re-pin and get the spec review. Revisit Tier 3 after
upstream decides on F-1 and F-2, since a fix changes what a proof covers.

### Upstream's obligations (handoff:9-23)

| Obligation | Properties | State |
|---|---|---|
| CFG | CFG-1, CFG-2 | Lean takes `validate` as its premise. Kani pending. |
| NUM | NUM-1, NUM-2, ROB-1 | Kani pending. The ±1,000,000 boundary is tested by trace 206. |
| AUTH | AUTH-1, SH-1, RT-PRED | Proved (model), tested. F-4: actor = executor is allowed. |
| ADM | ADM-1, ADM-2, HARD-STEP, INV-HARD | Proved (model), model-checked. Kani pending. |
| ATOM | TX-0, SH-5, RT-REVERT | Proved (model), tested. Messages lost on the documented build (NT-F1). |
| STALE | STALE-1 | Proved (model). |
| ASYNC | ASYNC-1, INV-LEDGER | Proved (model). RT-CALLBACK. |
| TERM | TERM-1 | Proved (model). EX-4. |
| DEP | DEP-1, INV-DEP | Proved (model). |
| BIND | LIFE-1, SH-6, EX-2 | Proved (model), tested. |
| STOCK, CASH | C-5 | Hold on the fixtures (bounded check). |
| RISK | C-5 | Fails: F-2. |
| Liveness (handoff:31) | LIVE-1, LIVE-2 | LIVE-1 (healthy, version < u32::MAX) proved (model). LIVE-2 fails: F-1, F-2. |

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
its evidence is a Prolog witness, a Lean mutant and the sandbox. F-1 and
F-3 also run on a local chain (RT-WEDGE, RES-1), and part of F-5 on the
wasm (RT-REVERT). The §4.2 findings are tests on the pinned builds.
Severity rates the harm to the property the docs promise.

### 4.1 Open: core

| ID | Finding | Reproducer and layers | Contradicts |
|---|---|---|---|
| F-1 (high) | **Disturbed-state hedge wedge.** An `observe` puts a metric outside [min, max]. The recovery rule (spec:23) then admits a hedge whose reservation brings the point inside, but whose completion moves it back out. From then on `settle(true)` and `settle(false)` both fail `Bounds`, and `cancel` and `observe` fail `Pending`, forever. The record never becomes terminal, and the pool can never be observed again. | **Trace 0.** Metrics m(0,10,5), m(−100,100,5); term t(1,0,1,target); recipe r(a1,x1,[−2,0],[2,−5],1,[]). `observe [12,5]`; submit 1 → `ok(0)`, values [10,5]; dispatch; `ack(true)` → Active; `settle` true and false → `Bounds`; the owner's `cancel` → `Pending`; `observe` → `Pending`. <br>**TLA+:** `Witness_Wedge` (4 states); TLA-LIVE-F1; `MC_Liveness_F1Shape` shows that, in the small universe, every LIVE-2 counterexample is this wedge. <br>**Lean:** `f1_forever` (for every later call sequence, the record stays Active and every observe fails). <br>**Prolog:** MC-1 `wedge` has 228 dead states. <br>**near-tests:** `wedge.rs` (from Dispatched, Unknown and Active; host and both builds). <br>**Sandbox:** RT-WEDGE. The executor commits "completed", its `settle(true)` fails `Bounds`, and the record stays Active. The executor then refuses `finish(cancelled)` ("terminal outcome conflict") and `confirm_not_executed` ("job exists"). The two contracts disagree permanently. | spec:46: a checked inverse "can fail if another commitment depends on its contribution". handoff:31 makes liveness conditional on resolving dependencies. Here no other commitment is open, so there is nothing to resolve (`div-F1-inverse`). |
| F-2 (high) | **Healthy-state release wedge in the supplied `risk` fixture.** No observe; every metric in bounds. A credit position is reserved (recipe 0, +20 on selloff loss). A selloff hedge (recipe 3, −10 per unit on completion) is admitted only because the position's +20 is counted: 60 + 20 − 70 ≥ 0 at 7 units. The hedge completes, and selloff loss is 10. The position's job never ran, so the executor honestly calls `settle(false)`. Releasing the +20 gives 10 − 20 < 0, so it fails `Bounds`. `cancel` and `observe` fail `Pending`. Only `settle(true)`, an attestation of work that did not happen, ends the record. The same check blocks `cancel` of a Reserved position. LIVE-1 is unaffected. <br>**F-2b** (found by the TLA+ layer): a release is not bounded by the envelope. After a sibling relied on the reservation, `values − reserve·units` can leave ±1,000,000. Then `cancel` (actor and owner) and the honest `settle(false)` fail `Arithmetic`. | **Trace 209** (`f2-risk`, 13 calls, the supplied `risk` config of trace 5, no observe): position × 1 (recipe 0, selloff loss 60 → 80), hedge × 8 (recipe 3, admitted with the position counted: 80 − 80 = 0), both dispatched and Active; the hedge settles completed (selloff loss 0). Then the executor's `settle(false)` for the position → `Bounds`, `cancel` by the owner and by the actor → `Pending`, `observe` → `Pending`; `settle(true)` → Ok, then `observe` → Ok. Equal under TLC, Lean, Prolog (MC-2) and the shell. <br>**Prolog:** `test_model` "F-2 witness" (position × 1, hedge × 7, hedge completed). C-5's release search finds 20 counterexamples in `risk` and none in `gpu`, `friday`, `inventory` or `hiring`. The first is `rel(p(0,1,3,7), release(0), other(reserved), via(cancel)) - err(bounds)`. MC-1 `reliance`: 150 release-blocked states with B = 0. <br>**TLA+:** TLA-LIVE-F2 (weak fairness of the honest `settle(false)` and of `cancel`); `MC_Liveness_F2Shape` shows that, in its small universe (`CreditHedgeConfig`), every LIVE-2 counterexample is this wedge. <br>**F-2b: trace 208** (`release-arith`, 13 calls), equal under TLC, Lean, Prolog and the shell. | spec:46: "In the supplied fixtures, physical availability and risk-credit timing prevent ordinary unsafe reliance on unexecuted work." spec:46 also says "resolve dependent work first", yet the dependent hedge is resolved and the release still fails. handoff:23 (RISK) is the related obligation, not contradicted. `div-F2-fixture-release`. |
| F-3 (low) | **Lifetime slot exhaustion.** One actor fills all 256 lifetime records with free submit-and-cancel cycles. After that, `Full` is permanent for every actor. `observe` does not prune (spec:54), and nothing else does. | **Trace 207** (`full`, 515 calls): submit `ok` 256, cancel `ok` 256, then submit `full` 2 (another actor, also after an observe). TLC TraceCheck (it also kills TLA+ mutants 13 and 25), REF-5L, MC-2, near-tests `traces.rs` and `sh4`. Sandbox RES-1: submit #257 is rejected `Full`. | Not explicit. handoff:34: "256 lifetime records bound ordinary growth". |
| F-4 (low) | **A principal can attest its own work.** `Config::validate` accepts a recipe whose actor is its executor, or the owner. That account can then submit, dispatch and settle its own work as completed. | **Trace 210** (`f4-self`, 8 calls): `validate` accepts recipe 0 with actor = executor = a1 and recipe 1 with actor = executor = the owner o. a1 submits, dispatches and settles record 0 completed, and o does the same with record 1; every call is Ok. Equal under TLC, Lean, Prolog and the shell. <br>**Prolog:** `test_model` "F-4 witness" (step/4). `extract.py` records `code_role_checks(validate, [])`. Code mutant c09 (validate rejects actor = executor) makes C-5 fail. | spec:64: "No worker can authorize its own acceptance through the wrapper". spec:50: "the independent operator". `amb-self-executor`. |
| F-5 (low) | **Version saturation freezes every transition.** At version = u32::MAX, every transition fails `Arithmetic`, including settling in-flight records and `set_paused(false)`. Reaching it takes 2³² − 1 effective transitions. | **No trace:** reaching version u32::MAX takes 2³² − 1 effective transitions; the highest version in the traces is 513. <br>**Prolog:** `test_model` "F-5 witness" (step/4 from a paused state at version u32::MAX with record 0 Dispatched: `settle` both ways, `ack` and `set_paused(false)` fail `Arithmetic`, `observe` fails `Pending`). <br>**Lean:** mutant 04 (version overflow one too late) is killed by the proofs. <br>**TLA+:** no witness; `VerErr` transcribes the bump, but `MaxVersion` is 2³¹ − 1 and no run gets near it (§17.5). <br>**Sandbox:** RT-REVERT patches version = u32::MAX into the state: `set_paused` and `submit` fail, and storage is unchanged. | None. handoff:34 documents "Version overflow is an explicit rejection". The effect on in-flight records is not documented. |
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
  built wasm with `wasm-surface.expected`. `pending (Kani layer)`: no result
  yet. `fails: F-n`: false, with a reproducer. No row is verified (§12).

### 5.1 Configuration and numerics

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| CFG-1 | `Pool::new` is Ok iff `validate` is Ok, and the initial state satisfies INV | kani, lean | Lean `inv_init` (`Valid cfg ⇒ Inv (init cfg now)`; strings not modelled); TLC TraceCheck on the configs the core accepted | partial: proved (model) without the string checks; Kani pending |
| CFG-2 | `validate` ⇒ references in range, vectors of length n, prerequisites strictly earlier and distinct, values bounded | kani, lean | Lean takes these checks as the definition `Valid`; no theorem about the Rust | pending (Kani layer) |
| NUM-1 | Valid config and bounded values ⇒ `energy_terms` and `energy` are Ok and exact | kani, lean | Lean computes exactly in `Int` and does not model overflow; TLC cannot represent large energies (§17.5) | pending (Kani layer) |
| NUM-2 | `add` fails closed exactly when the exact result leaves ±1,000,000 | kani, lean | Trace 206: `arithmetic` from `add` at 999,990 + 15 and from the envelope at 1,000,005; TLA+ mutants 23 and 24 | pending (Kani layer); boundary tested |
| ROB-1 | No core panic from any INV state, for any arguments | kani | Lean shows every index the guards read is in range (INV-WF), but does not model panics | pending (Kani layer) |

### 5.2 Transition contracts

Each contract gives the exact result (the first failing guard, in the
code's order), the exact post-state, and the frame.

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| TX-0 | Every `Err` leaves the Pool unchanged | kani, tla, lean, prolog | Lean `stepProps` (every call, every state); TLC TraceCheck; MC-2 | proved (model); tested on 212 traces; Kani pending |
| TX-SUBMIT | `submit`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2 on every replayed submit; TLC `StepProperty` (time, capacity and unit guards, effect); C-2 guard order | tested on 212 traces; model-checked in part; Kani pending |
| TX-DISPATCH | `dispatch`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2; TLC `StepProperty`; C-2 | tested on 212 traces; model-checked in part; Kani pending |
| TX-ACK | `acknowledge`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2; C-2, C-3 | tested on 212 traces; Kani pending |
| TX-CANCEL | `cancel`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; Kani pending |
| TX-SETTLE | `settle`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; Kani pending |
| TX-PAUSE | `set_paused`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; Kani pending |
| TX-OBSERVE | `observe`: exact result in guard order, exact post-state, frame | kani, tla, lean, prolog | REF-5, REF-5L, MC-2; C-2 | tested on 212 traces; Kani pending |
| TX-NOOP | Idempotent Ok paths change nothing, version included | kani, tla, lean, prolog | Lean `stepProps`; TLC TraceCheck; MC-2 | proved (model); tested; Kani pending |
| TX-VER | Every other Ok increments the version by exactly 1 | kani, tla, lean, prolog | Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |

### 5.3 Step properties

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| AUTH-1 | Effective submit and dispatch ⇒ caller = actor; cancel ⇒ actor or owner; settle ⇒ executor; pause and observe ⇒ owner | kani, tla, lean, prolog | Lean `exec_auth` (every Ok, no-ops included); TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending. F-4: actor = executor is accepted |
| STALE-1 | Submit Ok ⇒ request version = version; versions never repeat, so an accepted request cannot replay | kani, tla, lean, prolog | Lean `stale1_no_replay`, `version_mono_run`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |
| ADM-1 | Submit Ok ⇒ energy(post) ≤ energy(pre) | kani, tla, lean, prolog | Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |
| ADM-2 | Submit Ok in a violating state ⇒ energy(post + completion) < energy(pre) | kani, tla, lean, prolog | Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |
| HARD-STEP | Every Ok except observe: PV_i(post) ≤ PV_i(pre) for every metric | kani, tla, lean, prolog | Lean `stepProps`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |
| DEP-1 | Submit Ok ⇒ prerequisites met by Completed units | kani, tla, lean, prolog | Lean `dep1`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |
| LIFE-1 | Status graph Reserved → Dispatched or Cancelled, Dispatched → Active or Unknown, Unknown → Active, in flight → Completed or Cancelled; terminals absorbing; append-only; id, recipe, units and expiry immutable | kani, tla, lean, prolog | Lean `stepProps`; TLC `StepProperty`; C-3; MC-2 | proved (model); model-checked; tested; Kani pending |
| ASYNC-1 | Acknowledge never changes values; Active and Unknown keep the reservation | kani, tla, lean, prolog | Lean `stepProps`; TLC `StepProperty`; MC-2; RT-CALLBACK | proved (model); model-checked; tested; Kani pending |
| TERM-1 | The same terminal repeated is an Ok no-op; the opposite terminal is `InvalidState` (settle; cancel of a Completed record gives `Pending`, §4.3) | kani, tla, lean, prolog | Lean `term1`, `term1_cancel`; TLC invariant (error view); MC-2 | proved (model); model-checked; tested; Kani pending |
| OBS-1 | Observe Ok ⇒ no open record, config unchanged | kani, tla, lean, prolog | Lean `obs1`; TLC `StepProperty`; MC-2 | proved (model); model-checked; tested; Kani pending |
| PAUSE-1 | Paused ⇒ submit and dispatch have no effect; settle, ack, cancel and observe are unaffected | kani, tla, lean, prolog | Lean `pause1_blocks`, `pause1_transparent`; TLC `StepProperty` and the `WitStep_Paused*` witnesses; MC-2 | proved (model); model-checked; tested; Kani pending |

### 5.4 Invariants

These hold in every reachable state. Lean proves their conjunction `Inv`
with `inv_init`, `inv_step` and `reach_inv`.

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| INV-WF | Values have length n and are bounded; `records[j].id = j`; recipe in range; 1 ≤ units ≤ max_units; at most 256 records; config never changes | tla, lean, kani, prolog | Lean `reach_inv`; TLC MC_Safety and every trace state; MC-1, MC-2 | proved (model); model-checked; tested; Kani pending |
| INV-LEDGER | values = base + Σ reservations of records since k0 not Cancelled + Σ completions of Completed records since k0 | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-1, MC-2 | proved (model); model-checked; tested; Kani pending |
| INV-HARD | The envelope over the open records is computable and EV_i ≤ B_i | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-1, MC-2 | proved (model); model-checked; tested; Kani pending |
| INV-HEALTHY | B = 0 ⇒ every subset of open completions lands in bounds | tla, lean, kani, prolog | Lean `healthy`; TLC; MC-1, MC-2 | proved (model); model-checked; tested; Kani pending |
| INV-DEP | Every record's prerequisites are met by Completed records of lower index | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-1, MC-2 | proved (model); model-checked; tested; Kani pending |
| INV-VER | The version equals the number of effective transitions | tla, lean, kani, prolog | Lean `reach_inv`; TLC; MC-2 per edge | proved (model); model-checked; tested; Kani pending |

### 5.5 Reads

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| RD-PREVIEW | `preview.allowed` ⇔ `candidate` Ok; allowed and version < u32::MAX ⇒ submit Ok; no mutation, no panic | kani, near-tests, prolog | Prolog `preview_allowed` over a request grid (model only); near-tests: the shell's `preview` equals the core's after every SH-8 host call (the shell half) | partial: shell half tested, core half model only; Kani pending |
| RD-BEST | `best_quantity` is sound and minimal as documented | kani, prolog | Prolog `best_quantity` against brute force on small cases (model only) | partial: model only; Kani pending |

### 5.6 Liveness

| ID | Statement | Layer(s) | Evidence | Status |
|---|---|---|---|---|
| LIVE-1 | INV, B = 0 and version < u32::MAX ⇒ `settle(executor, id, true)` is Ok for every Dispatched, Active or Unknown record | lean, tla, prolog | Lean `live1` at every size; canary `Live1NoPremise.lean` fails to compile; TLC invariant in MC_Safety; Prolog on every trace state | proved (model); model-checked; tested |
| LIVE-2 | Every dispatched record eventually becomes terminal under executor fairness | tla, prolog | TLA-LIVE-F1 and TLA-LIVE-F2 violated; TLA-LIVE-1 holds on the completion path; MC-1 (dead records in `wedge`, release-blocked in `reliance`, none in `healthy`); traces 0 (F-1) and 209 (F-2) on the real core; RT-WEDGE | fails: F-1, F-2 |

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
| REF-1 | Guard exactness: the core's error is the TLA+ error operator's, so Ok exactly when the action is enabled | kani | `h_ref_*` (planned, §17.2) | pending (Kani layer) |
| REF-2 | Effect exactness: on Ok, the abstraction of the post-state is the TLA+ action's post-state | kani | `h_ref_*` (planned) | pending (Kani layer) |
| REF-3 | Rejected and idempotent calls stutter in the model | kani | `h_ref_*` (planned) | pending (Kani layer) |

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
| ASM-TOOLS | Scryer, TLC, Lean, Kani and the extractors are sound for what is used | assumption | canaries, witnesses and mutants in every runner; the Lean axiom audit | trusted (med) |
| ASM-SPEC | The specs, and the Prolog transcription of the docs, mean what we intend | assumption | `[review] spec_reviewer` (empty); the Prolog author had read the code (§8) | open: no reviewer (low) |
| ASM-MODEL | The small scopes are representative: Kani's bounds, TLC's universes and 32-bit integers, MC-1's universes | assumption | Lean at every size (model); traces at 256 records and ±1,000,000 | trusted (med) |
| ASM-LEAN-TLA | The Lean and TLA+ models transcribe the code | assumption | REF-5, REF-5L, MC-2, C-2; REF-1..3 pending | trusted (med); tested on 212 traces |
| ASM-COMPILE | `overflow-checks = true` in the release profile | assumption | `tools/scripts/check-pin.sh` (`release_overflow_checks = true`) | trusted (high); checked |

---

## 6. Kani on the real core

<!-- KANI: filled when the Kani layer lands -->

**Plan.** `projects/shared-pool/kani/` is a standalone crate whose only
dependency is `pool-core` from the mirror (Kani 0.68.0, CBMC 6.11.0).
Harness bodies are dual-mode, as in near-approval §6.1. Under Kani they
are symbolic (`kani::any`, `assume`), which is the proof. In plain
`cargo test` they run on random inputs: not a proof, but it takes seconds
and gates CI without Kani. There is one harness per transition contract
(TX-SUBMIT to TX-OBSERVE), checking TX-0, TX-NOOP, TX-VER and the step
properties on the same step. CFG, NUM and ROB harnesses cover `validate`,
`add` and `energy`; RD harnesses cover `preview` and `best_quantity`.
Every outcome has a cover that must be SATISFIED, the F-1 wedge included.
`h_canary` asserts a false property and must FAIL. Core mutants must be
killed under Kani and in plain mode. REF-1..3 reuse the step harnesses to
tie each TLA+ step to the real core (§17.2). Bounds, run times and results
will go in `kani/RESULTS.md`.

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

**Revisit** after PR #1 merges, upstream decides on F-1 and F-2, and Kani
is green, and only if "formally verified" will be claimed for the code
rather than the model.

---

## 8. Prolog

Results: `prolog/RESULTS.md`. Scryer Prolog 0.10.0. The final run
(2026-11-12, 212 traces) exits 0 in 332.4 s.

| File | Contents |
|---|---|
| `requirements/pool_req.pl` | 65 `requirement/3` facts, one per doc statement used; the api.md method table; `guard/5` (56 rows in the docs' order, each `doc`, `doc_condition` or `code_only`); the lifecycle table; constants; five fixtures with 23 claims; `finding/4` (F-1..F-6); 4 divergences; 8 ambiguities |
| `requirements/threat_model.pl` | 6 adversaries, 22 threats, 14 assumptions (§3) |
| `requirements/traceability.pl` | `property/3`, which is §5; `trace_row/2`, which maps requirements to properties |
| `model/pool_machine.pl` | `step/4`, written from the docs. It walks the guard table in order, so the model's behaviour is the requirement table. 16 places are tagged `CODE-ONLY`. Reads: `admissible/3`, `preview_allowed/3`, `best_quantity/4`. |
| `extract.py` → `extracted/` | Facts from the core and contract `lib.rs`, `fixtures.rs`, `SharedPool.tla` and `Props.tla`. A narrow parser that fails loudly on unknown constructs. `run.sh` fails on a regeneration diff. |
| `verification/`, `tests/`, `mutants/` | C-1..C-6, MC-1, MC-2 and the property checkers; four suites; 17 model, 2 requirements (r01, r02) and 9 code mutants |

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
- **Canaries and mutants.** Each of three suites exits 1 with only its
  canary failing. 28 of 28 mutants are killed (258.3 s summed).

**What it does not show.**
- **Independence (ASM-SPEC).** Unlike near-approval's M4, this layer's
  author had read the code. Doc-backed facts cite their line, and
  code-only facts are labelled, but no independent reviewer has checked
  either.
- **Bounds.** MC-1 has at most 3 records, 2 or 3 times, and fixed
  observation vectors. C-5's release search covers two records from each
  fixture's init state. RD-PREVIEW and RD-BEST are checked on the model
  only. C-2 skips five kinds of code error site that cannot fire from an
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
  transcribe the code, not a proof (ASM-LEAN-TLA). REF-1..3 (Kani,
  pending) will add a bounded proof per step.
- **Exits no trace reaches:** the version-overflow bump (the highest state
  version is 513); `settle(true)`'s add and envelope `Arithmetic`;
  submit's recovery add; release's envelope `Arithmetic`.
- **Not told apart:** exits of one kind (submit's two `Energy` exits).
  Of the core findings only F-5 has no trace (the version-overflow bump
  above).
- **Small random configs:** bounds within [−5, 10] and effects within ±3.

### 10.3 The chain and staleness

| Link | Checked by |
|---|---|
| docs ↔ code facts | C-1..C-4 (`extract.py`) |
| docs ↔ TLA+ guard order and edges | C-2, C-3 |
| Prolog `step/4`, TLA+, Lean ↔ real core | MC-2, REF-5, REF-5L (traces); REF-1..3 for TLA+ (Kani, pending) |
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
├── tools/scripts/      # check-pin.sh, check-status.sh (shared with near-approval)
└── projects/shared-pool/
    ├── strategy.md  status.toml  wasm-surface.expected
    ├── source-mirror/                   # submodule → shared-pool-controls @ pinned_commit
    ├── conformance/{src,traces}/        # generator; traces/core.txt checked in
    ├── kani/                            # §6, being built
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
| Unmerged pin | While `pinned_commit` is not on upstream `main`, no property goes past `in-progress`. The `pinned_commit` comment says it is a PR head. |
| Properties | The 83 non-ASM rows of §5, under `[modules.<m>.properties]`, one module per §5 subsection: `config_numerics` (§5.1), `transitions` (§5.2), `step_properties` (§5.3), `invariants` (§5.4), `reads` (§5.5), `liveness` (§5.6), `contract_shell` (§5.7), `executor` (§5.8), `runtime` (§5.9), `requirements` (§5.10), `tla_model` (§5.11), `lean_model` (§5.12) and `kani_refinement` (§5.13). IDs equal `traceability.pl`'s. `layer` is the first layer of the row's *Layer(s)* cell. `cross` holds the row's other layers, plus any other layer whose files carry the ID's `PROP:` tag. |
| Kani pending | Every property with `layer = "kani"` stays `unverified` until the Kani layer lands (§6), even where TLA+, Lean or Prolog already check it. Those results are in `cross` and `harness`. The §5.4 invariants list `tla` first, so TLC is their primary layer and they are `in-progress`. |
| Layer names | `near-tests/` carries `unit` (`shell.rs`, `executor.rs`, `wedge.rs`) and `difftest` (`store_diff.rs`, `traces.rs`). The surface check is `wasm-check`. The conformance generator is not a layer: each replay is recorded under the layer that runs it (REF-5 `tla`, REF-5L `lean`, MC-2 `prolog`, SH-8 `difftest`). REF-5 is `model-check`, a TLC run. REF-5L is a replay, test-class evidence (§5.12 says tested), recorded as `model-check` because `lean` allows no `test`; its `harness` says so. |
| False properties | LIVE-2 stays `unverified` with `finding = "F-1, F-2"`. SH-5 is `in-progress` with `finding = "NT-F1"`: it holds on the `--cfg near` build that §1 scopes, and is false on `scripts/build.sh`. Every row whose §5 Statement or Status cell names a finding carries `finding` too: the witnesses below, and the caveats on AUTH-1, SH-3 and SH-10. status-lint ignores the key; it is for readers. |
| Finding witnesses | TLA-LIVE-F1, TLA-LIVE-F2, LEAN-WIT, RT-WEDGE and C-5's known findings pass while their finding reproduces. When upstream fixes one, its witness fails as stale. Invert it into the property it guarded; do not delete it. |
| `[assumptions.<ID>]` | The 14 rows of §5.14. `statement` is §5.14's; `level` is `threat_model.pl`'s, the same as §5.14's. `checked_by` lists properties only: those of `assumption_checked_by/2` and of §5.14's *Evidence* cell that have a result. Pending ones (REF-1..3 for ASM-LEAN-TLA) are named in `observed`, as is a check that is not a property (`check-pin.sh`, the wasm surface). `source` cites the NEAR pages near-approval read, or the upstream docs as `spec:<line>`. |
| Property `assumptions` | The ASMs the row's claim rests on: its tools and models (TOOLS, SPEC, MODEL, LEAN-TLA), the runtime behaviour it relies on, and the environment it assumes (TIME for MC-1 and LIVE-2, which cites MC-1; an honest executor, EXEC, for LIVE-2, TLA-LIVE-F2 and MC-1's release-blocked states). Where a §3.2 threat's residual is an ASM, every property that mitigates the threat lists it: EXEC on ASYNC-1, RT-CALLBACK, SH-3 and INV-LEDGER (T-UNKNOWN), OWNER on OBS-1 and INV-WF (T-OBS). The in-bounds observations of LIVE-1, TLA-LIVE-1 and TLA-LIVE-F2 are premises of those claims, not OWNER. No property lists DEPLOY: T-REDEPLOY's only mitigation is the assumption itself, and no §5 row checks a deployment (§9.3). |

---

## 13. Milestones

| # | Deliverable | State |
|---|---|---|
| M0 | Submodule at the PR #1 head; `status.toml` with 16 `[source_hashes]` and `release_overflow_checks`; conformance generator and traces | Done |
| M1 | Kani on the real core (§6) | Being built |
| M1.5 | TLA+ (§17) | Done, except TLA-IND (open) and REF-1..3 (wait for M1) |
| M1.6 | Lean (§18) | Done |
| M3 | Shell: `near-tests/`, wasm surface | Done |
| M4 | Prolog (§8) | Done |
| M5 | Verus | Deferred (§7) |
| M6 | Sandbox | Done, on one shard |
| M7 | Deployment | Out of scope |
| CI | `.github/workflows/shared-pool.yml` (§14) | Green on PR #31 (run 43194245726); Kani jobs added with the layer |

**Next, in order.**
1. Land the Kani layer: harnesses, covers (F-1 among them), canary,
   mutants, REF-1..3.
2. Report F-1..F-6, NT-F1..NT-F4 and the two doc divergences on PR #1.
3. When PR #1 merges, re-pin to the merge commit: regenerate the traces,
   recompute the hashes, rerun every layer, and update the findings.
4. A named reviewer who wrote neither `pool-core` nor the models signs off
   the specs (`[review] spec_reviewer`).

Closed from this list: pointing C-6 at §5 instead of the brief (§5); a
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
`workflow_dispatch` with `sandbox: true`.

| Job | Runs | Fails on |
|---|---|---|
| `pin` | `tools/scripts/check-pin.sh shared-pool` | gitlink ≠ `pinned_commit`; `[source_hashes]` drift; no `overflow-checks = true`. Every job but `status-lint` needs it. |
| `status-lint` | `tools/scripts/check-status.sh shared-pool` | evidence not allowed for its layer; a status without its artifact; a status above its ceiling |
| `conformance` | `cargo run --release --locked -- --check traces/core.txt` | the checked-in traces differ from the generator's output |
| `tla` | `tla/run.sh safety liveness trace` (about 10 min), then `run.sh mutants` | a check failing; a witness or required violation passing; a mutant surviving |
| `lean` | `lean/run.sh` (about 4 min) | a `sorry` or forbidden construct; an extra axiom; a canary compiling; a REF-5L difference; a mutant surviving |
| `prolog` | `prolog/run.sh` (about 5.5 min) | a suite failing; a loader warning; extraction drift; a canary passing; a mutant surviving |
| `near-unit` | `near-tests/run.sh all`: the PROP-tag check, tests, surface, and the 21 mutants (about 9 min) | a tag problem (`check-tags.py`); a test failing; lockfile drift; a surface diff (SURF-2 stays expected-fail); a mutant surviving |
| `sandbox` | `sandbox/run.sh` (about 7 min warm) | any failure; lockfile drift |
| `plain`, `kani` | Not in the workflow yet; added when the Kani layer lands. The harness bodies in random mode, and the Kani harnesses (§6). | any failure; an unsatisfied cover; `h_canary` passing |

---

## 15. Risks

| Risk | Mitigation |
|---|---|
| The pin is a PR head. A force push can make it unreachable, and the merge can differ from it. | Re-pin at merge (§13). `pin` fails loudly if the commit cannot be fetched. |
| A fix for F-1 or F-2 changes admission or release. | Every model follows the code's guard order, and the traces regenerate from the core. Witnesses flip and must be inverted (§12). |
| Three hand-written models share a transcription error. | All replay the same real-core traces; C-2 compares guard orders; every layer has mutants; REF-1..3. |
| The Prolog author read the code (ASM-SPEC). | Doc citations on every fact; a named independent reviewer. |
| Kani is slow on `Vec`-heavy state. | Small bounds per function; plain mode in CI; one harness per transition. |
| TLC's 32-bit integers | Overflow aborts a run, so no run passes silently. Lean covers large values, and Kani will once it lands. |
| One-shard sandbox | RT-RACE records what one shard cannot show. The models treat ack and settle as independent steps. |
| The import surface cannot exclude code replacement (NT-F3). | Source review and dynamic absence. Deployment stays out of scope. |
| TLC memory on a GitHub-hosted runner. | Closed: at `TLA_HEAP=5g` the `tla` job passed safety (2,306,738 states, 1,300 s), liveness, trace and all 31 mutants on PR #31's first run. Peak RSS not recorded. |

---

## 16. Open questions

| # | Question |
|---|---|
| OQ-1 | Re-pin to the merge commit when PR #1 merges. If the PR is abandoned, do we keep verifying a commit that is not on `main`? |
| OQ-2 | F-1 and F-2 are upstream's call. Options: refuse a hedge whose completion re-violates a metric its own reservation cured; allow a nonexecution release after a completed sibling relied on it; or stop counting unexecuted reservations as headroom. Each layer's witness flips with the fix. |
| OQ-3 | NT-F1: build with cargo-near or `--cfg near`, and have upstream's sandbox tests assert failure messages. |
| OQ-4 | NT-F3: is source review plus dynamic absence enough for the 15 linked host functions, or is a static call graph of the wasm needed? |
| OQ-5 | F-4: should `validate` reject actor = executor, and an actor or executor that is the owner? |
| OQ-6 | F-3: a per-actor record cap, pruning on observe, or a documented limit? F-6: a refresh path that does not need every record terminal? |
| OQ-7 | TLA-IND: rewrite the model for Apalache, or accept LEAN-IND as the every-size safety result? |
| OQ-8 | L-1b: confirm with upstream that a reservation that cured a violation is meant to be uncancellable. |
| OQ-9 | Docs: update spec:39 and api:26 for the no-op acknowledgment, and api:34 for non-string results (NT-F4); state a minimum prepaid gas per method in api.md (none is given). Measured at the maximum-size state (§9.2, RES-1): `dispatch` needs at least 70 Tgas, `reconcile` 46 Tgas and the executor's `finish` 43 Tgas; 70 Tgas leaves under 1 Tgas spare for `dispatch`, so the documented figure needs headroom. |
| OQ-10 | Who reviews the specs? |

---

## 17. TLA+ over every event sequence

Kani, once it lands, will prove one step of the real core within bounds.
That says nothing about liveness or safety at depth. The TLA+ model is checked over all event
sequences in small universes, and tied to the real core by the traces
(REF-5) and, once Kani lands, step by step (REF-1..3). Results:
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

<!-- KANI: filled when the Kani layer lands -->

**Plan.** The Kani crate will hold α (a `Pool` mapped to the TLA+
variables), plus the error operators and actions transcribed in Rust.
REF-1 (guard exactness): the core's error equals the TLA+ error
operator's, so the core is Ok exactly when the action is enabled. REF-2
(effect exactness): α of the post-state equals the action's post-state.
REF-3: a rejected or idempotent call leaves α unchanged. The `h_ref_*`
harnesses reuse the step harnesses' generators, so they share the same
bounds. Until they land, REF-5 is the only link from this model to the
code.

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
  residuals (NUM-1) is Kani's job.
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
  `Arithmetic` error is not modelled (claimed unreachable). The envelope's
  fail-on-first partial sums are modelled by the final sums: argued, not
  proved.
- **Types.** Times, units and versions are unbounded `Nat`. u64
  `saturating_add` and the u32 version overflow are exact. `max_age`'s
  u32 type and all strings are not modelled.
- **Panics (ROB-1).** Not modelled. `Inv` shows every index the guards
  read is in range, but not that the Rust never panics.
- **Not stated in Lean:** RD-PREVIEW, RD-BEST and the shell. LIVE-2
  (LIVE-1 is its per-state half, and `f1_forever` its counterexample).
  TX-SUBMIT..TX-OBSERVE as separate theorems: they are the model's
  definitions plus REF-5L.
