# shared-pool near-tests: results

Shell layer of the shared-pool verification (near-approval strategy.md
section 9 pattern). Target: difflabai/shared-pool-controls PR #1 head
`a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7` (`../source-mirror`); contract
`crates/contract/src/lib.rs` sha256 `6ee32c1e…9784`, executor
`crates/executor/src/lib.rs` `917d0dcc…05c5`, core `9a4eb36c…05c4`.
Toolchain 1.98, near-sdk 5.29.1 (`unit-testing`), mocked runtime =
near-vm-runner 0.37.4 `VMLogic`.

Run: `./run.sh test | surface | mutants` (or `./run.sh` for all three).

## How the shell is exercised

- **Host path**: the `#[near]` methods called as Rust functions. Every call
  starts from storage (`state_read`, Borsh) and ends with `state_write` on
  success; a panic discards every write and receipt.
- **Wasm path**: the real wasm, run by the wasmi 2.0 interpreter with every
  `env` import forwarded to the same mocked `VMLogic`. This covers the code
  near-sdk generates only for wasm32: `#[init]` (init once), `#[private]`,
  the nonpayable deposit checks, JSON argument/return encoding and
  `#[callback_result]`. Two builds:
  - `Plain`: `cargo build --target wasm32-unknown-unknown --release --locked`,
    exactly upstream `scripts/build.sh`;
  - `Near`: the same with `RUSTFLAGS="--cfg near"`, as cargo-near builds.
  Any import other than the ones the shell uses (deploy, delete, add-key,
  transfer, stake, global-contract, ...) traps as a forbidden host call;
  every wasm call asserts none happened.
- **Receipt router** (`Net`): pool and executor wasm side by side; outgoing
  receipts run FIFO, a callback gets its dependency's result. Used for
  `dispatch -> execute -> on_result`, `reconcile -> status -> on_result`,
  `finish/confirm_not_executed -> settle`.
- Expected values come from `pool_core::Pool` (same pinned crate) and from
  docs/api.md, never from the contract's output.
- `Cargo.lock`: `tests/lockfile.rs` checks the 280 packages of the code under
  test resolve exactly as in the mirror's lockfile; the only extra packages
  are wasmi and its 8 dependencies (harness only).

## Test suite (`./run.sh test`, 29 tests, ~30 s wall)

| File | Properties | What |
|---|---|---|
| `tests/shell.rs` (14) | SH-1..SH-7, SH-9, SH-10, NT-F1, NT-F2 | exact scenarios on host + both wasm builds |
| `tests/store_diff.rs` (2) | SH-8 (+SH-4, SH-5, SH-9) | 2,000 x 40 random calls on the host path (fixtures, wedge, open, random configs), Borsh reload every call, results, panic messages, events, receipts, stored bytes and views (get_pool, get_commitments edges, preview) every call; 300 x 40 per wasm build with JSON views every 4 calls; coverage of 46 required outcomes |
| `tests/traces.rs` (1) | SH-8, F-1 | all 209 conformance traces (8,771 calls, incl. `Arithmetic`, `Full` and release `Arithmetic` in traces 206-208) replayed through the shell on host + both wasm builds: every result and post-state equals the trace |
| `tests/executor.rs` (8) | EX-1..EX-5 | executor alone on host + both builds (state checked against a Borsh mirror), executor wrappers, end-to-end normal/reject/unknown/panic flows through the router, settle-before-callback race |
| `tests/wedge.rs` (3) | F-1 | F-1 through the shell (host + both builds), control without the disturbing observe, F-1 end to end with the executor |
| `tests/lockfile.rs` (1) | TCB | lockfile equality |

Last run (2026-11-11): all 29 pass. Coverage of the default SH-8 host run
(80,000 calls) includes every submit reason except Full and Arithmetic
(unreachable within 40 calls / values of +-1000; both are covered by
`sh4`/`sh5` on crafted states), every dispatch/settle/cancel/observe error,
reconcile NotFound/InvalidState/Ok, and every on_result outcome class
including `completed:Bounds` and `cancelled:Bounds` (F-1 shapes).

## Property results

| ID | Result | Evidence |
|---|---|---|
| SH-1 | pass | `sh1_caller_is_the_predecessor_not_the_signer` (relayed calls by `relay.near` signed by the actor are the relay's; every method), `sh1_now_is_the_block_timestamp_in_whole_seconds` (149.999999999 s is second 149; expiry/horizon/observed_at), 15% relayed calls in SH-8; mutants m02, m10 |
| SH-2 | pass | `sh2_new_is_private_and_initialises_once`: `new` by any other predecessor fails (`Method new is private`) before reading input; by the pool stores exactly Borsh(`Pool::new`); a second `new` fails (`The contract has already been initialized`) without writing; uninitialised reads fail; invalid config/account names fail; mutant m09 |
| SH-3 | pass | `sh3_on_result_is_private` (5 foreign predecessors, before input/promise result are read), `sh3_on_result_maps_the_status_string` (completed/cancelled/active/unknown/garbage/""/"Completed"/" completed"/PromiseError from Dispatched, Unknown, Active, terminal), `sh3_non_string_promise_results_fail_the_callback` (NT-F4); mutants m01, m03, m04, m08, m14 |
| SH-4 | pass | `sh4_rejected_submit_returns_the_decision_and_writes_nothing`: 15 rejection cases (every reason incl. Full at 256 records, Arithmetic, disturbed-state Energy) return the exact core decision, `id: null`, a `decision` event, and identical state bytes; admitted submits return the core id; mutant m13 |
| SH-5 | finding (NT-F1) | host path and `--cfg near` wasm: every core error of every method panics with exactly the error string and changes nothing (`sh5_core_errors_are_panics_with_the_error_string`, SH-8). The documented build (`scripts/build.sh`) reports no message at all: NT-F1 |
| SH-6 | pass | `sh6_dispatch_promise_shape`: `execute{id,recipe,units}` to the recipe's executor, 30 Tgas, 0 deposit, then `on_result{id}` to the pool, 30 Tgas, depending on it; the callback promise is returned; no event; mutant m11 |
| SH-7 | pass | `sh7_reconcile_guard_and_promise_shape`: NotFound / InvalidState for Reserved, Completed, Cancelled; `status{id}` 10 Tgas then `on_result` for Dispatched/Unknown/Active, by anyone, no state write; mutants m05, m15 |
| SH-8 | pass | `sh8_store_diff_host` (80,000 calls), `sh8_store_diff_wasm` (12,000 calls per build), `conformance_traces_through_the_shell` (8,771 calls x 3 paths) |
| SH-9 | pass | `sh9_views_and_paging_at_256_records`: 12 x 7 (from, limit) edge pairs at 256 records incl. u32::MAX, JSON views on wasm; views every call in SH-8; mutant m06 |
| SH-10 | pass (NT-F2) | `sh10_mutating_methods_reject_attached_deposits`: `new`, `submit`, `dispatch`, `settle`, `cancel`, `set_paused`, `observe`, `on_result` reject 1 yocto and 1 NEAR (`Method X doesn't accept deposit`) before reading input; mutant m12. `reconcile` (a `&self` call method) accepts and keeps a deposit: NT-F2 |
| EX-1 | pass | `ex1_only_the_lock_executes` (6 foreign predecessors incl. signer = lock), `ex1_executor_wrappers` (new private, init once, deposits); mutant m17 |
| EX-2 | pass | `ex2_payload_binding_and_dedupe`: replay returns the recorded status in every mode without a second job, other payload `payload mismatch`, modes reject/unknown/panic, `full` at 256 jobs; mutants m16, m21 |
| EX-3 | pass | `ex3_only_the_operator_attests`: finish/confirm/set_mode by 5 other predecessors fail; invalid modes fail; mutant m18 |
| EX-4 | pass | `ex4_terminal_conflict_rejected`: same outcome idempotent (re-notifies), opposite outcome `terminal outcome conflict`, unknown job, `job exists`; mutant m19 |
| EX-5 | pass | `ex5_notify_calls_lock_settle`: `settle{id,completed}` to the lock fixed at init, 40 Tgas, 0 deposit; end-to-end flows; mutant m20 |
| F-1 | finding (reproduced) | `wedge.rs` and trace 0: see below |

## Findings

**NT-F1 (medium): the documented build drops every failure message.**
`scripts/build.sh` builds without `--cfg near`. near-sdk 5.29.1 then
compiles its pure-Rust fallbacks, where `env::panic_str` is `eprintln!` +
`panic!()` instead of the `panic_utf8` host call; the wasm does not even
import `panic_utf8` (`../wasm-surface.expected`). Every failure (core errors
through `must`, `#[private]`, deposit and init checks, `expect`/`assert!`,
argument errors) becomes a bare `unreachable` trap. State is still reverted
and every access check still fails closed (all shell tests pass on the
Plain build with "no message" expected), but clients cannot tell
`Unauthorized` from `Bounds` from `Stale`, and the sandbox tests, which only
check `is_failure()`, cannot notice. The `--cfg near` build reports
`Smart contract panicked: <error>` as the docs assume.
Reproducer: `cargo test --locked --test shell nt_f1_upstream_build_drops_every_panic_message`
(plain build: `observe` by z.near traps "wasm `unreachable` instruction
executed" with no panic message; near build: panic message `Unauthorized`).
Fix: build with cargo-near or `RUSTFLAGS="--cfg near"`.

**NT-F2 (low): `reconcile` accepts and keeps attached deposits.** It is a
`&self` method, so near-sdk generates no deposit check (the views neither).
api.md: "All mutating methods are nonpayable". The outgoing calls carry 0,
so the deposit stays with the pool. Reproducer:
`cargo test --locked --test shell nt_f2_reconcile_accepts_and_keeps_an_attached_deposit`.

**NT-F3 (informational): the wasm imports deploy, delete-account,
add-key, transfer, stake, gas-key and global-contract host functions**
(15 per file, both contracts, both builds), linked by near-sdk's generic
`Promise` action code. Source review shows only `function_call` actions are
built, and no wasm call in this suite (more than 50,000) reached one (each would
trap as forbidden), but the import surface alone cannot rule out an escape
hatch the way it does for near-approval. `wasm-surface.sh` records them
(SURF-2 expected-fail).

**NT-F4 (low): a promise result that is not a JSON string fails the
callback.** api.md: "Runtime failures and unexpected strings become Unknown
in the wrapper". Unexpected strings do; a non-string JSON value or invalid
JSON makes `#[callback_result]` panic (`Failed to deserialize callback using
JSON`), so the record stays where it was (e.g. Dispatched) instead of
Unknown. The pinned executor always returns strings; a production adapter
returning e.g. an object would leave records Dispatched (reconcile retries
the same failure; the executor's `settle` still works). Reproducer:
`cargo test --locked --test shell sh3_non_string_promise_results_fail_the_callback`.

**F-1 (brief) reproduced through the shell.** `wedge.rs`: after `observe
[12,5]`, the hedge is admitted (values [10,5]), dispatched, and from each of
Dispatched, Unknown and Active: `settle(true)` and `settle(false)` fail
`Bounds`, `on_result` "completed"/"cancelled" record `error: "Bounds"`,
`cancel` and `observe` fail `Pending`, version unchanged. End to end with
the executor (both builds): the operator's `finish(0, true)` succeeds at
the executor (job "completed") but its `settle` receipt fails `Bounds` at
the pool, so the executor and the lock disagree permanently; `finish(0,
false)` then fails `terminal outcome conflict`, `reconcile` reads
"completed" and records `Bounds`. Control: the same recipe from the
undisturbed baseline settles. Trace 0 replays identically on all paths.

Observations (not findings): a rejected `submit` rewrites `STATE` with the
same bytes (a `&mut self` method; costs gas only); `dispatch`/`reconcile`
call `value_return("null")` before `promise_return` (near-sdk's Promise
serialization; the promise wins); outgoing calls use static gas (weight 0);
anyone's `reconcile` can bump a record's version at most twice
(Dispatched -> Unknown -> Active), bounded.

## Wasm surface (`./run.sh surface`)

`wasm-surface.sh` builds both builds and compares with
`../wasm-surface.expected`: SURF-1 (exports and imports with class
promise/forbidden/other) passes; SURF-2 (no forbidden imports) fails with
exactly the recorded imports (NT-F3) and is reported as expected-fail.
pool_contract exports: `new get_pool get_commitments preview submit dispatch
reconcile on_result settle cancel set_paused observe contract_source_metadata`
and memory. promise imports: `promise_and promise_batch_create
promise_batch_then promise_batch_action_function_call(_weight)
promise_result promise_return` (executor: no `promise_result`).
`panic_utf8`: imported only by the `--cfg near` build (NT-F1).

## Mutants (`./run.sh mutants`)

Unpatched control: passes. 21 mutants (15 of `crates/contract/src/lib.rs`, 6 of
`crates/executor/src/lib.rs`), each applied with `patch -p1` to a temporary
copy of the source; both wasm builds are rebuilt before the suite runs
(host store_diff 300 x 40, wasm 40 x 40 per build). Last run 2026-11-11:
**21/21 killed**, 9 min.

| Mutant | Crate | Change | Verdict | Failing tests |
|---|---|---|---|---|
| m01_on_result_not_private | contract | SH-3: on_result accepts any predecessor | killed | `sh3_on_result_is_private` |
| m02_caller_is_signer | contract | SH-1: caller() is the signer instead of the predecessor | killed | `sh1_caller_is_the_predecessor_not_the_signer`, `sh8_store_diff_host`, `sh8_store_diff_wasm` |
| m03_swap_completed_cancelled | contract | SH-3: on_result maps completed and cancelled to the opposite settlement | killed | `ex5_end_to_end_normal_reject_unknown_panic`, `ex5_settle_before_callback_is_absorbed`, `sh3_on_result_maps_the_status_string` (+2) |
| m04_unknown_settles_cancelled | contract | SH-3: an "unknown" status is treated as definitive non-execution | killed | `conformance_traces_through_the_shell`, `ex5_end_to_end_normal_reject_unknown_panic`, `ex5_settle_before_callback_is_absorbed` (+5) |
| m05_reconcile_without_status_guard | contract | SH-7: reconcile no longer refuses records that are not in flight | killed | `sh7_reconcile_guard_and_promise_shape`, `sh8_store_diff_host`, `sh8_store_diff_wasm` |
| m06_get_commitments_limit_100 | contract | SH-9: get_commitments pages up to 100 records | killed | `sh9_views_and_paging_at_256_records` |
| m07_settle_emits_no_event | contract | SH-5/SH-8: settle forgets its "settled" event | killed | `conformance_traces_through_the_shell`, `ex5_settle_before_callback_is_absorbed`, `f1_control_without_the_disturbing_observe` (+5) |
| m08_on_result_promise_error_is_active | contract | SH-3: a failed execute (PromiseError) acknowledges the record as Active | killed | `conformance_traces_through_the_shell`, `ex5_end_to_end_normal_reject_unknown_panic`, `ex5_settle_before_callback_is_absorbed` (+5) |
| m09_new_not_private | contract | SH-2: anyone may initialise the pool | killed | `sh2_new_is_private_and_initialises_once` |
| m10_now_rounds_up | contract | SH-1: now() rounds the block timestamp up to the next second | killed | `conformance_traces_through_the_shell`, `ex5_settle_before_callback_is_absorbed`, `f1_control_without_the_disturbing_observe` (+17) |
| m11_execute_sent_to_actor | contract | SH-6: dispatch sends execute to the recipe's actor instead of its executor | killed | `conformance_traces_through_the_shell`, `ex5_end_to_end_normal_reject_unknown_panic`, `ex5_settle_before_callback_is_absorbed` (+15) |
| m12_submit_payable | contract | SH-10: submit accepts an attached deposit | killed | `sh10_mutating_methods_reject_attached_deposits` |
| m13_submit_ignores_preview | contract | SH-4/SH-5: submit tries the core directly and swallows its error (the version-overflow panic is lost) | killed | `sh5_core_errors_are_panics_with_the_error_string` |
| m14_on_result_panics_on_core_error | contract | SH-3/SH-5: on_result panics on a core error instead of reporting it in the event | killed | `f1_wedge_end_to_end_with_the_executor`, `f1_wedge_through_the_shell`, `sh8_store_diff_host` (+1) |
| m15_reconcile_status_gas_30 | contract | SH-7: reconcile attaches 30 Tgas to status instead of 10 | killed | `f1_wedge_through_the_shell`, `sh7_reconcile_guard_and_promise_shape`, `sh8_store_diff_host` (+1) |
| m16_executor_dedupe_dropped | executor | EX-2: execute no longer deduplicates a replayed id (a second job is pushed) | killed | `ex2_payload_binding_and_dedupe`, `ex4_terminal_conflict_rejected` |
| m17_executor_lock_is_signer | executor | EX-1: execute checks the signer, not the predecessor | killed | `ex1_only_the_lock_executes` |
| m18_executor_set_mode_unguarded | executor | EX-3: anyone may set the executor's mode | killed | `ex3_only_the_operator_attests` |
| m19_executor_terminal_conflict_dropped | executor | EX-4: finish may replace a terminal outcome with the other one | killed | `ex4_terminal_conflict_rejected`, `f1_wedge_end_to_end_with_the_executor` |
| m20_executor_notify_inverted | executor | EX-5: notify reports the opposite outcome to the lock | killed | `ex5_end_to_end_normal_reject_unknown_panic`, `ex5_notify_calls_lock_settle` |
| m21_executor_payload_unbound | executor | EX-2: a replayed id with another payload returns the recorded status | killed | `ex2_payload_binding_and_dedupe` |

## Gaps

- The mocked runtime is not the real NEAR runtime: gas, storage staking,
  receipt timing across blocks and the real promise-result plumbing are the
  sandbox layer's (RT-*). The router runs receipts FIFO in one block; the
  settle-before-callback race is covered on the pool side only
  (`ex5_settle_before_callback_is_absorbed`).
- NT-F3: no static proof that the forbidden host functions are unreachable
  (only source review and dynamic absence).
- SH-8 random configurations are small (1-3 metrics, 1-3 recipes, values
  near +-10); Full and Arithmetic are covered only by crafted states.
