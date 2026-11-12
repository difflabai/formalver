# shared-pool sandbox layer: results

Runtime evidence on the real wasm. `pool_contract.wasm` and `pool_executor.wasm`
are built from the pinned source mirror (a4bb5c3c, clean). They run in a local
near-sandbox 2.13.4 through near-workspaces 0.23.0, the versions upstream
`crates/sandbox` pins. Evidence class: **test** (near-approval strategy §12).
Every test also keeps a host-side `pool_core::Pool` in step with the chain. That
is the real core, used as an oracle. After each step the test compares the whole
`get_pool` state with it, so the tests cover the shell and core together, not
the shell alone.

Runner: `projects/shared-pool/sandbox/run.sh`. Exit 0 means every check passed.
It runs these steps in order:

1. `scripts/check-lock.py`. The sandbox `Cargo.lock` was seeded from the mirror's
   lockfile, and all 342 shared registry packages match it.
2. `scripts/build-wasm.sh`, which builds two variants:
   - **upstream**: exactly upstream `scripts/build.sh`.
   - **cfg-near**: the same build plus `RUSTFLAGS="--cfg near"`, which is the
     cfg cargo-near sets.
3. `scripts/build-res.sh`, which builds the helper contract `relay/`.
4. `scripts/sandbox-bin.sh`, which supplies a sha256-checked near-sandbox binary.
5. `tests/runtime.rs` on both variants, then `tests/resources.rs` (RES-1) on both
   variants.

Each test writes its observations to `results/<variant>/<ID>.json`.

## Artifacts under test (`results/wasm.json`)

All builds use rustc 1.98.1 (48a229cea 2026-09-01), `cargo build --target
wasm32-unknown-unknown --release --locked`, and the mirror's release profile:
opt-level z, LTO, panic=abort, overflow-checks=true. Each variant has its own
`CARGO_TARGET_DIR` (`target/pool`, `target/pool-near`).

| variant | wasm | sha256 | bytes |
|---|---|---|---|
| upstream | pool_contract | `8ddc9280c63157636fede6f201ebff30ef528307092ad21914730c00df380f7c` | 393744 |
| upstream | pool_executor | `ca76c3caf0505ab7fdb43ab3ecaef6234472eec94bb4256679e69c5a4785b0e5` | 237589 |
| cfg-near | pool_contract | `af617a8f00a10d0a049fb8092ae2f22463204faf71cf770a1b166d2c5b903c02` | 389435 |
| cfg-near | pool_executor | `760618725144241959be7c0b7a432c413d16b156a0a4aec7c875940c65b74cc6` | 233200 |

Rebuilding gives the same hashes.

## Properties

Every property row ran on **both** variants. The two variants differ only in the
failure text, as SB-1 describes. Wherever the cfg-near build asserts an exact
panic message, the upstream build asserts the bare `unreachable` trap in its
place. Both builds assert that the call fails and that storage is unchanged.

| ID | test (`PROP:` tag) | outcome | what it shows |
|---|---|---|---|
| RT-PRED | `rt_pred_relay_is_the_caller` | pass | See [RT-PRED](#rt-pred). |
| RT-PRIVATE | `rt_private_new_and_on_result` | pass | See [RT-PRIVATE](#rt-private). |
| RT-CALLBACK | `rt_callback_status_mapping` | pass | See [RT-CALLBACK](#rt-callback). |
| RT-REVERT | `rt_revert_core_errors_write_nothing` | pass | See [RT-REVERT](#rt-revert). |
| RT-RACE | `rt_race_settle_before_callback`, `rt_race_executor_key_settles_while_callback_in_flight`, `rt_race_operator_finish_vs_callback` | pass (the operator-`finish` form cannot occur on one shard; see the [RT-RACE](#rt-race) section) | See [RT-RACE](#rt-race). |
| RT-WEDGE | `rt_wedge_f1_end_to_end` | **finding F-1 reproduced** | See [RT-WEDGE](#rt-wedge). |
| RES-1 | `res_1_gas_at_max_state` | pass | See [RES-1](#res-1). |
| (SB-1 witness) | `sb1_upstream_build_loses_panic_messages` | **finding SB-1 reproduced** | Both builds side by side; see Findings below. |

### RT-PRED

- An actor signs `relay.forward(submit)`. The pool attributes the call to the
  relay: the decision event's `actor` is the relay, the result is
  `Unauthorized`, and storage is byte-identical.
- The same request sent directly by the actor is accepted.
- When the relay is a recipe's actor, a forward signed by an unrelated account
  is accepted as the relay's submit.
- `dispatch`, `cancel`, `settle` (even when signed by the executor's key),
  `set_paused` and `observe` (signed by the owner) are all rejected
  `Unauthorized` when they go through the relay. None of them writes anything.

### RT-PRIVATE

- `pool.new` fails "Method new is private" for the owner, the actor, an
  unrelated account and the executor.
- It also fails through the relay when the transaction is signed with the pool's
  own key.
- `exec.new` behaves the same way.
- A second `new` by the contract's own account fails "The contract has already
  been initialized".
- `on_result` fails "Method on_result is private" for four foreign callers and
  for the relay. The target is an Unknown record, so a forged callback that got
  through would change its state.
- On the pool's own key, `on_result` passes the private check but fails with the
  host error "Accessed invalid promise result index: 0", because a transaction
  carries no promise result.
- Storage is unchanged in every case.

### RT-CALLBACK

Each row is executor mode → result of `execute` → effect on the record.

- **normal** → "active" → Active. The reservation is kept (ASYNC-1).
- **reject** → "cancelled" → `settle(executor, false)` → Cancelled. The
  reservation is released exactly.
- **unknown** → the executor stores the job but returns "unknown" → Unknown.
  - `cancel` then fails Pending.
  - `reconcile`, which anyone may call, reads "active" → Active. Repeating it is
    a no-op that does not even bump the version.
- **panic** → `execute` fails "injected failure" → the callback sees a
  `PromiseError` → Unknown. The dispatch transaction itself succeeds and the
  reservation is kept.
  - `reconcile` reads "unknown", which is a no-op.
  - `confirm_not_executed` releases the reservation.
- Repeating the same terminal through `finish` is idempotent (TERM-1).

### RT-REVERT

Ten core errors through the wasm all panic. For each one the pool's raw storage
is byte-identical before and after, and the transaction emits no event:

- Unauthorized, NotFound and InvalidState on `dispatch` and `settle`
- Unauthorized and Pending on `cancel`
- Unauthorized on `set_paused`
- Pending on `observe`

The same holds for these further cases:

- Paused on `dispatch`.
- Bounds on `observe`, with three different bad inputs.
- Arithmetic at `version = u32::MAX` (the state is patched in) for `set_paused`
  and for `submit`.

Rejected submits (Paused, Stale, InvalidUnits, Unauthorized) do not panic. They
return a decision, emit one `decision` event and write nothing.

### RT-RACE

Three tests cover the race:

1. **Settle before the callback (deterministic).** The executor is the helper
   contract `relay/`, which runs `settle` from inside `execute`.
   - NEAR emits the receipts a function creates before the data receipt that
     carries its return value. So on one shard `settle` lands first, every time.
   - The late "active" ack is a no-op: the version moves by `+2` (dispatch,
     settle), where the callback-first order would give `+3`.
   - This holds for `settle(true)` and for `settle(false)`.
   - It also holds for a stale `reconcile` read (`+1`). Reconciling a terminal
     record fails InvalidState.
2. **Timed race with the upstream executor contract.** The executor account's
   own key signs `settle` 0–400 ms after `dispatch` is broadcast. Every serial
   order the core allows was observed:
   - settle before dispatch: rejected with InvalidState
   - dispatch, settle, callback: the late ack is ignored (the order the property
     targets)
   - dispatch, callback, settle

   The block heights are recorded. The test fails if the late-ack order never
   occurs.
3. **Timed race with the operator's `finish`, the path the property names.**
   There are only two outcomes:
   - "finish before execute": `finish` is rejected with "unknown job".
   - "callback first, then finish→settle".

   On one shard the notify cannot overtake the callback. `finish` needs the job
   that `execute` creates, and `execute`'s data receipt is emitted first. This is
   a gap, not a failure (see below). The test only requires that every outcome is
   a serial order.

### RT-WEDGE

F-1 end to end on the wasm, using the brief's configuration: `observe [12,5]`,
submit 1, dispatch → Active, then `finish(completed)`.

- The executor commits its job as "completed", but its notify `settle(true)`
  fails Bounds. The pool record stays **Active**.
- After that, nothing closes the record:
  - `reconcile` succeeds without a panic and only reports `error: "Bounds"` in
    its event.
  - The executor cannot change its answer: `finish(cancelled)` fails "terminal
    outcome conflict" and `confirm_not_executed` fails "job exists".
  - Repeating `finish(completed)` fails Bounds.
  - The executor key's `settle(true)` and `settle(false)` both fail Bounds.
  - `cancel` fails Pending for both the actor and the owner.
  - `observe` fails Pending for every input tried.
- After `fast_forward(200)` blocks the result is the same: observe stays Pending,
  reconcile still reports Bounds, and settle still fails Bounds.
- LIVE-2 is violated at runtime.

### RES-1

The state is built with real transactions only:

- 32 metrics with 128-byte names and units
- 64 terms
- 32 recipes with 128-byte names, 64-byte actor and executor ids, full effect
  vectors, and recipe *i* requiring every *j < i*
- 256 records: 31 Completed prerequisites and 225 open 100-unit reservations of
  recipe 31

The resulting contract state is 45,613 bytes of Borsh (`STATE`). The account's
storage_usage is 439,584 bytes, and `get_pool` returns 53,221 bytes of JSON.

Gas burnt, upstream build (from `results/upstream/RES-1.json`):

| call | pool receipt(s) Tgas | tx total Tgas | margin to 300 Tgas | attached budget |
|---|---|---|---|---|
| submit #256 (31 prerequisites over 255 records, envelope over 224 open × 32 metrics) | 12.56 | 12.87 | 287.1 | (none) |
| submit #257 (rejected Full) | 8.10 | 8.41 | 291.6 | (none) |
| preview at 255 records (one admission, as a transaction) | 5.98 | 6.30 | 293.7 | (none) |
| get_pool (as a transaction) | 9.83 | 10.14 | 289.9 | (none) |
| get_commitments(0, 1000) → 50 | 3.86 | 4.17 | 295.8 | (none) |
| dispatch + on_result (+ execute 1.50) | 8.29 + 7.62 | 18.16 | 281.8 | on_result 30 (22.4 spare), execute 30 |
| finish → notify settle(true) | 9.65 | 12.02 | 288.0 | 40 (30.4 spare) |
| settle(true) / settle(false) by the executor key | 9.64 / 9.63 | 9.95 / 9.94 | 290.1 | (none) |
| cancel (release) | 9.61 | 9.92 | 290.1 | (none) |
| reconcile + on_result (+ status 1.32) | 4.17 + 7.62 | 13.86 | 286.1 | on_result 30, status 10 |
| finish → notify settle(false) | 9.61 | 12.00 | 288.0 | 40 (30.4 spare) |

- The worst single receipt on the pool is 12.56 Tgas (submit #256), which leaves
  a margin of 287.4 Tgas to 300 Tgas.
- Submit gas grows linearly with the record count, at about 0.023 Tgas per
  record: 7.31 Tgas at 1 record, 9.66 at 128, 12.56 at 256. Most of each call is
  loading and deserializing the state.
- The `get_pool` view (RPC query) returns the full state.
- The cfg-near build's numbers are in `results/cfg-near/RES-1.json`. They
  are within 0.02 Tgas of the upstream build's, with the same worst case:
  12.56 Tgas.
- `best_quantity` (up to 100 admissions) is not a contract method. It is
  offchain only, so it is not measured.

## Findings

**SB-1 (build/deploy, medium: diagnostics, not safety).** Upstream
`scripts/build.sh` uses a plain `cargo build`, and so do `docs/api.md`
deployment step 1 and CI's `scripts/sandbox.sh`. None of them sets `--cfg near`.

Without that cfg, `near_sdk_env::panic_str` uses its "local" fallback
(`eprintln!` and then `panic!()`), and with `panic=abort` that becomes a wasm
`unreachable`. The `panic_utf8` host function is never called. near-sdk 5.29.1
itself documents this cfg combination as "pure-Rust fallbacks. not for on-chain
use".

On the deployed upstream artifact, **every** on-chain failure is the bare
"WebAssembly trap: An `unreachable` opcode was executed.". That covers:

- core errors (`Unauthorized`, `Bounds`, `Pending`, ...)
- the `#[private]` guard and init-once
- the executor's asserts ("only independent operator", "unknown job", ...)

State still reverts, so RT-REVERT holds on both builds. But a caller cannot tell
`Pending` from `Bounds` from `Unauthorized`. SH-5's "panic with the error string"
holds for the cfg-near build only.

Upstream's own sandbox test does not catch this. Its `fail` helper
(`crates/sandbox/tests/integration.rs:36`) only asserts `is_failure()`.

The witness test `sb1_upstream_build_loses_panic_messages` runs the same calls
on both builds side by side. It passes while the finding reproduces, and it will
fail as a stale witness once upstream builds with cfg(near).

To reproduce:

```
cd projects/shared-pool/sandbox && scripts/build-wasm.sh && scripts/build-res.sh
NEAR_SANDBOX_BIN_PATH=$(scripts/sandbox-bin.sh) cargo +1.98 test --locked \
  --test runtime sb1_upstream_build_loses_panic_messages -- --nocapture
```

Fix: build with `cargo near build` or with `RUSTFLAGS="--cfg near"`.

**F-1 at runtime (RT-WEDGE).** This is the brief's F-1, reproduced on both wasm
builds with the upstream executor. The runtime adds three things the core does
not show:

- The executor's job is "completed" while the pool's record stays Active, so the
  two contracts disagree permanently.
- `reconcile` "succeeds", with the Bounds error only inside its event.
- The operator's tools (`finish` with the other outcome, `confirm_not_executed`)
  are both locked out.

To reproduce, use the same setup as SB-1, then run:

```
POOL_WASM_VARIANT=cfg-near cargo +1.98 test --locked --test runtime rt_wedge_f1_end_to_end -- --nocapture
```

**Note, not a finding.** At `version = u32::MAX`, `preview` returns
`allowed: true`, but `submit` panics Arithmetic rather than returning a rejected
decision. RD-PREVIEW already excludes `version = u32::MAX`. The state needs
2^32 − 1 effective transitions, so it was patched in here.

## What is NOT shown

- **Multiple shards and congestion.** The sandbox is a single node with a single
  shard. On mainnet, receipt order across shards, and under congestion or
  delayed receipts, can differ from what is measured here. The late-ack order
  was produced deterministically with the helper executor and by timing with the
  executor key. It was **not** produced with the upstream executor's operator
  `finish`, which cannot overtake its callback on one shard.
- **Other protocol versions.** Gas is near-sandbox 2.13.4's protocol
  configuration. Other protocol versions price differently.
- **Proof of the worst case.** RES-1's maximum state is a constructed worst case,
  not a proven one: all 256 records, the longest `requires` lists, and the
  largest open envelope with those prerequisites.
- **Out of scope here (near-tests' mocked runtime covers them):**
  - attached deposits (SH-10)
  - expiry by block time (`Expired`, `SnapshotExpired`)
  - paging of `get_commitments` beyond one page
- **Prepaid gas below the maximum.** Every transaction attaches 300 Tgas
  (`max_gas`), so behaviour with less prepaid gas is not observed. Upstream
  `docs/api.md` states no minimum prepaid gas.
- **The executor at its cap.** RES-1 measures the executor's `execute` and
  `finish` at about 32 jobs, not at its 256-job cap.
- **Storage staking.** The 50 NEAR account held the max state. Storage staking
  limits were not probed. The executor's `finish` grows its state by 3 bytes
  per job (`active` to `completed` or `cancelled`).
- **Live deployment.** Nothing here touches testnet or mainnet, deployment locks,
  or code replacement (ASM-DEPLOY).

## Run times (this machine, macOS arm64)

On 2026-11-11, `run.sh` with warm caches took 438 s in total and exited 0. The
steps took:

- `check-lock`: under 1 s.
- `build-wasm` (both variants, cached): about 5 s.
- `build-res`: under 1 s.
- `tests/runtime.rs`:
  - upstream: 9 tests in 50.0 s.
  - cfg-near: 9 tests in 45.0 s.
  - Each of the tests runs its own sandbox, with 3 test threads.
- `tests/resources.rs` (RES-1):
  - upstream: 144.0 s.
  - cfg-near: 145.2 s.
  - Each run builds the 256-record state with about 350 real transactions.
- Test compilation accounts for the rest.

A cold build of the two wasm variants plus the relay takes about 2 minutes on
this machine.

On one shard the timed races reproduce the same block pattern on every run:

- **executor-key settle**: at 0 and 100 ms, settle lands before dispatch. At
  150, 200 and 300 ms the late ack occurs. At 400 ms the callback comes first.
- **operator finish**:
  - Up to 200–225 ms, finish lands before execute and is rejected.
  - From 225–250 ms on, it lands one block after the callback, never before it.
