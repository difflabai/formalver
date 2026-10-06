# near-approval: M1 results (Kani on the real core)

Pin: trust-framework `5736251d65c6bc11c20e5f27ddc869db27bd7299`,
`core/src/lib.rs` sha256 `6b3f53d5…6c24`. Tools: Kani 0.68.0 (built from
tag `kani-0.68.0`), CBMC 6.11.0 (CaDiCaL), rustc nightly-2026-08-21 for Kani,
stable 1.97.0 for plain mode. Machine: 4 cores, 15 GB memory cgroup.

## Kani

`tools/scripts/run-kani.sh near-approval`, harnesses run one at a time.

<!-- KANI-TABLE -->
All 16 pass (`exit=0`): every harness verifies with unwinding assertions
on, `h_canary` fails as required, and every cover is SATISFIED in its
family. Times are this machine's wall clock, one harness at a time.

| Harness | Result | Time | Covers | Properties |
|---|---|---:|---|---|
| `h_init` | verified | 4 s | none | INV at `Init`, GH at `Init` |
| `h_step_add` | verified | 10.5 min | 3/3 | TX-0..5, HIST, INV-1..10, LEM-1..3 for `add_principal` |
| `h_step_revoke` | verified | 10.2 min | 4/4 | same, `revoke_principal` |
| `h_step_request` | verified | 11.4 min | 5/6 | same, `request_action` |
| `h_step_request_empty` | verified | 8.5 min | 5/6 | `""` action instance; family 6/6 |
| `h_step_approve` | verified | 15.7 min | 10/10 | same, `approve`; TR-2 step, TR-3 step |
| `h_raw_add` | verified | 35 s | 1/1 | ROB-1, no panic from any state |
| `h_raw_revoke` | verified | 39 s | 1/1 | ROB-1 |
| `h_raw_request` | verified | 67 s | 3/3 | ROB-1, INV-9 cap boundary (`pend` any `u32`) |
| `h_raw_request_empty` | verified | 37 s | 0/3 | `""` instance; family 3/3 |
| `h_raw_approve` | verified | 113 s | 1/1 | ROB-1 |
| `h_read` | verified | 10.4 min | 1/2 | RD-1, RD-7, RD-5 (by index), LEM-4; family 2/2 |
| `h_read_page` | verified | 10.4 min | 1/2 | RD-2 for any `from`, `limit` |
| `h_read_find` | verified | 10.9 min | 1/2 | RD-5 (by request id) |
| `h_bmc_from_init` | verified | 37.5 min | 2/2 | GH (TR-1) at every step, TR-2, TR-3 witness, depth 6 |
| `h_canary` | FAILED (required) | 54 s | none | setup is not vacuous |

Against the M1 exit criterion "< 20 min per harness": all but
`h_bmc_from_init` meet it here. Section 6.3's fallback 1 (split) was
applied to `h_read`; `h_bmc_from_init` was reduced to ghost-only checks
(deviation 8) and still takes 37.5 min. The next ladder rung for it is
fallback 3 (requests and log bounded at 2); not applied yet.
<!-- /KANI-TABLE -->

## Plain mode

`cargo test --release`: all 12 harness bodies with the random source
(20k to 400k samples each). Every cover each body evaluates fires at least
once; `h_canary` panics as it must. **This is testing, not proof.**

## Mutants

`tools/scripts/run-mutants.sh near-approval` (plain mode): 26 core mutants
in `mutants/`. All 24 that must die are killed; the 2 equivalent ones
(F-14: role or account check dropped from `live_agent_registration`)
survive the `Inv`-based harnesses. They are killed by the `h_raw_*`
harnesses, which is expected: the equivalence holds only under INV-8, and
raw states violate it. The script therefore checks survival with the raw
harnesses skipped.

<!-- KANI-MUTANTS -->
Under Kani: not yet run (each mutant against its listed harness).
<!-- /KANI-MUTANTS -->

## Deviations from strategy.md section 6, and why

All of these came from CBMC running out of 15 GB on the design as planned.
A GitHub runner has 16 GB, so the plan as written would not run in CI either.

1. **Harness store: `ArrStore`, not `MemStore`** (`src/store.rs`). Any `Vec`
   of symbolic length (cloning a 3-entry `MemStore`, or one `approve` step
   from an `Inv` state) exhausted memory. `ArrStore` keeps the same `Store`
   semantics (first-match lookup, insert-or-overwrite, order-preserving
   removal, append-only requests and log, out-of-range `replace_request`
   ignored) over fixed arrays with symbolic counts. The core runs unchanged;
   `MemStore` is test support, not deployed code. New obligation: ST-1 must
   cover `ArrStore` and ST-3 must relate it to the contract store (M2).
2. **Actions have fixed length under Kani.** A symbolic choice among
   strings of different lengths is a `Vec<u8>` of symbolic length. The
   alphabet is `"ab"`, `"  "`, `"é"` (all 2 bytes: ASCII equality and
   inequality, whitespace for the `trim` mutant, one multi-byte char).
   `""` comes from separate harness instances (`*_empty`), which share
   covers with their family.
3. **`--no-memory-safety-checks`.** The core is `#![forbid(unsafe_code)]`;
   pointer checks only re-verify std's internals, which are already trusted
   (ASM-TOOLS). Panic, overflow, bounds and unwinding checks stay on.
4. **No ghost history in the step harnesses.** Assuming `GH` over an
   arbitrary state blew up even at one request. TR-1 is instead assembled
   from proven parts: (a) and (b) are TX-4 and TX-5 (a successful request
   or approval requires `Holds` and records exactly the caller, key,
   action, time and log position), the stored request is immutable
   (HIST-1), and (c) continuity follows from HIST-8 (void is terminal) plus
   `approve` requiring `Live`. `GH` itself is still asserted at every step
   of `h_bmc_from_init`, where the ghost starts concrete at `Init`.
5. **Invariants are written as fixed-bound loops** over the store's
   capacity, guarded by the counts, instead of iterator chains over slices.
   This cut the `Inv` assumption from 520k to 188k symex steps.
6. **Bounds.** `#P, #R, #L ≤ 3` in generated states (capacity 4 for the
   step). `h_bmc_from_init` keeps every trace at `#R ≤ 4`.
7. **Kani was built from source** here because GitHub release downloads
   are blocked in this environment; CI should use
   `cargo install kani-verifier --version 0.68.0 && cargo kani setup`.
8. **`h_read` split three ways and `h_bmc_from_init` checks the ghost
   only.** Both ran out of memory as one harness each. The cost was the
   core's `approvals` building a `Vec` of proofs, and `String`s cloned
   through a symbolic slot index; `ArrStore::request` and the RD-2
   comparison now read over concrete slots (same semantics). The BMC
   asserts GH, TR-2 and the TR-3 witness at every step but not TX, HIST
   and INV, which `h_step_*` prove for one step from any `Inv` state
   (and `Init` is `Inv` by `h_init`).

## Status in `status.toml`

The 39 M1 properties are `in-progress`, not `verified-with-assumptions`:
strategy.md section 12 requires a named spec reviewer (someone who did not
write `approval-core`) before any K property leaves `unverified`, and that
sign-off has not happened. Once it has, the flip is mechanical for every
property whose harnesses pass above.
