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
applied to `h_read`. For `h_bmc_from_init`, deviation 8 (ghost-only
checks) and then fallback 3 (requests bounded at 2, deviation 9) were
applied; the table's 37.5 min is at bound 4, and CI below runs bound 2.

### CI

`.github/workflows/near-approval.yml` runs `pin`, `plain` and one `kani`
job per cover family on every PR touching the project and nightly, and
`mutants` (one job per mutant, plain mode and Kani) weekly. The private
submodule is checked out with the `CROSS_REPO_BUILD_KEY` secret (OQ-7).

This repository's runners have 2 CPUs and 7.9 GB. CBMC peaks above that
(measured here: `h_raw_approve` 2.5 GB; `h_step_approve` 9.5 GB, and 6.5,
6.7 and 9.3 GB for its TX, HIST and INV parts alone), so the Kani jobs add
a swap file of up to 16 GB on the runner's disk. With it, every Kani job
passed on `4308bd0` (job wall times, including ~3 min of Kani install):

| Job | Time |
|---|---:|
| `h_init h_canary` | 2 min |
| `h_raw_request h_raw_request_empty` | 7 min |
| `h_raw_add h_raw_revoke h_raw_approve` | 10 min |
| `h_step_add` | 10 min |
| `h_step_revoke` | 14 min |
| `h_step_approve` | 22 min |
| `h_step_request h_step_request_empty` | 31 min |
| `h_bmc_from_init` (requests ≤ 2) | 32 min |
| `h_read h_read_page h_read_find` | 47 min |

`h_bmc_from_init` stays over 20 min on the CI runner even at bound 2.
A larger runner (set the `KANI_RUNNER` repository variable, and
`KANI_SWAP_GB` to 0) removes the dependence on swap.
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
Under Kani (`run-mutants.sh near-approval --kani`, each mutant against its
`killed-by` harness; a run that times out or runs out of memory counts as
no verdict, not a kill): **24/24 killed, 2/2 equivalent mutants survive**
`h_step_approve` and `h_read` (which carries LEM-4, the proof that they are
equivalent under `Inv`).

Mutant 05 (empty-action check dropped) was first labelled for
`h_step_request` and survived there, correctly: that instance never passes
`""`. It is relabelled to `h_step_request_empty`, which kills it.
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
   step). `h_bmc_from_init` keeps every trace at `#R ≤ 2` (deviation 9).
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
9. **`h_bmc_from_init` bounds requests at 2** (section 6.3 fallback 3),
   down from 4. One request is enough for every TR witness (approved;
   revoke, re-add, approve the old id fails), and two keep a second id in
   play for TR-2. The TR properties themselves are proven for one step from
   any `Inv` state with up to 3 requests by the step harnesses.

## Status in `status.toml`

The 39 M1 properties are `in-progress`, not `verified-with-assumptions`:
strategy.md section 12 requires a named spec reviewer (someone who did not
write `approval-core`) before any K property leaves `unverified`, and that
sign-off has not happened. Once it has, the flip is mechanical for every
property whose harnesses pass above.
