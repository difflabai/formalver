# near-approval: M1 results (Kani on the real core)

Pin: trust-framework `5736251d65c6bc11c20e5f27ddc869db27bd7299`,
`core/src/lib.rs` sha256 `6b3f53d5…6c24`. Tools: Kani 0.68.0 (built from
tag `kani-0.68.0`), CBMC 6.11.0 (CaDiCaL), rustc nightly-2026-08-21 for Kani,
stable 1.97.0 for plain mode. Machine: 4 cores, 15 GB memory cgroup.

## Kani

`tools/scripts/run-kani.sh near-approval`, harnesses run one at a time.

<!-- KANI-TABLE -->
_Suite running; table filled in when it completes._
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

## Status in `status.toml`

The 39 M1 properties are `in-progress`, not `verified-with-assumptions`:
strategy.md section 12 requires a named spec reviewer (someone who did not
write `approval-core`) before any K property leaves `unverified`, and that
sign-off has not happened. Once it has, the flip is mechanical for every
property whose harnesses pass above.
