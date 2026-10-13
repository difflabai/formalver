# near-approval: M1 results (Kani on the real core)

Pin: trust-framework `3426c9246cee98dbfaa3ff7980bd85ff839d60d6` (PR #15),
`core/src/lib.rs` sha256 `f5d72cc7…0d0c`. Previous pin `5736251`; the
results for it are in this file's history. Tools: Kani 0.68.0 (built from
tag `kani-0.68.0`), CBMC 6.11.0 (CaDiCaL), rustc nightly-2026-08-21 for
Kani, stable 1.97.0 for plain mode. Machine: 4 cores, 15 GB memory cgroup.

## Kani

`tools/scripts/run-kani.sh near-approval`, harnesses run one at a time.

<!-- KANI-TABLE -->
Every harness verifies with unwinding assertions on, and `h_canary` fails
as required. Step harnesses run as five parts each (deviation 12). CI
times are the full run on `016cc06` (workflow_dispatch, all 38 Kani jobs
green, `covers` green), wall clock per job on the self-hosted macOS
runners (`CI_RUNNER`), Kani already installed; local times are a 15 GB
Linux container, one harness at a time.

| Harness | Result | CI | Local (peak memory) | Properties |
|---|---|---:|---|---|
| `h_init`, `h_canary` | verified; canary FAILED (required) | <1 min | 41 s, 127 s | INV and GH at `Init`; setup is not vacuous |
| `h_step_add_{tx,post,hist,inv,reg}` | verified | 1, 2, 5, 2, 1 min | whole harness before the split: 26 min (13.6 GB) | TX-0, TX-1, HIST, INV for `add_principal` |
| `h_step_revoke_*` | verified | 2, 3, 4, 2, 2 min | | TX-2, HIST-8, HIST-10, INV-11/12/15 |
| `h_step_request_*` | verified | 2, 3, 5, 2, 1 min | | TX-3, TX-4 |
| `h_step_request_empty_*` | verified | 2, 2, 3, 2, 1 min | | `""` action instance |
| `h_step_approve_*` | verified | 4, 4, 8, 3, 2 min | tx 17 min (11.9 GB), post 17 min (12.7 GB), inv 13 min (10.0 GB), reg 10 min (7.0 GB) | TX-5, TR-2/3/4 steps; 11/11 covers |
| `h_step_reject_*` | verified | 2, 3, 4, 2, 2 min | | TX-7, HIST-9, INV-13 |
| `h_raw_add`, `h_raw_revoke`, `h_raw_approve`, `h_raw_reject` | verified | 4 min | 79 s, 94 s, 657 s, 345 s | ROB-1, HIST-7; add's `LogFull` at `G = MAXU` |
| `h_raw_request`, `h_raw_request_empty` | verified | 1 min | 164 s, 122 s | ROB-1, INV-9 cap boundary |
| `h_read` | verified | 6 min | 17 min (needs swap: out of memory at 15 GB without) | RD-1, RD-5, RD-7, RD-8, LEM-4 |
| `h_read_page` | verified | 4 min | 16 min | RD-2 |
| `h_read_find` | verified | 5 min | 14 min | RD-5 by request id |
| `h_bmc_from_init` (depth 5) | verified | 6 min | 26 min (11.2 GB); covers approved, rejected | GH (TR-1, TR-7), TR-2 on every trace of ≤ 5 ops |
| `h_bmc_from_init_witness` | verified | 2 min | 7 min (3.9 GB); revival cover satisfied | TR-3 witness, GH along it |
| `h_cut_add`, `h_cut_revoke`, `h_cut_request`, `h_cut_approve`, `h_cut_reject` | verified | not yet run in CI | 87 s, 105 s, 221 s, 493 s, 273 s | CUT-1 footprint rows (`CUTOFF.md`); tracking store transparent |

The step, raw and read rows also ran green earlier on GitHub's 2-CPU, 7.9 GB Linux runners
with 16 GB of swap (`2199a1e`), at 3 to 59 min per
job.

The full matrix runs on every pull request push, on main, nightly and on
manual dispatch (about 110 runner-minutes on the Macs).
<!-- /KANI-TABLE -->

## Loop bounds (U-1)

`tools/scripts/kani-loops.py projects/near-approval/kani --codegen
--core-file …/core/src/lib.rs` (CI job `loops`) lists every
loop of every harness's goto program and derives its bound from a constant:
5,002 (harness, loop) pairs, none underived, none in `core/src/lib.rs` (the core has no
loops; its iteration is in the store, which `ArrStore` bounds by `CAP_*`).
Library loops follow `unwind-rules.tsv`, each with its reason.

The report flags 60 loops as "needs 6 > unwind 5": `tla::holds::<5>` and
`tla::same::<5>` in the 30 `h_step_*` parts. They are dead there:
`assert_refines` runs only under `PART_REF` (`checks.rs`), a constant each
harness fixes, and the `h_ref_*` harnesses that do run it use unwind 6. The
check is static, so it over-approximates reachability; every flagged loop
was checked by hand. No reachable loop needs more than its harness unwind,
so with unwinding assertions on the bounds are sufficient for the state
sizes the harnesses build; `CUTOFF.md` covers sizes beyond them.

## Plain mode

`cargo test --release`: 14 tests over the harness bodies with the random
source (20k to 400k samples each), including `h_step_reject`, `h_raw_reject`
and the BMC test, which runs both the depth-5 body and the revival witness. Every cover each body evaluates fires at least
once; `h_canary` panics as it must. **This is testing, not proof.**

## Mutants

`tools/scripts/run-mutants.sh near-approval` (plain mode): 36 core mutants
in `mutants/`, regenerated against `3426c92` (26 carried over, 10 new for
reject, registration ids and revocations). All 34 that must die are killed; the 2 equivalent ones
(F-14: role or account check dropped from `live_agent_registration`)
survive the `Inv`-based harnesses. They are killed by the `h_raw_*`
harnesses, which is expected: the equivalence holds only under INV-8, and
raw states violate it. The script therefore checks survival with the raw
harnesses skipped.

<!-- KANI-MUTANTS -->
Under Kani (`run-mutants.sh near-approval --kani`, each mutant against the
`_tx` and `_post` parts of its `killed-by` harness, or `h_read` /
`h_raw_*`): all 36 jobs green on `016cc06`, so all 34 non-equivalent
mutants are killed in plain mode and under Kani, and both equivalent ones
(F-14) survive both. Median 4 min per mutant job, longest 26 min (the
must-survive mutants, which run every approve part and `h_read`).
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
   `approve` requiring `Live`. (d), the registration ids in the proof, is
   TX-4/TX-5 (each records the caller's current `registration_id`) plus
   INV-8 and INV-16 (a live registration id belongs to the key it was
   recorded with). `GH` itself, including the revocation log of TR-7, is
   still asserted at every step of `h_bmc_from_init`, where the ghost
   starts concrete at `Init`.
5. **Invariants are written as fixed-bound loops** over the store's
   capacity, guarded by the counts, instead of iterator chains over slices.
   This cut the `Inv` assumption from 520k to 188k symex steps.
6. **Bounds.** `#P, #R, #L, #V ≤ 3` in generated states (capacity 4 for
   the step). `h_bmc_from_init` keeps every trace at `#R ≤ 2` (deviation 9).
7. **Kani was built from source** here because GitHub release downloads
   are blocked in this environment; CI should use
   `cargo install kani-verifier --version 0.68.0 && cargo kani setup`.
8. **`h_read` split three ways and `h_bmc_from_init` checks the ghost
   only.** Both ran out of memory as one harness each. The cost was the
   core's `approvals` building a `Vec` of proofs, and `String`s cloned
   through a symbolic slot index; `ArrStore::request` and the RD-2
   comparison now read over concrete slots (same semantics). The BMC
   asserts GH and TR-2 (at the end of the trace, see 11) but not TX, HIST
   and INV, which `h_step_*` prove for one step from any `Inv` state
   (and `Init` is `Inv` by `h_init`).
9. **`h_bmc_from_init` bounds requests at 2** (section 6.3 fallback 3),
   down from 4. One request is enough for every TR witness (approved;
   revoke, re-add, approve the old id fails), and two keep a second id in
   play for TR-2. The TR properties themselves are proven for one step from
   any `Inv` state with up to 3 requests by the step harnesses.
10. **Registration ids in `Inv` states are drawn from `0..8`, and `G` is
    set to `#P + #V`** (since `3426c92`). INV-15 forces `G = #P + #V ≤ 6`
    and INV-11/12/14 keep every id below `G`, so within the other bounds
    nothing is lost; the narrower draw keeps the extra fields of PR #15
    (two registration ids per request, the rejection, the revocation
    list) affordable for CBMC. Raw states keep every id and `G` free, so
    `add_principal`'s `LogFull` at `G = MAXU` is checked (`h_raw_add`).
11. **Times are drawn from `0..16`, and the BMC is depth 5 plus a scripted
    witness** (since `3426c92`). Stored times in `Inv` states and the time
    of each BMC step come from `0..16` per component; every property
    compares times only by order, and 16 values exceed what any bounded
    state can hold, so this loses nothing (order isomorphism). At depth 6
    the BMC's CNF exceeded 15 GB; `h_bmc_from_init` now runs 5 steps,
    with step 0 an Add and steps 1-2 one of Add, Revoke, Request, ids
    drawn from `0..3`, and asserts GH once at the end (a failing step is a
    no-op, so every shorter trace is a prefix of one it checks). The TR-3
    revival (add, request, revoke, re-add, approve the old id) needs 6
    steps; `h_bmc_from_init_witness` runs that one scripted shape with
    symbolic arguments and checks GH and the cover.
12. **Step harnesses run in five parts.** Each `h_step_X` is
    `h_step_X_{tx,post,hist,inv,reg}` (`step_parts!` in `src/proofs.rs`):
    the exact result and TX-0; `post_ok`; HIST and the history-only
    lemmas; INV-0..10, LEM and TR-4; INV-11..16. Same state, same op,
    disjoint assertions, so their conjunction is the single harness. As
    one harness `h_step_add` peaked at 13.6 GB and `h_step_approve` was
    killed in CI; each part fits a 7.9 GB runner. A part's covers count
    for the family (`run-kani.sh`, `check-covers.sh`).

## Status in `status.toml`

The 50 M1 properties are `in-progress`, not `verified-with-assumptions`:
strategy.md section 12 requires a named spec reviewer (someone who did not
write `approval-core`) before any K property leaves `unverified`, and that
sign-off has not happened. Once it has, the flip is mechanical for every
property whose harnesses pass above.
