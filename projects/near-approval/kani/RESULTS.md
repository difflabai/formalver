# near-approval: M1 and M2 results (Kani on the real core)

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

The full matrix runs on every pull request push, on main, and on manual
dispatch (about 110 runner-minutes on the Macs). Nightly only if
`contracts/approval` moved past the pin.
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

## M2: ghost-store harnesses

`src/ghost.rs` holds the ghost stores, `src/ghost_checks.rs` the harness
bodies (strategy.md section 6.1, 6.2). `ghost.rs` carries the contract pin
and `contract/src/lib.rs`'s sha256 in its header; `plain::sparse_header_hash`
fails when the contract file, that header and `status.toml [source_hashes]`
disagree (it skips when the contract is absent, as in the mutant tree).

* **`Sparse`**: the contract's `Store` impl transliterated line by line
  over fixed association lists (`Assoc`, 4 slots), counters separate from
  the stored sizes as in the contract (`+= 1`, so an overflow panics), and
  every mutator call recorded (`Rec`).
* **`Window<APPROVED>`**: a log of any `u64` length starting at any
  offset; reads outside `from..e`, out of order, a slot without its request,
  and every write panic.
* **`Counting<T>`**: counts reads and writes through to `T`.

Local runs, one harness at a time, Kani 0.68.0, 15 GB container shared with
other jobs (peak = largest CBMC resident set seen; another job's CBMC may
inflate it).

<!-- M2-KANI-TABLE -->
| Harness | Local result | Time | Peak | Properties |
|---|---|---:|---:|---|
| `h_page_arith` | verified | 24 s | 0.3 GB | RD-3, RD-6, ROB-4 (`Window<true>`, `limit ≤ 2`) |
| `h_page_arith_empty` | verified | 206 s | 2.3 GB | RD-3, RD-6, ROB-4 (`Window<false>`, any limit); family covers 3/3 |
| `h_action_len` | verified, 3/3 covers | 34 s | 0.7 GB | ROB-3, TR-5 |
| `h_proto_add` | verified, 4/4 covers | 84 s | 1.4 GB | ST-2 |
| `h_proto_revoke` | verified, 4/4 covers | 92 s | 1.5 GB | ST-2 (F-6 absent key) |
| `h_proto_request` | verified, 2/2 covers | 119 s | 2.0 GB | ST-2, ROB-2, TR-5 (request `LogFull`) |
| `h_proto_request_empty` | verified | 89 s | 1.9 GB | `""` instance |
| `h_proto_approve` | verified, 2/2 covers | 456 s | 5.6 GB | ST-2, ROB-2, TR-5 (approve `LogFull`) |
| `h_proto_reject` | verified, 1/1 cover | 202 s | 2.6 GB | ST-2 |
| `h_oracle_approve` | verified, 3/3 covers | 616 s; 493 s with 8 accounts (ST-8W, 2026-10-19) | | ST-8 (any store size), ST-8W |
| `h_oracle_reject` | verified, 3/3 covers | 347 s; 255 s with 8 accounts (ST-8W) | | ST-8 (any store size), ST-8W |
| `h_link_t_add`, `_revoke`, `_request`, `_request_empty`, `_request_long`, `_reject` | verified (2026-10-19) | 31, 34, 178, 32, 32, 126 s | | K-LINK-T |
| `h_link_t_approve_part_err`, `_c0`, `_c1_ids`, `_c1_act_v`, `_c1_act_s`, `_c1_appr`, `_c1_rej`, `_c2`, `_c3` | verified, family covers 2/2 | 266, 317, 226, 270, 277, 229, 212, 294, 263 s | | K-LINK-T (approve, one part each: unsplit it ran out of memory) |
| `h_link_t_approve_empty`, `_long` | verified | 174, 539 s | | K-LINK-T |
| `h_count_add`, `_revoke`, `_request`, `_approve`, `_reject` | verified | 40, 46, 49, 222, 115 s | 0.5-4.9 GB | ROB-4, TX-0 |
| `h_refine_add`, `_revoke`, `_request` | verified | 841, 1078, 1177 s | 6.6, 6.7, 8.7 GB | ST-3, ST-2 |
| `h_refine_approve_tx`, `_post` | verified | 588, 1398 s | 9.0, 11.2 GB | ST-3, ST-2 |
| `h_refine_reject_tx`, `_post` | verified | 278, 1076 s | 4.2, 8.4 GB | ST-3, ST-2 |
| `h_store_laws_arr` | verified, 2/2 covers | 699 s | 4.5 GB | ST-1, INV-0 |
| `h_store_laws_sparse_reg`, `h_store_laws_sparse` | verified, 2/2 covers | 663, 765 s | 7.8, 8.6 GB | ST-1 |
| `h_store_laws_mem_law_insert`, `_remove` | verified, 1/1 cover each | 174, 404 s | 2.2, 7.4 GB | ST-1, INV-0 (`MEM_SHAPE_REG`) |
| `h_store_laws_mem_law_push_request`, `_replace_request`, `_push_approval`, `_count`, `_revocation` | verified | 227, 267, 210, 205, 294 s | 2.5, 3.3, 2.4, 2.4, 3.0 GB | ST-1, INV-0 (`MEM_SHAPE_SEQ`) |

`h_refine_add/_revoke/_request` ran before `refine` took its `part`
argument; they pass both bits, so their assertions are unchanged. The
`MemStore` law harnesses pass in plain mode, and mutant 43 is killed there;
the `MemStore` harnesses run one law each through `mem_law` (see
deviation 6).
<!-- /M2-KANI-TABLE -->

### Deviations from section 6.2, and why

1. **`Assoc` loops over its 4 concrete slots**, never a symbolic index:
   with a symbolic index, `h_proto_approve` and `h_proto_reject` ran out of
   memory at 13 GB; over concrete slots approve takes 456 s at 5.6 GB.
2. **`h_page_arith` is two harnesses.** One `Window` instance per harness:
   `h_page_arith` approves every request with `limit ≤ PAGE_SMALL` (2) and
   any `from`, and checks page length and every entry;
   `h_page_arith_empty` drops every request (fallback 6), any `limit`, and
   `from` drawn from the 10 `PAGE_FROMS` (0, 1, 2^32, 2^63 and every
   distance to `u64::MAX` that changes the page). With `from` free the
   100-slot instance timed out after 40 min in SAT (relating 100 unrolled
   increments to `from + min(l, PG)`); the Window's per-read assertions
   (slot `j` is the next one, `j < e`) bound the slots read by `e − f`, so
   ROB-4 holds for it without asserting the count. Plain mode runs both
   instances over any `from` and `limit` and also asserts the slot count of
   empty pages. Every `count` and offset stays free.
3. **`h_count_*` use a fixed `MemStore` shape** (`MEM_SHAPE`: 3
   principals, 3 requests, 3 log entries, 3 revocations; contents free).
   With a symbolic shape every `h_count_*` ran out of memory at 13.5 GB.
4. **`h_refine_*` compare `ArrStore` and `Sparse` under Kani**; the
   `MemStore` leg runs in plain mode only. `MemStore` is tied to the same
   observations by ST-1 (`h_store_laws_mem*` prove every mutator's law on
   it, from every well-formed state of the shape), and the core reaches the
   store only through those mutators and reads, so the third leg adds no
   behaviour Kani would check.
5. **`h_action_len` asserts the error kind and the non-action fields**
   (fallback 5); unwind 2051 so the chars-vs-bytes mutant fails on its
   assertion. Comparing the full 2 KB actions took more than 11 min of
   symex; this way 43 s.
6. **The `MemStore` law harnesses run one law each, straight-line**
   (`h_store_laws_mem_law_*`, through `ghost_checks::mem_law`), and
   `h_store_laws_sparse` is split in two (`_reg`: insert and remove
   principal; the base harness: the other five). All use a fixed shape:
   the registry laws 3 principals and one request, log entry and
   revocation (the frame), the others one principal and 3 of each other.
   Through the shared `Law` enum (`check_law`) the `MemStore` harnesses ran
   out of memory, two laws each, on the 64 GB CI runners as well as locally
   (1.06 M program steps for one law): CBMC kept every arm of the dispatch
   alive over the `Vec`-backed store. Straight-line, one law is 0.26 M steps
   and 2 to 7 GB;
   `h_store_laws_sparse` took 29 min at 9.6 GB, and with a symbolic shape
   its halves still took 20 and 23 min at 9.7 GB. `h_store_laws_arr` keeps every shape
   up to the `ArrStore` capacities, and the laws are per call, so a fixed
   shape loses only sizes the `ArrStore` harness covers.
7. **`h_refine_approve` and `h_refine_reject` run in two parts**: `_tx`
   (both results, `== expect`, the ST-2 calls) and `_post` (start and end
   observations agree). Same state and operation, disjoint assertions.
   As one harness approve ran out of memory (1.7 M steps, 13.5 GB) and
   reject took 25 min at 9.6 GB.
8. **`h_refine_*` assume `refine_pre`** (INV-0, INV-1, INV-8, distinct
   revocation ids, no live registration revoked): `ghost::expect` is
   `spec::expected` plus both counter guards, which is only the core's
   behaviour under INV-8 (F-14).

### Loop bounds (U-1)

`unwind-rules.tsv` gains rules for the ghost stores: `Obs` and `Rec` array
comparisons, the `Obs::r` clone, `MemStore`'s `insert_principal` and
`revocation` searches, and `approvals` per `Window` instance (`PAGE_SMALL +
1` for `Window<true>`, `MAX_PAGE_SIZE + 1` for `Window<false>`, ahead of
the generic `CAP_R + 1` rule). The unicode table search reached only from
`Result::unwrap`'s panic message (Debug of a string) is bound at 1 with the
other formatting code. With them `kani-loops.py` derives every loop:
6,368 (harness, loop) pairs on the M2 tree, none underived. New flags, all
dead or over-approximated, checked by hand:

* `h_page_arith`: the two `approvals` loops of `Window<false>` ("needs 101
  > unwind 5"); that instance runs only under `PAGE_EMPTY`, which
  `h_page_arith` never sets.
* `h_count_*`: `MemStore::insert_principal`'s search ("needs 6 > unwind
  5"); the rule's bound is for `CAP_MEM` (5) principals, `MEM_SHAPE` holds 3.

### Plain mode

`cargo test --release`: 29 tests, 3 s of test time. M2 adds
`h_page_arith`, the five `h_proto_*`, `h_count`, `h_refine`,
`h_store_laws` (mem, sparse, arr), `h_action_len`, `client_enum` (RD-4:
logs of up to 250 entries mixed with rejections and pending requests, `l ∈
{1, 2, 99, 100, 101, 200}`, both stop rules, the log optionally growing
between pages: every approval exactly once, in order),
`sparse_header_hash` and `sha256_known_answer`. Every cover each body
evaluates fires.

### Mutants

<!-- M2-MUTANTS -->
Seven new mutants (37-43), each with its `# killed-by:` harness:
action length off by one and counted in chars (`h_action_len`; 38 by `h_action_len_multi`), the page
clamp removed and the page addition wrapping (`h_page_arith`), request's
and approve's `LogFull` guard dropped (`h_proto_request`,
`h_proto_approve`), `MemStore::insert_principal` appending a duplicate
key (`h_store_laws_mem_law_insert`). `run-mutants.sh near-approval` (plain mode, all
43): 41 killed, the 2 equivalent ones (25, 26) survive. The survival check
now also skips `h_proto*` and `facts`: both see raw (non-INV-8) states, and
`facts::facts` already killed 25 and 26 on `7200b99` before M2. Not yet
run under Kani (`--kani`); CI's mutants matrix needs entries 37-43.
<!-- /M2-MUTANTS -->

## Status in `status.toml`

The 50 M1 properties are `in-progress`, not `verified-with-assumptions`:
strategy.md section 12 requires a named spec reviewer (someone who did not
write `approval-core`) before any K property leaves `unverified`, and that
sign-off has not happened. Once it has, the flip is mechanical for every
property whose harnesses pass above.
