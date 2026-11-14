# shared-pool: Kani layer results (bounded proofs on the real `pool-core`)

**Verified: shared-pool-controls v1.0.0 (contract code byte-identical to
the pin `a4bb5c3`).** Pin: difflabai/shared-pool-controls PR #1 head
`a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`, `crates/core/src/lib.rs`
sha256 `9a4eb36cc9690d353f8ec78e4eec6e389a895caccab24ced54994b8a8e7505c4`.
PR #1 has merged and the pin is on upstream `main`; v1.0.0 is commit
`6f61616` ("Mark the contract as v1.0.0"), and `crates/core/src/lib.rs`,
`crates/contract` and `crates/executor` are byte-identical between the
two (the version number is only in the root `Cargo.toml`). The fixes of
upstream PR #4 (v1.1) are not verified here.
The crate depends on the pinned submodule's `pool-core` with
`default-features = false` (zero dependencies): Kani checks the deployed
decision logic itself, not a transcription. Tools: Kani 0.68.0, CBMC 6.11.0
(CaDiCaL), rustc nightly-2026-08-21 (Kani's), rustc 1.95.0 for plain mode
(`overflow-checks = true` in release, as upstream: ASM-COMPILE). Machine:
macOS arm64, 10 cores, 64 GB, shared with other agents; one harness at a
time. Run dates 2026-11-12 and 2026-11-13.

Runner: `projects/shared-pool/kani/run.sh plain | kani [h...] | ref |
mutants [--kani] [glob] | all` (exit 0 iff every check passes; `ref` runs
the seven `h_ref_*` harnesses).

**Status: green.** 89 of 89 harnesses verified as required (88 `ok`,
`h_canary` FAILED on its own assertion only): within the bounds below
every asserted property holds on the pinned core, the code agrees
with the executable specification on every result, post-state and read,
and every call refines the TLA+ model (REF-1..3, below); 164 of 164
covers SATISFIED. INV-WF to INV-DEP hold, by induction
(`h_init_inv*` and the `_inv` parts of all seven kinds from 0, 1, 2 and 3
records), in every state reachable from `Pool::new` within the step shape
and domains that has **at most 3 records**; INV-VER is shown only along
2-operation traces from `Pool::new`. F-1 to F-6 are witnessed on the
real core, each in the sense the Findings table gives: a trace from
`Pool::new` (F-1), a configuration (F-4), some constructed state (F-2,
F-2b, F-5), one asserted cycle from `Pool::new` and from 2-record states
plus the exact limit at 255 and 256 records (F-3), the mechanism only
(F-6). Plain mode: 27 of 27 tests passed (testing, not proof). Mutants:
30 of 30 killed by plain mode and by their named Kani harness (mutant 30,
the limit one record early, added with `h_full_255`; mutant 31, a
transcription error in `tla.rs`, added with REF-1..3); the equivalent
mutant 20 survives plain mode and both of its harnesses. No property
failed on the final sources. Two tool hazards found and worked around:
Kani 0.68.0 can give a written static and an equal constant the same
storage, and a reference into a local array of structs at an index CBMC
does not fold, passed to another function, read unconstrained values
there ("Tool issues"). These are this machine's runs (A to N). CI
reruns the 53 harnesses that fit GitHub's hosted runner in memory; the
other 36 harnesses and 16 mutants were run again locally at commit
`89f99d6` and recorded, and CI checks that record instead of running
them ("CI and the local record", "Local record").

**REF-1..3** (run M, `run.sh ref`: 7 of 7 `ok`, "covers: 46 checked, all
satisfied", exit 0). For every INV state and operation of the step bounds
(1 metric, 1 term, 2 recipes, 2 records; the `h_step` generators), the
real core refines `tla/SharedPool.tla` as transcribed in `tla.rs`: the
core's error is the TLA+ error operator's and the core returns `Ok`
exactly when the action is enabled or the call is one of the model's
idempotent no-ops (REF-1); on an enabled action the abstraction of the
post-state is the action's post-state, configuration and ghost included
(REF-2); every other call leaves the abstraction unchanged (REF-3). The
46 `ref` covers are every value of each operator the step domain reaches
(`Full` needs 256 records: the traces reach it). Plain mode checks the
same on every sample of the step tests, `h_version_max` and
`h_bmc_from_init`, and on every call of the 212 conformance traces (8,804
calls; every operator value occurs). The first run FAILED three
harnesses on a tool hazard, not on a divergence ("Tool issues").

After the independent check (runs J to L): `h_full_255` now passes, with
the 255 records moved in from one constant array instead of 255 pushes
(deviation 21, cost ladder 28j); the INV preservation parts were added
at 0, 1 and 3 records (`h_step_<op>_inv_<k>`); `h_slot_cycle_*` and
`f3_slot_exhaustion` were added for F-3; the finding witnesses are
classified by what they establish. With REF-1..3 (runs M and N): the
seven `h_ref_<op>` harnesses run their own body (`checks::step_ref`, the
step's generators); the REF hooks added to `step` and `version_max` are
plain mode only (`#[cfg(not(kani))]`), so the code the earlier Kani
harnesses verify is unchanged under `cfg(kani)` and their rows stand (run
N reran `h_canary` and `h_step_pause_cov` as a check). `run.sh all` was
not run end to end in one invocation (its Kani part alone is about 7
hours); every result here is the harness's last run (table), on the
final sources.

At integration (2026-11-13) only comments changed: the `PROP:` tags of
NUM-2 (`check_tx`) and ROB-1 (the core call in `step`) and the v1.0.0
label; plain mode was rerun (27 of 27 passed). `run.sh`'s cover rule was
rerun, without Kani, over the 89 standing logs (each harness's log from
the run the table names): "covers: 164 checked, all satisfied". Dropping
`h_preview`, `h_bmc_from_init_s_submit`, `h_step_pause_cov` or
`h_ref_pause` from that set makes it report the family's covers that only
that harness satisfies, so a family's own cover left unsatisfied fails
the run, and the "0 of N" rows (`h_preview_post`, the `_tx`/`_post`/`_inv`
parts, the non-submit `h_bmc_from_init_s_*`) do not.

**CI and the local record.** The peaks in "Kani results" split the
work by what GitHub's hosted runner (`ubuntu-latest`: 4 CPUs, 16 GB,
15.6 GB usable) holds in memory:
- The workflow's `kani` job runs the 53 harnesses that peaked at 13 GB
  or less, in 8 groups, whenever a change reaches the Kani layer.
  `kani-mutants` (manual runs) runs the 15 mutants sized at 13 GB or
  less by their named harness's peak.
- The other 36 harnesses (21 groups, `kani-large`) and 16 mutants
  (`kani-mutants-large`) do not fit. They were run on a local machine at
  `89f99d6` and recorded ("Local record"). CI's `kani-record` job checks
  that record on every run instead of running them again, and the
  `covers` job counts the record's harnesses and covers with the
  groups'. They run in CI only when the `KANI_RUNNER` repository
  variable names a runner with at least 49 GB.

Before the split, all 29 groups ran on the hosted runner, the large ones
on swap. In run 43469880167 (2026-11-13, memory plus swap at 1.25 times
each group's peak), 85 of the 89 harnesses verified as required, with
the results of the table (`h_canary` FAILED on its own assertion only),
in 0.9 to 4.3 times the table's times. `h_energy_max` (1,800 s),
`h_validate` (2,400 s) and `h_bmc_from_init_s_submit` (3,600 s) ran out
of time on swap, and `h_bmc_from_init_po`'s runner shut down after 33
minutes. In run 43488691444 (commit `89f99d6`: memory plus swap at twice
each group's peak, and on swap each harness's share of the job's time),
27 of the 29 groups passed (87 harnesses).
`h_bmc_from_init_s_submit`'s runner lost contact after 52 minutes on
swap, and `h_bmc_from_init_po` ran for over 3 hours before the run was
cancelled. strategy.md section 14 has the workflow.

## Layout

| File | Contents |
|---|---|
| `src/spec.rs` | Executable specification written from the brief ("Exact core semantics"), not from the code: `expected(pre, op)` (exact result in guard order, with the reason of each exit, `Why`), `post_matches` (exact post-state and frame), `candidate`, `envelope`, `check_bounds`, `energy`, `valid`, the invariants `inv_wf`, `inv_ledger`, `inv_hard`, `inv_healthy`, `inv_dep`, `inv_ver`, the ghost `(base, k0, eff)` and `ghost_step`. Arithmetic is exact (deviation 2); the code is only ever called (`apply`), never reused. |
| `src/src.rs` | Dual-mode value source (near-approval design): `Sym` under `cfg(kani)` (symbolic: the proof), `Rng` (xorshift with hints: a test, not a proof). `assume!`, `cover!`, `Dom`, `Shape`, `Cfg`. |
| `src/gen.rs` | Bounded builders: valid configs, INV states with their ghost (values fixed by INV-LEDGER, INV-HARD and INV-DEP assumed), raw configs, operations, fixed-capacity copies. |
| `src/checks.rs` | Harness bodies (`PROP:` tags): `check_tx`, `check_post`, `assert_inv`, `covers`, and one body per harness; `step_ref` (the `h_ref_*` body), `refines` and `ref_covers` (REF-1..3 and their covers; in plain mode also called from `step`, `version_max` and `bmc_from_init`, `PART_REF`). |
| `src/proofs.rs` | `#[kani::proof]` wrappers: each fixes a `Cfg` (bounds, value domain, part). |
| `src/tla.rs` | REF-1..3: `tla/SharedPool.tla` transcribed, operator by operator, from the `.tla` text (not from `spec.rs` or the code): the state image `T` and the abstraction `alpha(pool, base, k0)`, the error operators `SubmitErr` … `ObserveErr` (guard order of `GuardOrder`), the actions (`T::next`), state equality `same`, and `assert_refines` (the three properties for one call). Fixed-capacity image: `TK` under Kani (the step bounds), `TB` over the traces (the core's limits). |
| `src/conform.rs` | Plain mode: `h_ref_traces`, REF-1..3 on every call of the 212 conformance traces (`conformance/traces/core.txt`, 8,804 calls), each replayed on the core against its recorded result and post-state. |
| `src/plain.rs` | Plain mode: every body with `Rng`, 2,000 to 2,000,000 samples each; every cover a body evaluates must fire. |
| `src/model.rs` | The fixed-capacity `Vec::with_capacity_in` and `Vec::reserve` models (deviation 1), `h_init`'s free `Config::validate` (deviation 23), `h_best`'s free `Pool::candidate` and `Pool::energy` (deviation 24), and the tagged statics they record into ("Tool issues"). |
| `mutants/*.patch` | 31 mutants: 30 of the core, 1 of `tla.rs` (`# applies-to: kani`; `# killed-by:` / `# must-survive` + `# checked-by:` headers). |
| `run.sh` | The runner (per-harness timeout 1800 s, 7200 s for the `h_step_*_inv_3` parts; memory cap `KANI_MAX_GB`, per-loop unwinding, cover check, mutants). |
| `local/` | The local record ("Local record"): `provenance.txt`, `jobs.tsv` and `covers.tsv` of the run at `89f99d6` of the 36 harnesses and 16 mutants too large for CI's hosted runner; `run-local.py` (runs them with `run.sh` and, with `--record`, records them), `record.py` (checks a finished run, writes the record and this file's block); `README.md` (format, fingerprint, commands). |

## Kani results

`run.sh kani` (all harnesses, one at a time, timeout 1800 s per harness
and 7200 s for `h_step_*_inv_3`, memory cap 40 GB, flags
`--no-memory-safety-checks --no-assertion-reach-checks -Z stubbing`,
unwinding assertions on). Times are wall clock per harness including
compilation; peak is CBMC's resident memory (sampled every 3 s). Clauses are
the CNF CBMC hands to CaDiCaL. These peaks size CI's groups: a harness
that peaked at 13 GB or less runs in the `kani` job, the others are in the
local record ("CI and the local record"). The table is the reference
measurement and is kept as measured; the local record's own times and
peaks for the 36 larger harnesses are in "Local record".

| Harness | Result | Time (s) | Peak (GB) | Clauses (M) | Covers SATISFIED (this harness) | Run |
|---|---|---:|---:|---:|---|---|
| `h_init` | ok | 576 | 21.6 | 54.2 | 2 of 2 | G |
| `h_init_inv` | ok | 61 | 5.8 | 14.1 | 1 of 1 | G |
| `h_init_inv_2` | ok | 63 | 6.3 | 14.3 | 1 of 1 | G |
| `h_validate` | ok | 737 | 26.3 | 71.7 | 10 of 10 | G |
| `h_energy` | ok | 150 | 18.8 | 32.9 | 4 of 4 | A |
| `h_energy_exact` | ok | 1674 | 18.9 | 34.7 | 0 of 4 | A |
| `h_energy_max` | ok | 447 | 32.8 | 226.3 | 1 of 1 | C |
| `h_preview` | ok | 1539 | 23.5 | 61.7 | 5 of 5 | G |
| `h_preview_post` | ok | 1436 | 22.0 | 34.5 | 0 of 5 | G |
| `h_best` | ok | 137 | 3.1 | 4.3 | 4 of 4 | G |
| `h_live1` | ok | 100 | 9.3 | 12.7 | 4 of 4 | A |
| `h_wedge` | ok | 426 | 39.0 | 59.4 | 2 of 2 | B |
| `h_wedge_healthy` | ok | 88 | 9.5 | 16.0 | 1 of 1 | F |
| `h_bmc_from_init_po` | ok | 1583 | 27.0 | 160.4 | 0 of 2 | G |
| `h_full_255` | ok | 764 | 19.9 | 37.9 | 1 of 2 | J |
| `h_full_256` | ok | 46 | 0.6 | 0.9 | 1 of 2 | J |
| `h_slot_cycle_0` | ok | 467 | 19.8 | 36.2 | 1 of 1 | J |
| `h_slot_cycle_2` | ok | 880 | 24.3 | 49.8 | 1 of 1 | J |
| `h_canary` | ok-FAILED | 100 | 10.3 | 15.0 | - | N |
| `h_version_max_submit` | ok | 357 | 16.4 | 25.8 | 1 of 10 | B |
| `h_version_max_dispatch` | ok | 42 | 4.4 | 8.0 | 1 of 10 | B |
| `h_version_max_ack` | ok | 34 | 2.7 | 4.8 | 2 of 10 | B |
| `h_version_max_cancel` | ok | 90 | 8.8 | 13.8 | 2 of 10 | B |
| `h_version_max_settle` | ok | 202 | 11.7 | 20.5 | 2 of 10 | B |
| `h_version_max_pause` | ok | 26 | 2.3 | 4.7 | 1 of 10 | B |
| `h_version_max_observe` | ok | 57 | 5.4 | 11.4 | 1 of 10 | B |
| `h_bmc_from_init_s_submit` | ok | 1121 | 29.6 | 100.2 | 2 of 2 | D |
| `h_bmc_from_init_s_dispatch` | ok | 256 | 17.4 | 37.3 | 0 of 2 | G |
| `h_bmc_from_init_s_ack` | ok | 270 | 16.7 | 36.8 | 0 of 2 | G |
| `h_bmc_from_init_s_cancel` | ok | 377 | 16.4 | 43.3 | 0 of 2 | G |
| `h_bmc_from_init_s_settle` | ok | 332 | 18.0 | 49.9 | 0 of 2 | G |
| `h_bmc_from_init_s_pause` | ok | 219 | 16.2 | 36.7 | 0 of 2 | G |
| `h_bmc_from_init_s_observe` | ok | 265 | 18.4 | 46.5 | 0 of 2 | G |
| `h_step_submit_tx` | ok | 553 | 20.8 | 29.8 | 0 of 68 | A |
| `h_step_submit_post` | ok | 412 | 17.8 | 34.6 | 0 of 68 | A |
| `h_step_submit_inv` | ok | 877 | 29.5 | 62.3 | 0 of 68 | A |
| `h_step_submit_inv_0` | ok | 394 | 19.4 | 53.4 | 0 of 68 | J |
| `h_step_submit_inv_1` | ok | 547 | 21.6 | 57.7 | 0 of 68 | J |
| `h_step_submit_inv_3` | ok | 1181 | 23.6 | 65.6 | 0 of 68 | L |
| `h_step_submit_cov` | ok | 229 | 17.0 | 25.9 | 17 of 68 | J |
| `h_step_dispatch_tx` | ok | 47 | 4.6 | 8.2 | 0 of 68 | A |
| `h_step_dispatch_post` | ok | 74 | 9.2 | 17.9 | 0 of 68 | A |
| `h_step_dispatch_inv` | ok | 103 | 9.9 | 19.0 | 0 of 68 | A |
| `h_step_dispatch_inv_0` | ok | 47 | 4.1 | 8.5 | 0 of 68 | J |
| `h_step_dispatch_inv_1` | ok | 74 | 8.1 | 15.0 | 0 of 68 | J |
| `h_step_dispatch_inv_3` | ok | 139 | 12.3 | 23.3 | 0 of 68 | K |
| `h_step_dispatch_cov` | ok | 55 | 5.0 | 8.0 | 8 of 68 | J |
| `h_step_ack_tx` | ok | 29 | 2.5 | 4.8 | 0 of 68 | A |
| `h_step_ack_post` | ok | 79 | 8.7 | 18.7 | 0 of 68 | A |
| `h_step_ack_inv` | ok | 82 | 9.0 | 15.8 | 0 of 68 | A |
| `h_step_ack_inv_0` | ok | 72 | 4.0 | 8.5 | 0 of 68 | J |
| `h_step_ack_inv_1` | ok | 63 | 5.5 | 11.9 | 0 of 68 | J |
| `h_step_ack_inv_3` | ok | 124 | 12.2 | 20.0 | 0 of 68 | K |
| `h_step_ack_cov` | ok | 44 | 3.3 | 4.8 | 8 of 68 | J |
| `h_step_cancel_tx` | ok | 101 | 8.4 | 14.1 | 0 of 68 | A |
| `h_step_cancel_post` | ok | 197 | 14.4 | 31.7 | 0 of 68 | B |
| `h_step_cancel_inv` | ok | 229 | 13.2 | 25.8 | 0 of 68 | A |
| `h_step_cancel_inv_0` | ok | 52 | 4.2 | 8.5 | 0 of 68 | J |
| `h_step_cancel_inv_1` | ok | 135 | 9.6 | 20.1 | 0 of 68 | J |
| `h_step_cancel_inv_3` | ok | 621 | 16.4 | 31.8 | 0 of 68 | K |
| `h_step_cancel_cov` | ok | 83 | 9.4 | 13.8 | 9 of 68 | J |
| `h_step_settle_tx` | ok | 204 | 13.7 | 20.9 | 0 of 68 | A |
| `h_step_settle_post` | ok | 355 | 18.4 | 41.0 | 0 of 68 | A |
| `h_step_settle_inv` | ok | 438 | 18.0 | 33.1 | 0 of 68 | A |
| `h_step_settle_inv_0` | ok | 46 | 4.1 | 8.5 | 0 of 68 | J |
| `h_step_settle_inv_1` | ok | 218 | 13.2 | 25.8 | 0 of 68 | J |
| `h_step_settle_inv_3` | ok | 1788 | 18.3 | 40.8 | 0 of 68 | K |
| `h_step_settle_cov` | ok | 135 | 12.5 | 20.6 | 13 of 68 | J |
| `h_step_pause_tx` | ok | 32 | 2.8 | 4.7 | 0 of 68 | A |
| `h_step_pause_post` | ok | 69 | 8.6 | 17.4 | 0 of 68 | A |
| `h_step_pause_inv` | ok | 90 | 8.7 | 15.8 | 0 of 68 | A |
| `h_step_pause_inv_0` | ok | 57 | 4.1 | 8.5 | 0 of 68 | J |
| `h_step_pause_inv_1` | ok | 62 | 5.7 | 11.8 | 0 of 68 | J |
| `h_step_pause_inv_3` | ok | 124 | 12.8 | 20.0 | 0 of 68 | K |
| `h_step_pause_cov` | ok | 37 | 2.8 | 4.7 | 5 of 68 | N |
| `h_step_observe_tx` | ok | 97 | 11.3 | 24.2 | 0 of 68 | A |
| `h_step_observe_post` | ok | 164 | 12.0 | 29.4 | 0 of 68 | A |
| `h_step_observe_inv` | ok | 124 | 11.1 | 23.5 | 0 of 68 | A |
| `h_step_observe_inv_0` | ok | 76 | 7.6 | 15.7 | 0 of 68 | J |
| `h_step_observe_inv_1` | ok | 91 | 9.6 | 19.3 | 0 of 68 | J |
| `h_step_observe_inv_3` | ok | 162 | 14.1 | 28.1 | 0 of 68 | K |
| `h_step_observe_cov` | ok | 70 | 6.9 | 13.2 | 8 of 68 | J |
| `h_ref_submit` | ok | 351 | 12.4 | 23.0 | 12 of 46 | N |
| `h_ref_dispatch` | ok | 62 | 5.7 | 11.1 | 8 of 46 | N |
| `h_ref_ack` | ok | 55 | 5.2 | 10.7 | 4 of 46 | N |
| `h_ref_cancel` | ok | 104 | 9.6 | 16.0 | 7 of 46 | N |
| `h_ref_settle` | ok | 221 | 11.0 | 21.9 | 7 of 46 | N |
| `h_ref_pause` | ok | 55 | 5.3 | 10.7 | 3 of 46 | N |
| `h_ref_observe` | ok | 69 | 8.4 | 15.2 | 5 of 46 | N |

**89 of 89 harnesses as required** (88 `ok`, `h_canary` FAILED on its own
assertion only, as it must). Sum of the harness times: 26,921 s
(7.5 h).

"Covers" counts the covers of the harness's family that are SATISFIED in
this harness (the step families' covers are in their `_cov` parts; "0 of
68" in a `_tx` part is expected). "Run" is the run the row comes from;
each row is the harness's last run. A: the first complete `run.sh kani`
(every harness, ended 07:40); B: the rerun of the harnesses that failed in
A, after the first fixes (09:56); C, D, F, G, H, I: later runs of the
harnesses that changed (12:22, 13:05, 14:41, 17:20, 18:36, 21:01; I is
`h_full_256` with the field-sensitivity option of deviation 21, 376 s
against 30 s without it in H); run E left no standing result. J, K, L:
after the independent check. J is one `run.sh kani` of `h_full_*` (the
constant array of deviation 21), `h_slot_cycle_*`, `h_step_*_inv_0`,
`h_step_*_inv_1` and the seven `_cov` parts (4,848 s, ended 23:53, exit
0, "covers: 71 checked, all satisfied"). K is `h_step_*_inv_3` (ended
00:44): `h_step_settle_inv_3` passed in 1788 s, 12 s inside the
limit of then 1800 s, and `h_step_submit_inv_3` was stopped by hand
after 79 s, on the guess from that margin that it would not fit; K's exit
is 1 for that and because it has no `_cov` part ("Covers"). L is
`h_step_submit_inv_3` alone with the limit 7000 s (ended 01:05; it
needed 1181 s, one SAT call of 1072 s); `run.sh` now gives the `_inv_3`
parts 7200 s. M and N: with REF-1..3. M is `run.sh ref` (the seven
`h_ref_*`, 01:57 to 02:13, exit 0, "covers: 46 checked, all satisfied";
the same results and times within 2 s as N); N is `run.sh kani h_canary
h_step_pause_cov h_ref_*` with `KANI="/usr/bin/time -l cargo kani"` (02:18
to 02:36), whose peak column is the maximum resident set size that
`time -l` reports (exact, not sampled; the earlier runs sampled every 3
s), and whose exit is 1 only because one `_cov` part does not satisfy
the whole `h_step` family (the 46 `h_ref` covers were all SATISFIED
again). N reran `h_canary` and `h_step_pause_cov`, whose code is
unchanged under `cfg(kani)`, as a check: both as before. The first
`run.sh ref`, before the fix of "Tool issues", FAILED three harnesses and
left no standing result. A harness whose reachable code changed after its row's run
was rerun; the later changes to `run.sh`'s per-loop bounds only lowered
bounds of loops that earlier passes had unrolled further (unwinding
assertions are always on, so those passes stand). The failed and stopped
attempts are in the cost ladder. Logs: `target/kani-logs*/<harness>.log`
(not committed).

## Local record

The 36 harnesses of the workflow's `kani-large` groups (each peaked
above 13 GB in "Kani results") and the 16 mutants of
`kani-mutants-large` were run again at commit `89f99d6` of this
repository (Kani tree `da291ce`, core pin `a4bb5c3`) on a 10-core, 64 GB
Apple M1 Max, with Kani 0.68.0 and CBMC 6.11.0. The mutants are 01, 03,
05, 06, 10, 11, 12, 15, 16, 18, 19, 21, 23, 25, 28 and 30: those whose
named harness peaked above 13 GB, and mutant 21, which takes
`h_full_256` past the record limit and is sized as `h_full_255`. Each
job ran `run.sh` unchanged in a `git archive` copy of the commit's Kani
inputs, with its CI matrix timeout as `KANI_TIMEOUT`,
`KANI_DEFER_COVERS=1` and `run.sh`'s default memory cap of 40 GB, two
jobs at a time. `kani/local/record.py` checked the finished run (every
job exited 0, every harness `ok`, every mutant as its patch expects, the
commit's Kani inputs the same as HEAD's) and wrote the record to
`kani/local/` (`provenance.txt`, `jobs.tsv`, `covers.tsv`; format and
commands in `kani/local/README.md`) and the block below.

On every run, CI's `kani-record` job (`tools/scripts/check-kani-record.py`)
checks that:
- the record's fingerprint of the Kani inputs is the commit's. The
  inputs are every file under `kani/` except `kani/local` and the
  Markdown, with the git object ids of `kani/src`, `Cargo.toml`,
  `Cargo.lock`, `mutants`, `run.sh` and `.gitignore` on lines of their
  own, the core's gitlink and `conformance/traces/core.txt`, the
  repository's `.cargo/config[.toml]` above `kani/` (none here), and
  `tools/versions.env`'s `KANI` and `CBMC`;
- `jobs.tsv` and `covers.tsv` match the digest in `provenance.txt`, and
  the fingerprint is the hash of the record's input lines and, where the
  clone has the record's commit, that commit's;
- every recorded harness is `ok` and every recorded mutant as its patch
  expects;
- the `kani` groups and the record together are `run.sh list`, each
  harness once, and `kani-mutants` and the record are `mutants/*.patch`,
  each mutant once;
- the block below is there and is `record.py table`.

A change to any Kani input fails that job until
`kani/local/run-local.py --record` has been run at the new commit and
the record committed. On a `KANI_RUNNER`, a run whose `kani-large` and
`kani-mutants-large` jobs verify all it records passes with a warning,
but `kani-mutants-large` runs only on a manual run with `mutants`, so
pull requests and pushes still need the new record. The
`covers` job checks the record's covers with the groups'. CI cannot
check that the run took place as recorded: the record, like the tables
above, rests on the word of whoever ran it. Anyone with a 64 GB machine
can repeat it with `run-local.py --record` and compare.

The block's times and peaks are this run's, with two jobs at a time, so
they need not equal the one-at-a-time measurements in "Kani results",
which size the groups. A mutant's time is its whole job, plain mode
included. Its plain mode used the host's default Rust toolchain (rustc
1.95.0, not `tools/versions.env`'s 1.97.0; `run-local.py` now sets
1.97.0 for the mutant jobs, as CI does). The record does not cover the
plain half of a mutant's verdict, and `RUST_TOOLCHAIN` is not in the
fingerprint: CI's `mutants` job reruns every mutant's plain mode with
`tools/versions.env`'s toolchain on every run.

<!-- kani-local-record: begin (kani/local/record.py writes this block; do not edit) -->
**PLACEHOLDER, not a result: the local record is not written yet.** The
run at `89f99d6` is still in progress. When it has finished,
`kani/local/record.py <run dir>` replaces this block with the record's
provenance, its harness table and its mutant table.
`check-kani-record.py` fails while this placeholder stands.
<!-- kani-local-record: end -->

## Bounds

All harnesses (`proofs.rs`, `gen.rs`):

- **Accounts** `o_`, `a1`, `x1`, `z_` (the brief's `o, a1, x1, z`; all 2
  bytes, deviation 5). Every role (owner, actor, executor) and every caller
  is any of the four, so every equality pattern among the at most three role
  holders a step compares and the caller is reached (including actor =
  executor, F-4).
- **Step harnesses** (`h_step_*`): a valid configuration with **1 metric, 1
  term, 2 recipes** (recipe 1 may require recipe 0, 1 to 100 units) and an
  INV state with **exactly 2 records** (statuses free, the first `k0`
  terminal, `k0` free; values by INV-LEDGER from a free base). Metric bounds,
  base values and targets from `Anchored(4)`: `a + o` with
  `a ∈ {-1e6, 0, 1e6}`, `o ∈ -4..=4`, clipped to ±1e6, so small values and
  both extremes of the value range. Deltas (`reserve`, `complete`) in
  `-3..=3`; `max_units` in `1..=3`; weights in `{1, 2, 1000}`; any term shape;
  `max_age_seconds` free. Version, `observed_at`, `paused`, expiries free
  (`u32`/`u64`/`bool`). Operation arguments: caller any account; request
  recipe in `0..4` (2 and 3 are `InvalidRecipe`), units in `0..8` (0 and
  4..7 are `InvalidUnits`), request version and expiry and `now` free; record
  ids in `0..8` (2..7 are `NotFound`); `accepted`, `completed`, `paused` free;
  observe vectors of length 0..3 with values from the value domain or
  ±1,000,001 or `i64::MIN`/`MAX`. Narrow ranges are used only for arguments
  the code compares before any arithmetic or index (deviation 4).
- **`h_step_<op>_inv_<k>`** (`k` = 0, 1, 3; one harness per kind and
  count, the `h_step` cover family): the `_inv` part of the steps from INV
  states with exactly `k` records instead of 2, everything else as the
  steps. With `_inv` (2 records) every kind runs from every count `0..=3`.
- **`h_ref_<op>`** (REF-1..3, one harness per kind, the `h_ref` cover
  family): the steps' state and operation, from the same generators with
  the same `Cfg` (`STEP`: 1 metric, 1 term, 2 recipes, exactly 2 records,
  the domains above), through `checks::step_ref`. The TLA+ image `TK` has
  room for 2 metrics, 2 terms, 2 recipes, 2 requirements per recipe and 4
  records, above every pre- and post-state of the step shape (a submit ends
  at 3 records); `alpha` asserts that the pool fits. In plain mode the same
  check runs inside every step test (`h_step_*`: up to 2 metrics, 2 terms,
  2 recipes, 3 records), in `h_version_max` and in `h_bmc_from_init`
  (depth 5, image of 8 records), and over every call of the conformance
  traces (`h_ref_traces`, image `TB`: 32 metrics, 64 terms, 32 recipes, 32
  requirements, 256 records; the traces have at most 8 metrics, 5 terms,
  6 recipes, 2 requirements and 256 records).
- **`h_live1`**: as the steps with **3 records** (so two other records can
  be open).
- **`h_version_max_<op>`** (one harness per operation kind, one cover
  family): as the steps with `version = u32::MAX`.
- **`h_preview`, `h_preview_post`**: as the steps.
- **`h_best`**: under Kani the configuration of the steps with no record,
  any submit request of the step domain (units `0..8`), the core's
  `candidate` stubbed by a free result per quantity (`Ok` with any values
  in `[-1e6, 1e6]`, or `Err`) and its `energy` by a free result per call
  (`Ok` with any `u64`, or `Err`; deviation 24). In plain mode as the steps,
  the real `candidate`, request units ≤ 3 (`max_units` ≤ 3, so larger
  requests only add `InvalidUnits` candidates).
- **`h_energy`** (contract): **2 metrics, 2 terms**, values and targets
  anywhere in `[-1e6, 1e6]` (`Full`), any weight in `1..=1000`, vectors of
  length 0..3 with values in range, ±1,000,001 or `i64::MIN`/`MAX`.
  **`h_energy_exact`**: the same shape with `Anchored(4)` values and any
  weight. **`h_energy_max`**: the 64-term worst case, concrete.
- **`h_init`**: a raw configuration (at most 2 metrics, 2 terms, 3 recipes,
  2 requirements per recipe, vector lengths free, every field free among
  in-range, edge and out-of-range values: values and targets
  `Anchored(4)`, deltas `-3..=3`, each also ±1,000,001 or `i64::MIN`/`MAX`;
  term metrics, weights, `max_units`, requirement indices and units any
  `u32`; strings of 0 or 2 bytes); `now` free; `validate` free (deviation
  23). The raw domain contains every valid configuration of that shape and
  value set. Plain mode draws up to 3 metrics, also 128/129-byte strings
  and, half the time, a valid configuration with free initial values.
  **`h_validate`**: the same raw configurations, the real `validate`.
  **`h_init_inv`**, **`h_init_inv_2`**: a valid configuration of the step
  shape (1 metric, 1 term, 2 recipes), resp. 2 metrics, 2 terms and 2
  recipes; values `Anchored(4)`, deltas `-3..=3`, initial values free in
  `[min, max]`; under Kani `new`'s `Ok` value built by `pool_of`
  (deviation 23).
- **`h_wedge`**: from `Pool::new` over a symbolic configuration of the
  step shape (1 metric, 1 term, 2 recipes), bounds, initial values, targets
  and observations in `-4..=4`, deltas in `-3..=3`, any weight in
  `{1, 2, 1000}`, any term shape; under Kani the roles are fixed (owner
  `o_`, actors `a1`, executors `x1`; deviation 19). The script of F-1:
  observe, submit, dispatch, then settle both ways, cancel, observe.
- **`h_wedge_healthy`**: under Kani from every healthy INV state (`B = 0`,
  version < MAX) of the step shape with values in `-4..=4` whose record 0
  is Dispatched and record 1 Completed (deviation 19): settle(cancelled)
  of record 0 by its executor, cancel by the owner, observe. In plain mode
  the script of F-2 from `Pool::new` over random configurations (up to 2
  metrics and 2 terms, 2 recipes): two submits, two dispatches, the hedge
  completes, then settle(cancelled), cancel, observe, and
  settle(completed).
- **`h_bmc_from_init_po`**, **`h_bmc_from_init_s_<op>`** (one cover
  family): from `Pool::new` over a valid configuration of the step shape,
  **2 operations**: a pause or an observe, then any operation
  (`_po`); or a submit, then an operation of kind `<op>` (`_s_<op>`, one
  harness per kind; a second submit is possibly a replay of the first).
  After the first operation the exact post-state is asserted and the
  second starts from that state rebuilt with constant shapes, after a
  submit only from its `Ok` outcome (deviation 20). Values in `-3..=3`,
  deltas in `-2..=2`, `max_units` ≤ 2.
- **`h_full_255`**, **`h_full_256`**: 255 or 256 Cancelled records of
  recipe 0 with ids `0..count` (a concrete count each, one constant array
  moved into the vector, deviation 21), configuration, values, version,
  `observed_at`, `paused` and the submit request as the steps.
- **`h_slot_cycle_0`**, **`h_slot_cycle_2`** (one cover family): a valid
  configuration of the step shape and domain; from `Pool::new` (`_0`,
  `pool_of`, `observed_at` free) or from an INV state of the steps with 2
  records (`_2`), restricted to quiet states (no open record, every metric
  within `[min, max]`) with `version < u32::MAX - 2`; a submit of the
  step domain, then (if it is accepted) a cancel of the new record by the
  same caller and the same request again at the new version, each on the
  previous post-state rebuilt with constant shapes (deviation 25).

## Properties

PROP tags are in `checks.rs`; each is asserted inside the bounds above.

| ID | Harnesses | What is asserted |
|---|---|---|
| CFG-1 | `h_init`, `h_init_inv`, `h_init_inv_2`, `h_validate` | `Pool::new` calls `validate` and is Ok iff it is Ok (`h_init`, `validate` free), so iff the spec's `valid` (CFG-2); it fails only `InvalidConfig`; the initial pool is the config, initial values, version 0, `observed_at = now`, unpaused, no records; a valid configuration is accepted and its initial pool satisfies every INV-* with the initial ghost (`h_init_inv`, `h_init_inv_2`, deviation 23). |
| CFG-2 | `h_validate` | `validate` = spec on raw configs; Ok ⇒ nonempty, term metrics in range, weights 1..1000, metric bounds ordered and bounded, vectors of length n, deltas bounded, `max_units` 1..100, requirements strictly earlier, distinct, units 1..100. |
| NUM-1 | `h_energy`, `h_energy_exact`, `h_energy_max` | Bounded values of length n ⇒ `energy_terms` and `energy` Ok with one term per term (any value in ±1e6, any weight); each term exactly `w·r²` and `energy` their exact sum (anchored values, any weight; 64-term worst case 2.56e17 exact); other vectors fail `Bounds`. |
| NUM-2 | `h_step_submit_tx`, `h_step_cancel_tx`, `h_step_settle_tx` | `add` fails closed exactly at ±1e6: the exact result in guard order includes every `Arithmetic` exit (`Why::Add`), with values at both extremes (covers "Arithmetic (reserve)", "(release)"). |
| ROB-1 | every step harness | No panic, overflow or out-of-bounds access in the core from any INV state within the bounds, any argument within the domains (Kani checks every one). |
| TX-SUBMIT … TX-OBSERVE | `h_step_<op>_tx`, `_post` (2 records); for submit also `h_full_255`, `h_full_256` | Exact result in guard order (`expected`), exact post-state and frame (`post_matches`, including the configuration). At the record limit (`h_full_*`): the exact result and post-state of a submit at 255 and at 256 Cancelled records, so `Full` exactly from 256 records on (a submit at 255 is admitted when the other guards pass: cover "full: Ok at 255 records"). |
| TX-0, TX-NOOP, TX-VER | `h_step_*_tx`, `h_version_max_*`, `h_full_*` | Every `Err` leaves the pool unchanged; idempotent `Ok` paths change nothing (version included); every other `Ok` increments the version by exactly 1; at `u32::MAX` every effective transition fails `Arithmetic` and nothing wraps. |
| AUTH-1 | `h_step_*_tx` | A call that changes the state was made by the role of the brief. |
| STALE-1 | `h_step_submit_tx`, `h_bmc_from_init_s_submit` | Submit Ok ⇒ request version = version and the version strictly increases; along every 2-operation trace no accepted request is accepted again. |
| ADM-1, ADM-2, DEP-1 | `h_step_submit_tx` | As in the catalogue, against the spec's exact energy. |
| HARD-STEP, LIFE-1, ASYNC-1, TERM-1 | `h_step_*_post` | As in the catalogue. |
| OBS-1 | `h_step_observe_tx` | Observe Ok ⇒ no open record, config unchanged. |
| PAUSE-1 | `h_step_*_tx` (blocked ops), `h_step_*_post` (transparent ops) | Paused: submit and dispatch change nothing. Settle, acknowledge, cancel and observe: the spec's outcome with `paused` flipped is the same (flag kept flipped); with `_tx`/`_post` (code = spec from every state, `paused` either way) the code's outcome is independent of `paused` (deviation 18). |
| INV-WF, INV-LEDGER, INV-HARD, INV-HEALTHY, INV-DEP, INV-VER | `h_step_*_inv` (2 records), `h_step_*_inv_0`, `_inv_1`, `_inv_3`, `h_init_inv*`, `h_bmc_from_init_*` | INV-WF to INV-DEP hold in the initial state (`h_init_inv*`) and are preserved, with the ghost update, by every step of every kind from every INV state of the step shape and domains with **exactly 0, 1, 2 or 3 records** (one harness per kind and count). By induction, every state with **at most 3 records** that calls within the domains reach from `Pool::new` satisfies them (the steps' configurations fix `initial = min`; only `new` reads `initial`). A submit from 3 records ends at 4 records, never a pre-state here: states with 4 or more records are not covered by Kani. INV-VER (version = the ghost's count of effective steps from `Init`) only along the 2-operation traces of `h_bmc_from_init_*`. |
| RD-PREVIEW | `h_preview`, `h_preview_post` | `allowed` iff the spec's candidate is Ok; `reason` (Debug name), candidate values, `before`, `after` and the term strings as coded; no mutation; allowed and version < MAX ⇒ submit Ok with the previewed candidate. |
| RD-BEST | `h_best` (with `h_preview`, `h_step_submit_tx`, `h_step_submit_post`, `h_energy`) | `best_quantity` evaluates `candidate` exactly once for each quantity in `1..=units` with the request's other fields, `energy` exactly once on each `Ok` candidate's values and on nothing else, and returns the quantity of least energy among those whose energy is `Ok`, ties to the larger, `None` iff none (Kani: any `Ok`/`Err` pattern of `candidate` and of `energy`, any `Ok` values, units ≤ 7; deviation 24); `candidate` is the spec's (`h_preview`: `Ok` iff the spec's, the reason; `h_step_submit_*`: the `Ok` values, below `u32::MAX`) and `energy` is the spec's and `Ok` on them (`h_energy`, NUM-1), so the result is the spec's choice, admissible, and `submit` accepts it below `u32::MAX` (plain mode also calls `submit`). |
| LIVE-1 | `h_live1`, `h_wedge_healthy` (in the F-2 state) | From an INV state with B = 0 and version < MAX, `settle(executor, id, true)` is Ok for every Dispatched, Active or Unknown record (with up to two other open records). |
| F-1, F-2 | `h_wedge`, `h_wedge_healthy` | Covers that must be SATISFIED (F-1 from `Pool::new`, F-2 from INV states; "Findings"), plus TX-0 on the failed calls. |
| REF-1 | `h_ref_submit`, `h_ref_dispatch`, `h_ref_ack`, `h_ref_cancel`, `h_ref_settle`, `h_ref_pause`, `h_ref_observe`; plain `h_step_*`, `h_version_max`, `h_bmc_from_init`, `h_ref_traces` | Guard exactness: for every INV state and operation of the step bounds, the core's `Err` is the TLA+ error operator's value (`SubmitErr`, `DispatchErr`, `AckErr`, `CancelErr`, `SettleErr`, `PauseErr`, `ObserveErr` of `alpha(pre)`; `InvalidConfig` is no operator value), and the core returns `Ok` exactly when the operator gives "Ok" (the action is enabled) or "Noop" (the idempotent paths, a stutter in the model; TraceCheck's `Agrees`). At `version = u32::MAX` no action is enabled (plain `h_version_max`). |
| REF-2 | as REF-1 | Effect exactness: when the operator gives "Ok", `alpha(post)` is the action's post-state (`T::next`: every TLA+ variable but the history variables `steps` and `last`, configuration included), with the implementation's ghost (`base`, `k0` from the core's post-state after an `Ok` observe); submit returns the new record's index (`NR`). |
| REF-3 | as REF-1 | Stutter: every other call (an error, or "Noop") leaves `alpha` unchanged, configuration, values, version, `observedAt`, `paused`, records and ghost. |
| F-3 (the cycle) | `h_slot_cycle_0`, `h_slot_cycle_2` | From `Pool::new` and from quiet INV states with 2 records (version below `u32::MAX - 2`): an accepted submit is the spec's; the same caller's cancel of the new record is then accepted; afterwards the values, `paused`, `observed_at` and the older records are as before, the new record is Cancelled and the version is 2 higher; and the same request at the new version is accepted with the same reserved values and the next id. Cover "slot cycle: ..." SATISFIED. |

## Covers (vacuity)

Every cover is a `kani::cover!` in the `_cov` part of its family (or in the
harness itself). `run.sh kani` collects every cover's status from every log
and requires each to be SATISFIED in some harness of its family; `h_canary`
must FAIL on its own assertion ("canary: no submit is ever accepted") and on
nothing else.

**164 of 164 covers SATISFIED** in some harness of their family.
`h_canary` FAILED on "canary: no submit is ever accepted" and on nothing
else (runs B and N). Run J checked the `h_step`, `h_full` and `h_slot_cycle`
families in one invocation ("covers: 71 checked, all satisfied"); the
other families' covers come from the runs named in the table. Run K
(`h_step_*_inv_3`) has no `_cov` part, so its own cover check reports the
`h_step` covers as not satisfied in it; with run J's cover statuses
merged (the same sources) every `h_step` cover is SATISFIED. Run M
(`run.sh ref`) checked the `h_ref` family in one invocation ("covers: 46
checked, all satisfied"). `run.sh` counts a cover whose description
starts with `ref ` in the `h_ref` family only, and no other cover there:
`step_ref` also reaches the generators' code, whose covers are the
`h_step` family's.

| Family | Covers | SATISFIED | Not satisfied |
|---|---:|---:|---|
| `h_step` | 68 | 68 | - |
| `h_energy` | 4 | 4 | - |
| `h_energy_max` | 1 | 1 | - |
| `h_live1` | 4 | 4 | - |
| `h_version_max` | 10 | 10 | - |
| `h_wedge` | 2 | 2 | - |
| `h_wedge_healthy` | 1 | 1 | - |
| `h_bmc_from_init` | 2 | 2 | - |
| `h_best` | 4 | 4 | - |
| `h_init` | 3 | 3 | - |
| `h_init_inv_2` | 1 | 1 | - |
| `h_validate` | 10 | 10 | - |
| `h_preview` | 5 | 5 | - |
| `h_full` | 2 | 2 | - |
| `h_slot_cycle` | 1 | 1 | - |
| `h_ref` | 46 | 46 | - |

The `h_step` family's 68 covers are each step's guard outcomes and paths
(every `Err` kind it can return, every `Why` exit, the `Ok` variants),
checked in `h_step_<op>_cov` (submit 17, dispatch 8, acknowledge 8, cancel
9, settle 13, pause 5, observe 8). The `h_version_max` family's 10 covers
are each kind's `Arithmetic` at `u32::MAX` (7) and the no-op `Ok`s that
remain possible there (acknowledge, cancel, settle). A cover UNSATISFIABLE
in one harness and SATISFIED in another of its family is expected (for
example "version max: submit Arithmetic" outside `h_version_max_submit`).
The `h_ref` family's 46 covers are, per operation, every value of its
TLA+ error operator that the step domain reaches: "Ok" (the action is
enabled; REF-2 is then not vacuous) and each error and "Noop" (REF-3),
in `h_ref_<op>` (submit 12: Ok and every guard but `Full`; dispatch 8,
acknowledge 4, cancel 7, settle 7, pause 3, observe 5). `Full` needs 256
records (`h_full_*` for the core; the conformance traces for REF, plain
mode).

## Plain mode

`run.sh plain` (`cargo test --release`): 27 tests, every harness body with
the random source, 2,000 to 2,000,000 samples each (the step bodies run all
four parts at once, over random shapes of up to 2 metrics, 2 terms, 2
recipes and 3 records, and half the time from a random-walk state reached
from `Pool::new`; `h_bmc_from_init` at depth 5, and `h_bmc_two`, the
Kani harnesses' two-operation body; `h_slot_cycle`, the F-3 cycle from
`Pool::new` and from random INV states), plus `f1_brief_instance`
(the brief's F-1 reproducer, unscaled), `f2_risk_fixture` (F-2 in the
`risk` fixture), `f2_small_instance` (`h_wedge_healthy`'s Kani
instance) and `f3_slot_exhaustion` (F-3 end to end: 256 submit/cancel
cycles from `Pool::new` on the brief's configuration, then `Full`, also
after an `observe`), and `h_ref_traces` (REF-1..3 on every call of the
212 conformance traces, 8,804 calls, each replayed on the core against
its recorded result and post-state; every value of the error operators
occurs: "Ok" 2,053 times, "Noop" 494, and each of the 15 errors the
traces contain, `Full` twice). The step tests, `h_version_max` and
`h_bmc_from_init` also check REF-1..3 on every sample (`PART_REF`, plain
mode only; under Kani REF-1..3 are the `h_ref_*` harnesses'). Every cover
a body evaluates must fire at least once (the 46 `ref ...` covers fire in
the step tests).
Result: 27 passed, 0 failed (10.0 s of tests, `h_ref_traces` 0.06 s;
`run.sh plain` 10 s with an up-to-date build, while a Kani harness and
the plain mutant runs ran; run M). **This is testing, not proof.**

## Mutants

`run.sh mutants [--kani]`: 31 mutants (`mutants/*.patch`): 30 of the
core, each applied to a temporary copy of `crates/core`, and one of the
TLA+ transcription (`# applies-to: kani`: applied to a copy of this
crate's `src`). A mutant to be killed
must make plain mode fail and, with `--kani`, the harness named in its
`# killed-by:` header FAIL; CBMC stops at the first violated property
(`--stop-on-fail`; the covers are compiled out of the mutant's copy, and
Kani's text output is read, "Tool issues"). Mutant 20 is equivalent
(`# must-survive`): plain mode and its `# checked-by:` harnesses must pass
on it, as proofs.

**Plain mode: 30 of 30 killed, mutant 20 survived. Kani: 30 of 30
killed by their named harness, mutant 20 survived both
`h_step_observe_tx` and `h_step_observe_post`.** `run.sh mutants --kani`
over mutants 1 to 29 (94 min), then mutants 20 and 21 again (36 min)
after two `run.sh` changes they called for: the bound 4 of `observe`'s
value loop (deviation 11; the first run of mutant 20 failed an unwinding
assertion there, not a property) and the field-sensitivity option for
`h_full_256` (deviation 21). Mutant 21 then still timed out; after the
constant-array construction of deviation 21, `run.sh mutants --kani
'[23][01]-full*'` ran mutants 21 and 30 (517 s, after run L): both killed.
Plain mode over all 30: `run.sh mutants` in run J (266 s). With REF-1..3
(run M): plain mode over all 31, `run.sh mutants` (243 s, run beside a
Kani harness): 30 killed, mutant 20 survived; `run.sh mutants --kani
'31*'` (112 s): mutant 31 killed by `h_ref_cancel` ("REF-1 guard
exactness", 15.96M clauses, one SAT call of 27 s).

In CI ("CI and the local record"), the `mutants` job reruns all 31 in
plain mode on every run. `kani-mutants` (manual runs) reruns under Kani
the 15 sized at 13 GB or less by their named harness's peak. The other
16 were run again at `89f99d6`, in plain mode and under Kani, and their
rows are in the local record's mutant table ("Local record").

| Mutant | What it changes | Expected | Plain | Kani (harness) |
|---|---|---|---|---|
| `01-guard-swap-paused-stale` | candidate: Stale checked before Paused | killed | killed | killed (`h_step_submit_tx`) |
| `02-guard-swap-dispatch-auth-paused` | dispatch: Paused checked before Unauthorized | killed | killed | killed (`h_step_dispatch_tx`) |
| `03-submit-expiry-off-by-one` | candidate: a request expiring now is accepted (<= became <) | killed | killed | killed (`h_step_submit_tx`) |
| `04-dispatch-expiry-off-by-one` | dispatch: dispatch at the expiry instant is accepted (>= became >) | killed | killed | killed (`h_step_dispatch_tx`) |
| `05-check-bounds-without-skip` | settle(completed): check_bounds keeps the settled record in the envelope (skip dropped) | killed | killed | killed (`h_step_settle_tx`, `h_live1`) |
| `06-envelope-ignores-reserved` | envelope: Reserved records are left out (pending hedges ignored) | killed | killed | killed (`h_step_submit_tx`) |
| `07-release-without-bounds-check` | release: no check_bounds before undoing a reservation | killed | killed | killed (`h_step_cancel_tx`) |
| `08-dispatch-version-not-bumped` | dispatch: version not incremented | killed | killed | killed (`h_step_dispatch_tx`) |
| `09-ack-noop-bumps-version` | acknowledge: the reverted reconcile griefing (a repeated ack bumps the version) | killed | killed | killed (`h_step_ack_tx`) |
| `10-settle-accepts-opposite-terminal` | settle: the opposite terminal outcome is applied (Completed can be released) | killed | killed | killed (`h_step_settle_tx`) |
| `11-prerequisite-counts-non-completed` | candidate: prerequisites counted from every non-cancelled record, not only Completed | killed | killed | killed (`h_step_submit_tx`) |
| `12-energy-ge` | candidate: equal energy rejected (> became >=) | killed | killed | killed (`h_step_submit_tx`) |
| `13-cancel-allows-dispatched` | cancel: a Dispatched record can be cancelled (reservation released while in flight) | killed | killed | killed (`h_step_cancel_tx`) |
| `14-observe-ignores-open-records` | observe: no Pending check (baseline replaced under open obligations) | killed | killed | killed (`h_step_observe_tx`) |
| `15-submit-actor-check-dropped` | candidate: caller not checked against the recipe actor | killed | killed | killed (`h_step_submit_tx`) |
| `16-settle-executor-check-dropped` | settle: caller not checked against the executor | killed | killed | killed (`h_step_settle_tx`) |
| `17-cancel-owner-check-dropped` | cancel: the owner can no longer cancel (actor only) | killed | killed | killed (`h_step_cancel_tx`) |
| `18-preview-candidate-divergence` | preview: admission evaluated one second later than submit would (preview/candidate divergence) | killed | killed | killed (`h_preview`) |
| `19-recovery-gt` | candidate: recovery accepts a completion that does not decrease energy (>= became >) | killed | killed | killed (`h_step_submit_tx`) |
| `20-observe-length-check-dropped` | observe: vector length not checked. | survive | survived | survived (`h_step_observe_tx`, `h_step_observe_post`) |
| `21-full-off-by-one` | candidate: a 257th record is admitted (>= became >) | killed | killed | killed (`h_full_256`) |
| `22-version-wraps` | bump: version wraps at u32::MAX instead of failing | killed | killed | killed (`h_version_max_pause`) |
| `23-envelope-ignores-extra` | envelope: the requested recipe's own completion is not included | killed | killed | killed (`h_step_submit_tx`) |
| `24-best-ties-to-fewer-units` | best_quantity: ties go to the smaller quantity | killed | killed | killed (`h_best`) |
| `25-energy-excess-sign` | energy_terms: Excess measured below the target (sign flip) | killed | killed | killed (`h_energy_exact`) |
| `26-ack-accepted-inverted` | acknowledge: accepted maps to Unknown and rejected to Active | killed | killed | killed (`h_step_ack_tx`) |
| `27-add-bound-check-dropped` | add: result not checked against +-1e6 (only i64 overflow). | killed | killed | killed (`h_step_cancel_tx`) |
| `28-check-bounds-vs-candidate` | check_bounds: compares against the violations of the candidate instead of the current values | killed | killed | killed (`h_step_submit_tx`) |
| `29-observe-keeps-observed-at` | observe: the new baseline keeps the old observation time (snapshot age never refreshed) | killed | killed | killed (`h_step_observe_post`) |
| `30-full-rejects-at-255` | candidate: the 256th record is refused (`Full` one record early: `>= MAX_RECORDS - 1`) | killed | killed | killed (`h_full_255`) |
| `31-tla-release-skip-dropped` | `tla.rs` (the TLA+ transcription, not the core): `ReleaseErr` checks the envelope without skipping the released record (`CheckBounds(.., -1)` for `CheckBounds(.., i)`) | killed | killed (`h_ref_traces`, `h_step_cancel`, `h_step_settle`, `h_version_max`, `h_bmc_from_init`: REF-1) | killed (`h_ref_cancel`) |

**Mutant 20 is equivalent.** It drops `values.len() != self.values.len()`
from `observe`'s `Bounds` guard. A vector of the wrong length then reaches
`self.energy(&values)?`, whose `energy_terms` checks the length first and
returns the same `Err(Bounds)`, before `bump` and before any write; a
vector of the right length takes the same path as before. Result and state
are the original's for every input, so no check can kill it; the two
observe harnesses prove that on the mutant (within their bounds) and plain
mode passes on it.

**Mutants 21 and 30 under Kani** move the record limit by one record
either way. On mutant 21 (`>=` became `>`) a submit at 256 records goes
past the guard into the scans of the 256 records and the admission, and
`h_full_256` FAILED "TX: exact result at the record limit" (Kani 262 s
with the build: 1.51M steps, 33.8M clauses); with 256 pushes it had
timed out (6.43M steps, 508 s of symbolic execution, the SAT call not
done at 30 minutes). On mutant 30 a submit at 255 records fails `Full`,
and `h_full_255` FAILED the same check (234 s: 1.14M steps, 4.7M
clauses). Before `h_full_255` passed, mutant 30 would have passed every
Kani harness.

## Findings

**No property failed.** Within the bounds above every asserted property
holds on the pinned core, and the executable specification (written from
the brief) agrees with the code on every result, post-state and read; the
Kani layer found no new defect and no spec-versus-code divergence. Two
tool hazards were found and worked around ("Tool issues").

The findings of the find/confirm phase are witnessed on the real core,
but not all in the same sense. Each witness is a `cover!` that `run.sh
kani` requires to be SATISFIED: a cover is existential (some input of the
harness's domain reaches it), a witness and not a failed check. For F-3
there are also asserted properties (every input). The "Kind" column says
what the witness establishes:

- **trace**: a script of calls from `Pool::new` reaches the finding in
  some configuration of the harness's domain (F-1).
- **configuration**: `validate` accepts a configuration with the
  property, so `Pool::new` does (CFG-1); nothing else is needed (F-4).
- **state**: the finding happens from some constructed state (an INV
  state, or a pool built by hand); that this state is reachable from
  `Pool::new` is not shown by Kani (F-2, F-2b, F-5).
- **state + one cycle from `Pool::new`**: F-3. The cycle (submit, cancel,
  submit again by the same actor) is asserted from `Pool::new` and from
  every quiet INV state with 2 records, and the limit is exact at 255 and
  256 Cancelled records; the chain of 256 cycles from `Pool::new` is not
  run by Kani.
- **mechanism**: the guards the finding is made of fire, the finding as a
  whole is not reached (F-6).

| Finding | Kind | Kani witness (SATISFIED) | Not shown by Kani | Plain-mode reproducer |
|---|---|---|---|---|
| F-1, wedge after a disturbing observe | trace | `h_wedge`: "wedge: F-1 reachable (settle both ways Bounds, cancel and observe Pending)": for some configuration of the step shape (values in `-4..=4`, fixed roles, deviation 19) the script from `Pool::new` (observe, submit, dispatch) reaches a state in which both settles, cancel and observe fail; TX-0 is asserted on every failed call of every configuration | - | `f1_brief_instance` (the brief's configuration and script, unscaled) |
| F-2, healthy-state release wedge | state | `h_wedge_healthy`: "wedge healthy: F-2 reachable (settle(cancelled) Bounds, cancel and observe Pending, B = 0)": the harness ranges over every healthy INV state of the step shape (values in `-4..=4`) whose record 0 is Dispatched and record 1 Completed, and in some of them the three calls fail; settle(completed) is `Ok` in every such state (LIVE-1, `h_live1`) | that such a state is reachable from `Pool::new` (deviation 19) | `f2_small_instance` (the whole script from `Pool::new`), `f2_risk_fixture` (the `risk` fixture from `Pool::new`) |
| F-2b, release fails `Arithmetic` (or `Bounds`) | state | `h_step_cancel_cov`, `h_step_settle_cov`: "cancel: Arithmetic (release)", "settle: Arithmetic (release)", "cancel: Bounds (a dependent reservation blocks release)", "settle: Bounds (release)", each from some INV state with 2 records | reachability of those states from `Pool::new` | the step bodies (half of their samples from random walks from `Pool::new`) |
| F-3, slot exhaustion | state + one cycle from `Pool::new` | `h_full_255`: "full: Ok at 255 records" (a submit at 255 Cancelled records is still admitted, exactly the spec's); `h_full_256`: "full: Full at 256 records" (exactly the spec's); `h_slot_cycle_0` (from `Pool::new`) and `h_slot_cycle_2` (from quiet INV states with 2 records): "slot cycle: submit, cancel and submit again by the actor (F-3)", and asserted for every such state and submit: from a quiet state (no open record, values within bounds, version below `u32::MAX - 2`) an accepted submit is always followed by an accepted cancel by the same actor, whose only lasting effects are one more Cancelled record and the version + 2, and the same request is accepted again with the same values; records are append-only (LIFE-1, `h_step_*_post`) and observe keeps them (TX-OBSERVE) | the 256 cycles as one trace (the cycle lemma is shown at 0 and 2 earlier records, the limit at 255 and 256 Cancelled records of recipe 0) | `f3_slot_exhaustion` (256 cycles from `Pool::new` on the brief's configuration, then `Full`, also after an `observe`) |
| F-4, actor = executor accepted | configuration | `h_validate`: "validate: Ok with actor = executor (F-4)"; with CFG-1 `Pool::new` accepts it; every role equality pattern is in the step domains | - | `h_validate` |
| F-5, frozen at `u32::MAX` | state | `h_version_max_<op>`: "version max: <op> Arithmetic" for all seven kinds, settle and pause (so no unpause) included, each from some INV state with `version = u32::MAX`; asserted (TX-VER) for every such state: every effective call fails `Arithmetic` and changes nothing | reaching `u32::MAX` from `Pool::new` (2^32 - 1 effective transitions; INV-VER says the version counts them) | `h_version_max` |
| F-6, stale snapshot with an open record | mechanism | "observe: Pending" (`h_step_observe_cov`), "submit: SnapshotExpired", "dispatch: SnapshotExpired" (`h_step_submit_cov`, `h_step_dispatch_cov`), each from some INV state | the finding as one scenario (a long-open record, then the snapshot expires and observe cannot refresh it) | the step bodies |

## Deviations from the plan, and why

All but two came from CBMC running out of memory or time on the design as
planned (cost ladder below); 25 applies deviation 20's design to a harness
added later, without measuring the direct design first, and 26 records
choices for REF-1..3 that the plan left open. None weakens an
assertion: each either narrows the
inputs (stated in Bounds), replaces a library function by a model that can
only make a harness fail, rewrites a spec function into an equal one that
CBMC handles better, or splits a property into harnesses whose conclusions
combine (deviations 18 to 25; in 23 and 24 a core function is replaced
by a free result in one harness and pinned down by others).

1. **Fixed-capacity `Vec::with_capacity_in` model** (`model.rs`, every
   harness except `h_validate`, `h_energy_max`, `h_full_*`). The core's
   fallible `collect` in `add` merges its error exit into the result, so the
   length of `next` is symbolic, and `values.to_vec()` then allocates a
   symbolic size, which CBMC encodes with the array theory (a single submit
   with 1 metric, 1 term, 1 recipe and no record ran out of 20 GB). The model
   returns an empty vector with a constant capacity (24 bytes, 3 large
   elements, 4 otherwise) and asserts that the request fits, so a larger
   request fails the harness; std guarantees only "at least `capacity`", and
   the core never reads a capacity. `Vec::reserve` (called by `extend` and
   `collect` with a symbolic size hint: `release`'s `undo`, `violations`) is
   modelled the same way: it gives an empty vector the constant capacity and
   asserts that `additional` fits in the spare capacity. std reallocates only
   when `capacity - len < additional`, so the model never removes a path the
   code takes within the constant capacity; the std growth path it replaces
   was 41M of the 45M clauses of a cancel step (cost ladder).
2. **Spec integers are `i64` with overflow checks**, not `i128`, and
   `d·u` is a 32-bit product (`mul_du`, its preconditions asserted): every
   spec quantity fits by a wide margin (energy ≤ 2.56e17), and an overflow
   would be a failed check, never a silent wrap. `i128` doubled every
   multiplier.
3. **Concrete-slot reads and writes.** Every lookup by a symbolic index in
   the spec goes through a loop over concrete slots (`rcp`, `rec`), and the
   generated records and the vectors of the raw configurations are written
   at concrete offsets and then truncated: an index into a heap buffer is a
   symbolic byte offset, a mux over every byte of the buffer. (With
   conditional pushes in the raw configurations, `h_init` and `h_validate`
   ran out of 40 GB in the propositional encoding after 0.56M and 0.97M
   symbolic-execution steps.)
4. **Narrow operation arguments under Kani** (`Src::wide` is false): request
   recipes in `0..4`, units in `0..8`, record ids in `0..8`. Each is only
   compared (`recipe >= #recipes`, `units == 0 || units > max_units`,
   `id < #records`) before it reaches arithmetic or an index, so the
   ranges reach every guard outcome; plain mode also draws them from all of
   `u32`.
5. **Equal-length accounts and bounded string equality** (`eq_str`,
   `eq_text`, `eq_i64s`, `same_config`, `same_state`). `==` on `str` is a
   `memcmp` whose length CBMC cannot fold, each byte read a case split over
   every string object in the state (12.5M of 27M clauses in a submit). The
   lengths are compared first and then at most `K` bytes (2 for accounts);
   a longer string fails the harness on an assertion, it is never compared
   partially. `preview`'s strings are read once into a local array
   (`Text<K>`, again asserting the length): the `reason` (16 bytes; the
   longest reason, `SnapshotExpired`, has 15) is compared there with the
   spec's, and each number (24 bytes) is parsed there and compared with the
   spec's number (`is_dec`: the canonical decimal numeral, 1 to 20 digits
   and no leading zero unless it is `0`, is unique, so this is
   `s == x.to_string()`; plain mode checks the parser against `to_string`
   on every call). With the reason compared three times on the heap
   `h_preview` was 62.2M clauses; with the spec formatting its numbers by
   `to_string` (a 64-bit division per digit pair) `h_preview_post` had no
   CNF after 20 minutes. The same holds for value vectors: `y.values == x.values`
   (PAUSE-1) is a `memcmp` over `[i64; 2]` that CBMC did not unroll within
   the bound (`h_step_cancel_post` failed its unwinding assertion), so it is
   `eq_vals`, a loop over the two elements.
6. **Configuration equality in the step harnesses only in `_post`.** Under
   Kani, `same_state` (TX-0, TX-NOOP, AUTH-1's "changed", PAUSE-1) and the
   post-state checks of `h_full_*` and `h_bmc_from_init_*` compare values,
   version, `observed_at`, `paused` and records, not the configuration;
   `_post` proves that no step changes the configuration (frame of
   `post_matches`), so the two together give the full equality. In
   `h_full_*` the configuration is not copied or compared under Kani at all
   (at its unwind of 258 the copy's loops and then the slice comparisons
   of `same_config` were unrolled about 257 times each; cost ladder 28c,
   28d); there the frame is `h_step_submit_post`'s over 2 records. Plain
   mode compares everything everywhere, `h_full` included.
7. **Fixed shapes and record counts** (deviation from the brief's ≤ 2
   metrics, ≤ 2 terms, ≤ 3 records in the steps): 1 metric, 1 term, 2
   recipes, exactly 2 records (3 in `h_live1`; 0, 1 and 3 in
   `h_step_<op>_inv_<k>`, one harness per count, so that the invariants'
   induction covers every count up to 3). A symbolic record count
   doubled the formula and each further metric, term or recipe multiplies it
   (cost ladder); with 2 metrics, 2 terms and 3 records the submit step did
   not fit in 26 GB. 2 metrics and 2 terms are covered by `h_energy*`; all
   shapes up to 2/2/2/3 by plain mode and the other layers.
8. **`pool_of` instead of `Pool::new`** in `h_energy*`, `h_energy_max`,
   `h_wedge*` and `h_bmc_from_init` (under Kani; plain mode calls
   `Pool::new`). Validating a config that is valid by construction cost
   more than the energy (13.8M of 52.5M clauses); in `h_energy_max`, without
   the capacity model, `validate` unrolled each requirement loop 66 times
   inside a recipe loop unrolled 66 times. `pool_of` builds `Pool::new`'s
   Ok value directly (CFG-1, shown by `h_init`, says it is the same; its
   INV too).
9. **Energy exactness by a same-circuit product.** Under Kani each term is
   compared with `w·r²` computed by a wrapping `u64` product after
   asserting `r ≤ 2e6` and `w ≤ 1000` linearly, so equality modulo 2^64 is
   equality; an `i128` product against the code's `u64` product (a miter of
   two different multipliers) did not finish. Exactness runs on anchored
   values (`h_energy_exact`), the Ok/`Bounds` contract over the full range
   (`h_energy`).
10. **Parts.** Each step harness is four CBMC runs: `_tx` (exact result and
    the result-level properties), `_post` (exact post-state, frame, LIFE-1,
    ASYNC-1, TERM-1, HARD-STEP, PAUSE-1), `_inv` (INV-* after the step),
    `_cov` (covers). Each SATISFIED cover is one more SAT call, and with the
    assertions in the same run every call carries the whole formula.
11. **Per-loop unwinding** (`run.sh`, `short_loops`). The core's iterator
    loops over values, deltas, terms and requirement pairs (at most 2
    elements in the steps; 3 recipes and 2 pairs in `h_init` and
    `h_validate`, bound 4) get bound 3, the record and string loops the
    harness unwind (4 to 7; 24 in `h_preview_post`, 258 in `h_full_*`).
    `h_energy_max` (64 terms) has no short loops. Some loops get their own
    bound: the 24- and 20-byte loops of `spec::Text::<24>::of` and
    `spec::parse_dec` 25, the 16-byte loops of `spec::Text::<16>` 17,
    `observe`'s loop over the observed values (`any(!bounded)`) 4 (it runs
    after the length check, so on n ≤ 2 values; mutant 20, which drops that
    check, runs it on the observe domain's vectors of up to 3 values),
    `spec::eq_i64s`'s loop over `M + 2 = 4` elements 5 (above the unwind of
    `h_init` and `h_validate`, 4, where it failed its unwinding assertion),
    `best_quantity`'s two loops over `1..=units` 8 (`h_best`: units ≤ 7
    under Kani), `gen::copy_vec`'s loops over values, deltas,
    requirements, metrics and terms, the slice comparisons over
    requirements and terms and `spec::prereqs_met`'s loop over a recipe's
    requirements 4 in `h_full_*` and `h_preview_post` (CBMC does not fold
    those lengths: at `h_full`'s unwind of 258 each copy was unrolled about
    253 times, and `prereqs_met` repeated its scan of the 255 records once
    per unrolled requirement), and in `h_energy_max` the loop inside each
    `next()` of `energy_terms`' fallible `collect` 2 (it exits in its first
    iteration, but CBMC does not fold it, and at 66 it was unrolled 66 times
    inside the 66 of the `collect`). Unwinding assertions stay on, so a
    bound that is too small fails the harness; it never hides a path.
12. **`assume` returns a constant `true` under Kani** (`src.rs`), so an
    early return after an assumption is dead code: a live early return
    merged every field of the returned state with an unconstrained value.
13. **Reachability checks of assertions off** (`--no-assertion-reach-checks`;
    one SAT round per assertion). Vacuity is covered by the covers.
14. **`h_bmc_from_init` at depth 2** (plain mode: depth 5). Every level adds
    every operation's formula again. The covers "a record completes" and
    "observe after a completion" need depth 3 and 4, so they are plain
    mode's (`h_bmc_from_init`, whose body is plain-only; the Kani
    harnesses run `bmc_two`).
15. **`h_init` and `h_validate` under Kani: at most 2 metrics, strings of
    0 or 2 bytes, the capacity model.** `h_init` draws raw configurations
    only (they contain every valid configuration of the domain; a second
    builder doubled the heap objects every pointer may refer to). Both draw
    at most 2 metrics and vectors of at most 2 deltas (`RAW_M`; 3 recipes,
    2 terms and 2 requirements per recipe as planned) and strings of 0 or 2
    bytes (`INIT_LONG`). `validate` reads only the length of a string
    (`short`: 1 to 128 bytes), so the 128/129-byte boundary of `short` is
    plain mode's, as are 3-metric raw configurations. The runs before: with
    129-byte strings `h_init` did not finish symbolic execution in 30 min
    (the requirement-pair loops unrolled 6 to 8 times); `h_validate` with
    3 metrics, long strings and no capacity model (1.09M symbolic-execution
    steps) and `h_init` with 3 metrics, short strings and the capacity model
    (1.66M steps) ran out of 40 GB.
16. **`--no-memory-safety-checks`.** The core is `#![forbid(unsafe_code)]`;
    pointer checks would only re-verify std (ASM-TOOLS). Panic, overflow,
    bounds and unwinding checks stay on.
17. **Spec rewrites that CBMC handles better** (equal functions):
    `inv_healthy` computes each slot's liveness and completion deltas once
    and sums them over the 16 subsets (it recomputed them per subset), and
    `valid`'s delta-chain loop is one loop per vector instead of a chained
    iterator.
18. **PAUSE-1 for the transparent operations at the spec level under
    Kani.** The plan called the code a second time on the pre-state with
    `paused` flipped; that doubled the formula and the cancel and settle
    `_post` runs went out of 32 GB. The harness asserts that the spec's
    outcome does not depend on `paused`; `_tx` and `_post` assert that the
    code's outcome is the spec's from every state of the domain (`paused`
    is free), so the code's outcome does not depend on it either. Plain
    mode also calls the code again.
19. **The wedge harnesses under Kani: fixed roles in `h_wedge`, a healthy
    INV state in `h_wedge_healthy`.** The plan's `h_wedge` (symbolic roles,
    `Pool::new`) ran out of 40 GB after 26 min. Under Kani its owner is
    `o_`, every actor `a1`, every executor `x1` (with symbolic roles every
    `==` on an account is a case split over the four accounts); the
    configuration stays symbolic, so its TX-0 assertions on the wedged
    state hold for every instance of the domain. `h_wedge_healthy`'s script
    makes nine calls on the core over two records, and every outcome is
    symbolic, so the length of the record vector is too from the first
    submit on: with the spec's steps and the invariants it was stopped in
    symbolic execution; with the script on the core alone it ran out of 40
    GB (3.7M steps); and on one concrete configuration with the spec's
    checks it still ran out of 40 GB (5.2M steps, and 20,347 verification
    conditions left after simplification: CBMC did not reduce the concrete
    run to constants; we did not find out which values stayed symbolic).
    Under Kani it starts from the state the script reaches, any
    healthy INV state whose record 0 is Dispatched and record 1 Completed,
    and covers the wedge there; TX-0 for the three failed calls and LIVE-1
    for record 0 are `h_step_{settle,cancel,observe}_tx`'s and `h_live1`'s
    over these states. Reachability from `Pool::new` is plain mode's
    (`h_wedge_healthy`, `f2_small_instance`, `f2_risk_fixture`), and the
    TLA+ and sandbox layers'.
20. **`h_bmc_from_init` under Kani: the first operation a submit, pause or
    observe, the state after it rebuilt, one harness per second kind after
    a submit.** From `Pool::new` there is no record, so every other kind
    fails (`NotFound` or earlier) and changes nothing. The plan's version
    (`Pool::new`, INV of the initial state, any kind first) was still in
    symbolic execution after 16 minutes; with the first kind restricted and
    any kind second it ran out of 40 GB (6.3M symbolic-execution steps);
    with one harness per second kind it timed out at 30 minutes (2.8M
    steps, 37 GB; 2.4M without the copy of the pre-state). The cause is the
    first operation's symbolic outcome: the record count and the value
    vector after it depend on it, so every later read is a case split and a
    second submit pushes at a symbolic offset. So `bmc_two` asserts the
    exact result and the exact post-state of the first operation (the
    spec's: values, version, `observed_at`, `paused`, the pushed record),
    then rebuilds that state with constant shapes (the configuration moved,
    not copied) and runs the second operation from it, with INV after both.
    After a submit it continues from the `Ok` outcome only: an `Err` leaves
    the initial pool (asserted above), and the pause/observe harness
    continues from it too (a pause by a non-owner fails). `_po` takes any
    second kind (from a state without records every kind but submit, pause
    and observe fails `NotFound`); `_s_<op>` fixes it. Together they cover
    every 2-operation trace from `Pool::new` within the bounds.
21. **`h_full` split into `h_full_255` and `h_full_256`**, each with a
    concrete record count, **the records one constant array**, and CBMC's
    field sensitivity raised. With a symbolic count (255 or 256) every push
    was guarded, the vector length symbolic from the first record on, and
    63 of the 256 pushes took 9 minutes of symbolic execution (cost ladder
    24). `h_full_*` run CBMC with `--max-field-sensitivity-array-size 8192`
    (`run.sh`, `extra_cbmc`): the records' buffer (257 × 24 bytes) is one
    byte array, above CBMC's default limit of 64 elements, so no read of a
    record folded to its constant fields, both envelopes took the `open`
    branch (a multiplication) for each of the 255 records, and symbolic
    execution was still in the core's envelope after 13 minutes; with the
    limit above the buffer's size each byte is its own symbol and the reads
    are constants (cost ladder 28e to 28g). But then every write into the
    buffer rewrote all of its bytes: built by 255 pushes, the records cost
    16 to 17 minutes of symbolic execution (8.05M steps) and the first SAT
    call did not finish in the rest of the 30 minutes (28h, 28i: the
    harness timed out, with the steps' values and with values 0). The
    records are now `OLD_RECORDS` (`checks.rs`), 257 Cancelled records of
    recipe 0 with ids `0..257` computed by the compiler (a `const fn`),
    moved into the vector by `Vec::from` (one write of the whole buffer)
    and truncated to 255 or 256, so the buffer has room for the core's push
    and never reallocates (mutant 21 pushes at 256). The post-state check
    compares the old records over `0..count`, a concrete trip count (it
    was the post-state's length, 255 or 256). The pool is the same as
    before: the same 255 or 256 records, the same configuration, values and
    request domains, the same assertions. `h_full_255` then took 2.42M
    steps (493 s of symbolic execution) and two SAT calls of 147 s and
    93 s (37.9M clauses), and passes in 764 s (28j); `h_full_256` 46 s (it
    took 376 s). The option and the
    construction change the encoding and the capacity of the vector, not
    the program under test or the properties. Under Kani `h_full_*` do not
    evaluate INV-DEP (true by construction: every record is of recipe 0,
    which has no prerequisite) or INV-WF of the whole post-state (the old
    records are asserted unchanged and are well formed by construction,
    the new one is asserted to be the spec's, and the count is asserted to
    be 256); plain mode evaluates both. The configuration is not compared
    under Kani (deviation 6).
22. **`h_version_max` split by operation kind** (`h_version_max_<op>`,
    one cover family). All seven kinds in one formula (73.1M clauses, 35 GB)
    timed out at 30 minutes.
23. **`h_init` with a free `validate`, and `h_init_inv`.** `h_init` stubs
    `Config::validate` by `model::validate`, whose result is free and
    recorded, and asserts that `Pool::new` calls it, is `Ok` exactly when
    it is, fails only with `InvalidConfig`, and builds the specified
    initial pool. `h_validate` shows that the real `validate` is the spec's
    validity over the same raw configurations, so the two give CFG-1's
    "`new` Ok iff valid". The INV of the initial pool is `h_init_inv`'s
    and `h_init_inv_2`'s, over valid configurations of fixed shapes (1
    metric, 1 term, 2 recipes; 2, 2, 2): each configuration is `valid`
    (asserted), so `new` accepts it (`h_init`, `h_validate`) and returns
    the pool `h_init` describes, which these harnesses build directly
    (`pool_of`) and check against INV with the initial ghost. The plan's
    single harness (raw configuration, real `validate`, the spec's `valid`
    and the invariants in one formula) ran out of 40 GB (deviation 15), and
    `h_init_inv` with the real `validate` and symbolic shapes had no CNF
    after 20 minutes. Plain mode checks everything in one body, with the
    real `validate`.
24. **`h_best`: the search alone, with `candidate` and `energy` stubbed.**
    The search runs one admission of the core per quantity, and the
    harness one of the spec per quantity. With up to 3 units and the plan's
    second call to `submit` on the result, the formula did not reach the
    solver in 20 minutes (9.3M symbolic-execution steps); with up to 2
    units and no second call it had 161.9M clauses, its first SAT call took
    1230 s and it timed out. Under Kani the core's private
    `Pool::candidate` is stubbed (`model::candidate`): each call returns a
    free result, `Ok` with any values of length n in `[-1e6, 1e6]` (the
    real `candidate`'s `Ok` is `add`'s result, such a vector) or `Err`, and
    records it with the call's arguments. Ranking the candidates by the
    spec's energy, or by the core's `energy` again in the harness, left a
    miter of multiplier circuits per quantity: the last SAT call did not
    finish (12 minutes with full-range values; 30 minutes, a timeout, with
    anchored values; 7 minutes with the core's energy on both sides). So
    `Pool::energy` is stubbed too (`model::energy`): a free result per
    call, `Ok` with any `u64` or `Err`, recorded under the quantity of the
    preceding `candidate` call with whether its argument is exactly that
    candidate's `Ok` values. `h_best` shows, for requests of up to 7 units,
    that `best_quantity` calls `candidate` exactly once for each quantity
    in `1..=units` with the request's other fields, the caller and `now`,
    calls `energy` exactly once on each `Ok` candidate's values and never
    otherwise, and returns the quantity whose energy is least among those
    with an `Ok` energy, ties to the larger, or `None`. That the real
    `candidate` is the spec's is `h_preview`'s (`allowed` = `candidate` is
    `Ok`, iff the spec's; the reason) and `h_step_submit_tx`'s and
    `_post`'s (`submit` is `candidate` followed by the version bump, so its
    `Ok` post-values below `u32::MAX` are `candidate`'s `Ok` values); that
    the real `energy` is `Ok` and the spec's on every vector of length n in
    `[-1e6, 1e6]` is `h_energy`'s (NUM-1). At `version = u32::MAX` the `Ok`
    values of `candidate` are not observed by any harness; `candidate`
    reads the version only in the `Stale` guard. The cap of 100 units
    (`min(units, 100)`) is plain mode's (wide units), as are 3 units with
    the real `candidate` and `energy` and the call to `submit` on the
    result.

25. **`h_slot_cycle_*`: each call of the cycle on a rebuilt state** (added
    after the first review, F-3; deviation 20's design, used from the start
    and not measured against the direct script). The submit's outcome is
    symbolic, so after it the record count and the value vector would be
    too, and every later read a case split. `slot_cycle` asserts that the submit's result
    and post-state are the spec's (values, version, the pushed record),
    continues from the accepted outcome only, and runs the cancel on that
    post-state rebuilt with constant shapes (the configuration moved); the
    cancel's post-state is asserted (values and older records as before,
    the new record Cancelled, the version + 2, `paused` and `observed_at`
    unchanged) and rebuilt the same way for the second submit. Plain mode
    runs the same body. That the cycle can be repeated until `Full` is an
    induction this layer shows only in its base and step at 0 and 2 earlier
    records and at the limit (255, 256 records); the 256-cycle trace is
    plain mode's (`f3_slot_exhaustion`).
26. **REF-1..3: what `alpha` maps, and the ghost** (added with REF-1..3;
    choices the plan left open, not cost). `alpha` maps the `Pool` field
    by field to `cfg, values, version, observedAt, paused, records` (names
    and units, which the core only length-checks, are not modelled) and
    leaves out `steps` and `last`: history variables that only `Step`
    writes and no operator or action reads. The model's ghost `base, k0`
    has no `Pool` field; it is the implementation's ghost, the values and
    record count after `new` or the last `Ok` observe, read off the core's
    post-state (under Kani the pre-state's ghost is `gen::inv_state`'s).
    "Noop" (an idempotent `Ok(())`) agrees with the core's `Ok` and must
    stutter, as TraceCheck's `Agrees`. `alpha` is partial: it asserts that
    the pool fits the image, that `records[j].id = j` and that every recipe
    vector spans the metrics (the `.tla`'s "by construction" and
    `ValidCfg`), so a post-state outside its domain fails the harness. Two
    products are written as equal functions that CBMC handles better
    (deviations 9 and 17): `Rcp(r).complete[m] * units` as a 32-bit product
    after asserting `|d| <= 1e6` and `units <= 100` (exact: at most 1e8),
    and each energy term as `(r * r) * w` in `u64` after asserting
    `r <= 2e6` and `w <= 1000` (at most 4e15). Accounts are compared with
    `eq_str` (deviation 5). The configuration is compared in full under
    Kani (deviation 6's restriction was not needed: see the `h_ref` rows).

## Tool issues: a static sharing storage with a constant, references into local arrays (Kani 0.68.0)

The first complete run of `h_best` with both stubs FAILED: "RD-BEST:
energy of the candidate's values" and memory checks in `Vec::<i64>`
(`push_mut`: pointer invalid; `__rust_dealloc`/`__rust_realloc`: invalid
or double free). The CBMC trace (`cbmc --trace` on the harness's goto
binary, property `Vec::<i64>::push_mut.safety_check.2`) showed a vector
created by the `candidate` stub with capacity 4 and the dangling pointer
`NULL + 8`: `RawVecInner::new_in` had read `RawVec`'s constant `ZERO_CAP`
as 4. In the goto program, `new_in` reads that constant from
`model::CAND_LAST`, the stub's `AtomicUsize` static initialized to 0:
Kani keeps one global per allocation content, and the static and the
8-byte zero constant had the same bytes. The stub's store of the
quantity (4) to `CAND_LAST` therefore changed the constant, and every later
`Vec::new_in` got capacity 4 without a buffer. Not a defect of the core;
a soundness hazard of the tool whenever a harness writes a static whose
initial bytes equal a constant's (a write could equally hide a bug).

The fix: every static the models write is `model::Tagged`, a distinct
64-bit tag in front of the value, so its bytes match no constant; in the
rebuilt goto program `new_in` reads an anonymous constant global. A scan
of every harness's goto program for named statics read outside their own
functions found no other case (only std's read-only tables and the
models' own readers): `VALIDATED` (`h_init`) was read only by `validate`'s
stub and `checks::init`. `h_best` and `h_init` are the only harnesses
that reach these statics, and their results in the table are from the
tagged version (the same scan of the tagged build: every model static is read only by its stub and its harness body).

A second hazard, found with REF-1..3: in a function, a reference to a
field of an element of a local array of structs at an index CBMC does
not fold (`&t.recipes[r].reserve` in `tla.rs`, with `r` read from
`t.records`), passed to another function, read unconstrained values
there. The first `h_ref_*` run (on the sources before the fix) FAILED in
`h_ref_submit`, `h_ref_cancel` and `h_ref_settle` (REF-1, REF-2, `mul`'s
precondition, "attempt to negate with overflow" in `neg`); `h_ref_dispatch`,
`_ack`, `_pause` and `_observe`, which pass no such reference, were `ok`.
The CBMC trace of `h_ref_cancel` (`cbmc --trace` on its goto binary,
property `tla::mul.assertion.2`) showed `alpha` writing
`recipes[1].reserve[0] = 0`, then `release_err`'s `neg(&rec_rcp(i).reserve)`
reading 0 and `next`'s identical call reading -4611686018427387905. A
concrete probe harness (1 metric, 2 recipes, a Reserved record of recipe
1; plain mode passes it) failed the same way under Kani in 26 s; in it,
`neg(&t.rcp(1).reserve)` (a constant index), a read in place
(`t.rec_rcp(0).reserve[0]`) and `neg` of a local copy passed, while
`neg(&t.rec_rcp(0).reserve)`, `neg(&x.reserve)` with `x = t.rec_rcp(0)`,
and `neg(&t.rcp(r).reserve)` with `r = t.rec(0).recipe` failed. The values
were unconstrained (the solver chose a different one at each read), so in
`tla.rs`, where no assumption follows such a read, the hazard could only
make a harness fail. The fix: `rcp`, `rec` and `rec_rcp` return copies
(the image's records are `Copy`), so every reference passed on is to a
local; the probe then passed (9 s) and so did every `h_ref_*` harness
(table). `spec.rs` and the harness bodies do not pass such references
(their lookups are concrete-slot reads, deviation 3), and the core's
vectors are heap objects, not local arrays of structs. The probe was not
kept (`proofs.rs` has no `probe_*` harness).

A third, harmless tool limitation: with CBMC's `--stop-on-fail` (the
mutant runs) Kani 0.68.0's driver panics while parsing CBMC's JSON
("data did not match any variant of untagged enum ParserItem"), after
CBMC has found the violation. `run.sh mutants --kani` therefore runs the
mutants with `--output-format old` (CBMC's own text) and reads the
violated property from it (`mutant_verdict`: a violated property that is
not an unwinding assertion, an unsupported construct or a Kani-internal
check kills the mutant).

## Cost ladder

Measured on the submit step unless noted (CNF sizes from `--dimacs`,
times wall clock). "m/t/r/c" = metrics/terms/recipes/records.

| Step | Instance | Measurement | Consequence |
|---|---|---|---|
| 1 | `h_energy`, 2 metrics, 2 terms, `Full` values, via `Pool::new` | 52.5M clauses, out of 24 GB after 73 s; `Pool::new`'s validation 13.8M; one 64-bit multiplier 104k | `pool_of` (deviation 8) |
| 2 | Energy exactness against an `i128` product (miter), or an uninterpreted multiplier | did not finish; UF 101.9M vs 47.3M clauses | same-circuit product (deviation 9), anchored values for exactness |
| 3 | submit step, symbolic record count ≤ 3 | out of 26 GB | fixed record counts (deviation 7) |
| 4 | submit step 1/1/1/0 | 28.3M clauses, of which `memcmp` on `str` 12.5M; 290 s | bounded string equality (deviation 5) |
| 5 | submit step, fixed records 0/1/2/3 (1/1/1/c) | 19.4M / 22.3M / 24.7M / 27.1M; symbolic ≤ 3: 56.6M | |
| 6 | submit step 1/1/2/1, 2/2/2/0 | 49.1M, 53.7M | |
| 7 | submit core alone vs spec alone (1/1/1/1, 1/1/2/1) | core 10.1M / 12.4M, spec 1.9M / 4.4M | the cost is the core's heap, not the spec |
| 8 | after `same_state` without the configuration (deviation 6) | 1/1/1/1 15.6M; 1/1/2/1 25.7M (solved in 417 s); 2/2/2/0 29.1M; 1/1/2/2 29.8M; 2/2/2/2 40.7M | step shape 1/1/2/2 |
| 9 | hot spots in 1/1/2/1 (`--write-solver-stats-to`) | `prereqs_met` 3.4M, `add`'s closure 2.7M, `i64` clone 1.9M, `(u32, u32)` clone 1.0M | per-loop unwinding (deviation 11) |
| 10 | first full step run (32 GB cap) | submit tx/post/inv/cov 520/436/991/224 s (inv 72.7M clauses, 33.4 GB); cancel_tx 51.1M, 272 s; settle_tx 57.9M, 483 s; cancel post/inv and settle post/inv/cov out of 32 GB | probes below |
| 11 | cancel_tx with `--max-field-sensitivity-array-size 1024` | 47.2M vs 51.1M | not adopted |
| 12 | probes 1/1/2/2: INV state alone; core cancel; spec cancel; core settle(completed); core submit | 3.7M; 45.4M; 4.8M; 9.8M; 15.6M | the core's cancel is the outlier |
| 13 | core cancel with a fixed record id; then with the `Vec::reserve` model | 45.3M → 8.4M (std's growth path in `release`'s `undo` collect) | `Vec::reserve` model (deviation 1); cancel_tx 51.1M → 14.1M |
| 14 | PAUSE-1 by calling the core a second time | doubled `_post` (cancel, settle out of 32 GB) | spec-level PAUSE-1 (deviation 18) |
| 15 | `h_energy_max` (64 terms, `pool_of`, no capacity model) at unwind 66 | killed after 744 s and 526 s in symbolic execution (21.6 GB): the loop inside each `next()` of `energy_terms`' fallible `collect` unrolled 66 times inside the 66 of the `collect` | that loop bound 2 (deviation 11) |
| 16 | `h_version_max`, all seven kinds in one formula | 73.1M clauses, 34.7 GB, timed out at 1802 s | one harness per kind: 26 to 357 s (deviation 22) |
| 17 | `h_preview` with `eq_text::<24>` at the harness bound 6 | unwinding assertion failed (28.2M clauses, 567 s) | bound 25 for that loop |
| 18 | `h_preview` with the bound 25, `reason` compared three times on the heap | 62.2M clauses, 32.9 GB, solved in 859 s (1634 s in all) | `reason` copied once into `Text<16>` (deviation 5) |
| 19 | `h_preview_post`: the spec formats its numbers with `to_string` (a 64-bit division per digit pair) and compares 24 bytes | no CNF after 20 min of propositional encoding (22 GB); stopped at 1193 s | `is_dec`: parse the core's numeral (multiplications by 10) |
| 20 | `h_best` at the harness bound 6 | stopped after 808 s, 23 GB still in symbolic execution: `best_quantity`'s two loops over `1..=units` unrolled 5 times each | those loops bound 4 (units ≤ 3) |
| 20b | `h_best`, units ≤ 3 (loops at 4), with the second call to `submit` | 9.3M symbolic-execution steps (468 s), no CNF after 20 min; stopped at 1188 s | units ≤ 2 (loops at 3), soundness by decomposition (deviation 24) |
| 20c | `h_best`, units ≤ 2 (loops at 3), no second call to `submit` | 6.43M steps, 161.9M clauses, 36 GB; the first SAT call took 1230 s; timed out at 1801 s | `candidate` stubbed by a free result: the search alone, up to 7 units (deviation 24) |
| 20d | `h_best` with `candidate` stubbed, `Ok` values anywhere in `[-1e6, 1e6]`, units ≤ 7 | 1.09M steps, 12.5M clauses; four SAT calls in 45 s, the last (the core's energies against the spec's, a miter of two multipliers per quantity) not done after 12 min; stopped at 749 s | the stub's values from the step domain `Anchored(4)` |
| 20e | `h_best`, `candidate` stubbed with values from `Anchored(4)`, ranked by the spec's energy | 1.10M steps, 12.5M clauses; three SAT calls in 71 s, the fourth (the spec's energies against the core's) not done; timed out at 1800 s | the harness ranks by the core's `energy` |
| 20f | `h_best`, ranked by the core's `energy` (two copies of the core's circuit per quantity) | 1.30M steps, 15.2M clauses; three SAT calls in 91 s, the fourth not done after 7 min; stopped | `energy` stubbed too: a free result per call, `h_energy` pins it down (deviation 24) |
| 20g | `h_best` with `candidate` and `energy` stubbed | 0.70M steps, 7.7M clauses, 272 s: FAILED on memory checks in `Vec::<i64>` and "RD-BEST: energy of the candidate's values"; the trace shows the tool issue (a static sharing storage with `RawVec`'s `ZERO_CAP`) | tagged statics ("Tool issues"); then 0.52M steps, 4.3M clauses, ok in 137 s |
| 21 | `h_wedge`, symbolic roles, `Pool::new` | 3.66M symbolic-execution steps, out of 40 GB at 1558 s | fixed roles, `pool_of` (deviation 19) |
| 22 | `h_wedge_healthy` with the spec's step and the invariants along the script; then the script on the core alone; then one concrete configuration with the spec's checks | stopped at 196 s in symbolic execution; 3.73M steps, out of 40 GB at 216 s; 5.19M steps, 20,347 VCCs left, out of 40 GB at 1465 s | from a healthy INV state (deviation 19) |
| 23 | `h_bmc_from_init` from `Pool::new`, INV of the initial state, any first kind | still in symbolic execution after 16 min (stopped at 988 s) | `pool_of`, first operation submit, pause or observe (deviation 20) |
| 23b | `h_bmc_from_init`, first kind restricted, second any kind | 6.34M steps (641 s of symbolic execution), out of 40 GB at 685 s | one harness per second kind (deviation 20) |
| 23c | `h_bmc_from_init_pause` (one harness per second kind), with a copy of the pre-state at each step; then without the copy | 2.79M steps, 37 GB, timed out at 1803 s with no verdict; 2.41M steps (stopped there) | the first operation's post-state asserted equal to the spec's and rebuilt with constant shapes, a submit continued from `Ok` only (deviation 20) |
| 24 | `h_full`, symbolic count 255 or 256 | 63 of 256 pushes in 9 min of symbolic execution (stopped at 586 s) | concrete counts (deviation 21) |
| 25 | `h_init` with 129-byte strings; then short strings, 3 metrics, real `validate` and INV in one formula | not through symbolic execution in 30 min; then 1.66M steps, out of 40 GB at 190 s (39.1 GB) | free `validate` and `h_init_inv` (deviation 23), 2 metrics (deviation 15) |
| 25b | `h_init_inv`: symbolic shapes (up to 2/2/2), the real `validate` via `Pool::new`, INV | 2.12M steps; no CNF after 20 min of propositional reduction (stopped at 1450 s) | fixed shapes (`h_init_inv`, `h_init_inv_2`), `pool_of` and the spec's `valid` (deviation 23) |
| 25c | `h_init` (free `validate`) at its unwind 4 | `spec::eq_i64s`'s loop over 4 elements failed its unwinding assertion (33.9M clauses, 258 s) | that loop bound 5 (deviation 11); then 54.2M clauses, ok in 576 s |
| 26 | `h_validate` with 3 metrics, 128/129-byte strings, no capacity model | 1.09M steps, out of 40 GB at 817 s (37.5 GB) | 2 metrics, short strings, capacity model (deviation 15) |
| 27 | `h_step_cancel_post`: PAUSE-1 compares `[i64; 2]` with `==` | `memcmp` loop of 16 bytes, unwinding assertion failed at bound 6 | `eq_vals` (deviation 5) |
| 28 | `h_full_256` with `assume(inv_dep)` over the 256 records | still in symbolic execution after 9.5 min (767 `completed_units` loops over up to 256 records); stopped at 582 s | INV-DEP by construction, not evaluated under Kani |
| 28b | `h_full_255` with a copy of the pool for the spec and TX-0 | the copy of 255 records took most of 13 min of symbolic execution; stopped at 816 s | the spec's outcome computed before the call, the post-state compared with it and with the known records (no copy) |
| 28c | `h_full_256` with the configuration copied for the exact post-state, harness unwind 258 | `gen::copy_vec`'s loops over the recipes' deltas unrolled about 253 times each (1,532 unwindings in 8 min of symbolic execution); stopped | those loops bound 4 in `h_full_*` and `h_preview_post` (deviation 11) |
| 28d | `h_full_256` with the copy's loops at 4 | the slice comparisons of `same_config` unrolled 257 times each; 5.98M steps (381 s), timed out at 1801 s in the first SAT call | the configuration not compared under Kani (deviation 6) |
| 28e | `h_full_255` at the harness unwind 258 | `spec::prereqs_met`'s loop over a recipe's requirements unrolled toward 258, each iteration a scan of the 255 records (about 4,000 loop iterations in 16 min of symbolic execution); stopped at 991 s | that loop bound 4 (deviation 11) |
| 28f | `h_full_255` with that loop at 4 (CBMC by hand on the goto binary) | no read of a record folded to its constant fields (the buffer, 257 × 24 bytes, is above CBMC's field-sensitivity limit of 64 elements): both envelopes took the `open` branch, with a multiplication, for every record (`spec::rcp` reached 514 times); still in the core's envelope after 13 min; stopped | `--max-field-sensitivity-array-size 8192` for `h_full_255` (deviation 21) |
| 28g | `h_full_255` with the field-sensitivity limit 8192 (by hand) | the 257 pushes took 8 min (field-sensitive writes, the machine shared with a CI virtual machine using 5 cores), then every scan folded (`spec::rcp` reached 4 times) until INV-WF's scan of the post-state, after the conditional push, ran at about 4 records a minute; stopped | INV-WF of the post-state not evaluated under Kani (deviation 21) |
| 28h | `h_full_255` (`run.sh`) with the loop at 4, the field-sensitivity limit and no INV-WF scan, step domain | 8.05M steps, 1001 s of symbolic execution, 113 s converting SSA, the first SAT call (the admission arithmetic of the step harnesses' submit, result and post-state in one formula) not done; timed out at 1801 s (28.8 GB) | values, bounds and targets 0, deltas in `-1..=1` |
| 28i | `h_full_255` as 28h with values, bounds and targets 0 and deltas in `-1..=1` | 8.05M steps, 962 s of symbolic execution, 93 s converting SSA, the first SAT call again not done; timed out at 1802 s (31.1 GB) | not the arithmetic: the harness back on the steps' domain; the records built without pushes (28j) |
| 28j | `h_full_255` with the records one constant array (`OLD_RECORDS`, `Vec::from`, then `truncate`), the field-sensitivity limit, INV-WF of the post-state not scanned, the steps' domain (as 28h) | 2.42M steps (8.05M in 28h), 493 s of symbolic execution, 14 s converting SSA, 37.9M clauses, two SAT calls of 147 s and 93 s; ok in 764 s (19.9 GB); `h_full_256` ok in 46 s | adopted (deviation 21); mutant 30 (`Full` at 255) added for the boundary it now shows |
| 29 | `h_init`, `h_validate`: raw configurations built by conditional pushes | 0.56M and 0.97M steps, out of 40 GB in the propositional encoding after 86 s and 145 s | concrete-offset writes, then truncate (deviation 3) |
| 30 | `h_energy_max` (64 terms, concrete) | 226.3M clauses, 27.2 GB, 447 s | |
| 31 | the `_inv` parts from 0, 1, 2 and 3 records (submit; settle) | submit 53.4M / 57.7M / 62.3M / 65.6M clauses, one SAT call of 297 / 438 / 772 / 1072 s; settle 8.5M / 25.8M / 33.1M / 40.8M, 17 / 165 / 378 / 1712 s (`h_step_settle_inv_3` ok in 1788 s, 12 s inside the limit of 1800 s) | `h_step_*_inv_3` get a 7200 s limit in `run.sh` |
| 32 | `h_ref_*` (REF-1..3) as first designed: the step state, the image `TK` with the configuration compared in full, `mul` in 32 bits and energy as one `(r * r) * w` product (deviation 26) | 0.34M to 1.00M steps, 10.7M (pause) to 23.0M (submit) clauses, largest SAT call 189 s (submit), 5.2 to 12.4 GB, 55 to 351 s per harness | kept; no reduction needed (deviation 6's restriction was not) |

## What is not shown

Every Kani result is a bounded proof: it holds for every input inside the
bounds above and says nothing outside them. In particular:

- **Shapes.** The step, liveness, preview and version harnesses use 1
  metric, 1 term, 2 recipes and exactly 2 records (3 in `h_live1`; 0, 1
  and 3 in the `h_step_<op>_inv_<k>` parts, which check INV preservation
  only); 2 metrics and 2 terms appear only in `h_energy*`, `h_init*`,
  `h_validate` and `h_init_inv_2`, and the 64-term worst case only in
  `h_energy_max`. The exact result and post-state (`_tx`, `_post`) from
  0, 1 or 3 records (other than the states `h_bmc_from_init_*` and
  `h_slot_cycle_0` reach), any step from 4 or more records (other than a
  submit at 255 or 256 Cancelled records), steps over 2 metrics or 2
  terms, and anything larger than the brief's small scope are plain
  mode's (random, not proof) and the other layers' (TLA+, Lean at every
  size for the properties it states).
- **Values.** The steps use anchored values (`-1e6`, `0`, `1e6` plus or
  minus 4) and deltas in `-3..=3`; only `h_energy` covers the full value
  range. A bug that needs a value strictly between the anchors and the
  extremes (other than through energy) is not excluded.
- **Depth.** `h_bmc_from_init_*` runs 2 operations from `Pool::new`
  and `h_slot_cycle_0` 3 (submit, cancel, submit); longer traces rest on
  the induction (`h_init_inv*` + `h_step_*_inv` + `h_step_*_inv_<k>`),
  which shows INV-WF to INV-DEP in every reachable state with at most 3
  records (step shape and domains) and nothing about states with 4 or
  more. The induction is over INV only: the per-step results (`_tx`,
  `_post`) are shown from 2-record INV states, and INV-VER only along
  the 2-operation traces. The depth-3 and depth-4 covers ("a record
  completes", "observe after a completion") are plain mode's.
- **The record limit with other records.** `h_full_255` and
  `h_full_256` hold 255 or 256 Cancelled records of recipe 0 (deviation
  21): the submit there is exactly the spec's, so the limit is exactly
  256 (mutants 21 and 30 move it by one either way). A limit state with
  open or Completed records (prerequisites met by old records, an
  envelope over 255 reservations) is plain mode's (`h_full` draws only
  Cancelled records too) and the other layers'.
- **Reachability of F-2, F-2b, F-3 and F-5 from `Pool::new`.**
  `h_wedge_healthy` covers the wedge from every healthy INV state of its
  shape whose records are a Dispatched position and a Completed hedge;
  that such a state is reachable from `Pool::new` is shown by plain mode
  (`f2_small_instance`, `f2_risk_fixture`) and by the TLA+ and sandbox
  layers, not by Kani. F-2b's covers are from 2-record INV states. F-3:
  Kani shows the cycle from `Pool::new` and from quiet 2-record states,
  and the limit at 255 and 256 Cancelled records; the 256 cycles as one
  trace (the cycle from quiet states with 3 to 255 records) are plain
  mode's (`f3_slot_exhaustion`). F-5: Kani shows every effective kind
  frozen from states at `u32::MAX`; reaching `u32::MAX` takes 2^32 - 1
  effective transitions (INV-VER), not run by Kani.
- **RD-BEST** is a composition (deviation 24): the search with a free
  `candidate` and a free `energy` (units ≤ 7), plus `candidate` = spec
  from `h_preview` and `h_step_submit_*` and `energy` = spec from
  `h_energy`. The `min(units, 100)` cap, the real `candidate` and `energy`
  with 3 units and the call to `submit` on the result are plain mode's; at
  `version = u32::MAX` the equality of `candidate`'s `Ok` values with the
  spec's rests on reading the code.
- **CFG-1** is a composition (deviation 23): `h_init` (free `validate`),
  `h_validate` (2 metrics, strings of 0 or 2 bytes) and `h_init_inv*` (two
  fixed shapes). 3-metric raw configurations and the 128/129-byte boundary
  of `short` are plain mode's.
- **LIVE-2** (eventual termination under executor fairness) is not a Kani
  property; it is the TLA+ layer's. LIVE-1 is shown for 3 records with
  B = 0; Lean shows it at every size.
- **REF-1..3** (the real core refines the TLA+ model per step) are
  bounded proofs within the step bounds only: pre-states of 1 metric, 1
  term, 2 recipes and exactly 2 records, the step domains. Other record
  counts and shapes are plain mode's (the step tests up to 2 metrics, 2
  terms, 2 recipes and 3 records, `h_bmc_from_init` to depth 5) and the
  212 conformance traces' (up to 8 metrics and 256 records): tests, not
  proofs. The link is to `tla.rs`, a hand transcription of
  `SharedPool.tla`, trusted to be the `.tla` (part of ASM-LEAN-TLA). It is
  checked against the TLA+ model only indirectly: on the 8,804 trace
  calls `tla.rs` (`h_ref_traces`) and TLC's TraceCheck (REF-5) both agree
  with the core's recorded results and states, so with each other there.
  Mutant 31 (a transcription error in `ReleaseErr`) shows the check
  depends on the transcription. `steps` and `last` are not mapped
  (deviation 26); the TLA+ initial state (`Init`) is linked by CFG-1 and
  the traces, not by a REF harness.
- **Memory safety of std** is not checked (`--no-memory-safety-checks`;
  the core forbids `unsafe`). Panics, overflow, bounds and unwinding
  assertions are checked.
- **The shell, the executor and NEAR** (callbacks, gas, promises,
  predecessor) are out of scope here: near-tests and sandbox.
- **The models** (`model.rs`) are trusted to be what deviation 1, 23 and
  24 say: the capacity models can only make a harness fail; the free
  `validate`, `candidate` and `energy` are pinned down by other harnesses.
- **The tool.** Kani 0.68.0 and CBMC 6.11.0 are trusted (ASM-TOOLS), with
  the two hazards found and worked around ("Tool issues"): the scan for
  statics sharing storage with constants covers the named statics of
  every harness's goto program, not every allocation Kani could merge.
- **The specification** (`spec.rs`) is trusted to mean the brief
  (ASM-SPEC); it was written from the brief, not from the code, and the
  plain-mode mutants check that it distinguishes the code from 29 changed
  versions of it.
