# formalver

The approval contract's core is proved. Nobody has signed the spec.

This repo holds those proofs, and room for the next ones. Three labels. We will use them as written.

| Label | Means |
|---|---|
| Production Ready | Pinned build, locked deployment, spec signed by someone who did not write the code. |
| Development Ready | Proofs pass on the pinned source. You can rerun them. Spec unsigned. Not a deployment attestation. |
| In-Progress | Not a result. A passing run may prove nothing. |

Nothing here is Production Ready.

| Project | Label | What it is |
|---|---|---|
| [near-approval](projects/near-approval/strategy.md) | Development Ready | Verification of [trust-framework](https://github.com/difflabai/trust-framework) `contracts/approval` |
| [shared-pool](projects/shared-pool/strategy.md) | In-Progress | Verification of [shared-pool-controls](https://github.com/difflabai/shared-pool-controls) PR #1 (pool-core and its NEAR contract) |
| [ironclaw](projects/ironclaw/strategy.md) safety modules | In-Progress | Scaffold of [nearai/ironclaw](https://github.com/nearai/ironclaw) `src/safety/` |
| [strategy](strategy/README.md) | In-Progress | A plan for deriving a verification strategy from a codebase. No extractor yet. |
| [near-proofs](near-proofs/README.md) | In-Progress | Submissions to [NEAR Proof Arena](https://github.com/ilblackdragon/near-proof-arena). None yet. |

[MIT](LICENSE), copyright Differential AI Lab, same notice as trust-framework. The Verus twin in `projects/near-approval/verus/` is a copy of `approval-core` plus annotations.

How the layers fit, and when to use Kani or Verus: [`docs/architecture.md`](docs/architecture.md).

Tool versions are pinned in [`tools/versions.env`](tools/versions.env), and GitHub Actions use full commit SHAs. [`near-approval`](.github/workflows/near-approval.yml) verifies only the layers affected by the complete PR or push diff; documentation-only changes run no verification jobs. Shared inputs select their dependent layers (for example, extracted Prolog facts also feed the plain and Lean checks).

[`near-approval-watch`](.github/workflows/near-approval-watch.yml) owns the schedule. It compares trust-framework's approval `core/` and `contract/` crates and workspace build inputs against `.github/approval-seen`; unrelated projects, upstream sandbox tests, and documentation do not trigger re-verification. A changed contract calls `near-approval` at that exact upstream tip. An open recording PR for equivalent contract code suppresses repeat verification even if unrelated upstream commits arrive. Only successful verification opens the baseline-update PR; the reviewed verification pin stays unchanged. Bot PR workflows may require **Approve workflows to run**. The Actions PR creation/approval setting must be enabled; only the watcher's recording job requests write access.

The sandbox checks lockfile compatibility before installing tools or building Wasm. Its diagnostic artifact contains both lockfiles, the selected source SHA, a structured mismatch report, and available test output. Scheduled upstream runs adapt only the expected artifact fingerprint; export-surface and behavioral observations stay strict. Pinned runs retain the independent reviewed Wasm hash.

## near-approval

Development Ready. Pin [`249f932d84b91fbc6f82abd0668cac6c0503fc42`](https://github.com/difflabai/trust-framework/commit/249f932d84b91fbc6f82abd0668cac6c0503fc42), trust-framework `main` (2026-11-02). `core/src/lib.rs` and `contract/src/lib.rs` match the previous pin `af2c704`. `near-sdk` is built without its unmaintained `wee_alloc` default, which changes `contract/Cargo.toml`, the lockfile and the contract README.

Reproducible wasm of this pin, from the sandbox job's `cargo near build reproducible-wasm` of that commit:

| | |
|---|---|
| sha256 | `3a3be0b8be6338555436b7cdd6a4ded2cb60544ccd34a167aaeaa971d88e0323` |
| NEAR code hash | `4vKbxYH8PY7w1vKVpXteRYKomwpK6Yx53gYfbPPetbfx` |

The build records the commit, so this hash is not the hash of `af2c704` (`4fPDQYaQdSn6SkD7WYgD5pUrU1d6Ev8FQqE7iEYvUtyJ`). Same logic. Different artifact.

`approvals.difflabai.testnet` is a demonstration, owned by `difflabai.testnet`, deployed from `081a3a6`. Its code hash is `5G334oPHzjDvPLXKUSstbaf3BzUPaj1sWZnDhy5Baauv`. The account still has a full-access key, so it can be redeployed. It is not this pin, and a matching code hash on one read is not a lock.

Kani, TLA+, Lean, Prolog and Verus pass. Every Kani and Verus property stays `in-progress`. [`status.toml`](projects/near-approval/status.toml) refuses `verified*` until `[review] spec_reviewer` names a person who did not write `approval-core`. That review happens after these repos are public, and it is an approval recorded by the contract itself. It is not in the log yet. A green check here is not a signature.

The property list is the status file. The plan is [`projects/near-approval/strategy.md`](projects/near-approval/strategy.md).

### Setup

All commands run from the repository root.

```bash
git submodule update --init projects/near-approval/source-mirror
./tools/scripts/check-pin.sh near-approval           # submodule = pinned_commit, file hashes match
```

Needs Rust (`RUST_TOOLCHAIN` in `tools/versions.env`), Python 3.11+, and Java 17+ for TLA+.

### Kani: the real core, bounded ([strategy §6](projects/near-approval/strategy.md))

The harnesses in `projects/near-approval/kani` run the real `approval-core`. The same harness bodies run in two modes.

```bash
# Plain mode: random tests, no Kani needed (not a proof)
(cd projects/near-approval/kani && cargo test --release)

# Kani: install the pinned version, then run every harness
cargo install --locked kani-verifier --version 0.68.0 && cargo kani setup
./tools/scripts/run-kani.sh near-approval            # or name harnesses: ... h_step_approve

# Loop bounds (U-1): every loop's bound comes from a constant
python3 tools/scripts/kani-loops.py projects/near-approval/kani --codegen

# Core mutants: each must be killed (two equivalent ones must survive)
./tools/scripts/run-mutants.sh near-approval         # plain mode
./tools/scripts/run-mutants.sh near-approval --kani  # plus each mutant's Kani harness
```

Harnesses are memory-bound: run them one at a time on a 16 GB machine. The full matrix takes about 2 hours on one Mac. Results and run times are in [`kani/RESULTS.md`](projects/near-approval/kani/RESULTS.md).

### TLA+: every call sequence ([strategy §17](projects/near-approval/strategy.md))

```bash
./tools/scripts/run-tla.sh near-approval             # fetches pinned TLC/Apalache; or name checks: safety liveness apalache trace mutants
./tools/scripts/run-mc3.sh near-approval             # MC-3: Prolog graph = TLC graph (~40 min; nightly in CI)
```

### Lean: the model at every size ([strategy §18](projects/near-approval/strategy.md))

```bash
export PATH="$(./tools/scripts/get-lean.sh):$PATH"   # pinned Lean release, sha256-checked, no elan
./tools/scripts/run-lean.sh near-approval            # build, audit, canary, guards, replay, graph, mutants
./tools/scripts/run-lean.sh near-approval build audit   # or name checks
```

`replay` (REF-5L) needs the submodule and Rust. `graph` (MC-4) needs Java.

### Prolog: the requirements oracle ([strategy §8](projects/near-approval/strategy.md))

```bash
cargo install --locked scryer-prolog --version 0.10.0

# Generated fact files are current
python3 tools/scripts/tla-facts.py projects/near-approval --check
(cd projects/near-approval/kani && cargo test --release --locked facts)

# Requirement checks C-1..C-10, C-2t, MC-1
./tools/scripts/run-prolog.sh near-approval

# MC-2: real-core traces on step/4, and step/4 traces on the core
(cd projects/near-approval/kani &&
  cargo test --release --locked mc2_core_traces &&
  (cd ../prolog/verification &&
    scryer-prolog mc2.pl -g "(replay('$PWD/../../kani/target/mc2/core.txt') -> halt(0) ; halt(1))" </dev/null &&
    scryer-prolog mc2.pl -g "(generate('$PWD/../../kani/target/mc2/prolog.txt', 60) -> halt(0) ; halt(1))" </dev/null) &&
  cargo test --release --locked mc2_prolog_traces -- --nocapture)
```

## shared-pool

In-Progress. Pin [`a4bb5c3`](https://github.com/difflabai/shared-pool-controls/commit/a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7), a head of shared-pool-controls PR #1. The PR is not merged. Its two later commits (to `4b68c4e`, checked 2026-11-12) change only `README.md` and `ui/`, none of the files [`status.toml`](projects/shared-pool/status.toml) hashes. Re-pin when the PR merges.

The label is In-Progress because the pin is an unmerged PR head, the Kani layer is still being built, and nobody has signed the spec. It does not mean the runs below are empty. TLA+, Lean, Prolog and near-tests carry vacuity guards and fail without them: TLC witnesses must be violated, Lean and Prolog canaries must fail, and every checked-in mutant must be killed.

[`conformance/`](projects/shared-pool/conformance) runs the pinned `pool-core` and generates 212 traces (8,804 calls) from it. TLA+, Lean and Prolog are separate models that replay its traces. The NEAR shell (near-tests) wraps the real core and replays them too. All four match every trace's results and post-states.

- TLA+: no error in 2,306,738 distinct states (TLA-SAFE) in a small universe (2 metrics, at most 3 records). Every witness is reachable. LIVE-2 holds on the completion path and fails as F-1 and F-2, as required. 31 of 31 spec mutants killed. No Apalache inductive check (TLA-IND is open).
- Lean: `Inv`, the step properties and LIVE-1 proved for states of every size on the Lean transcription of the core (not the Rust code). F-1 proved permanent (`f1_forever`). 40 of 40 headline theorems use only `propext`, `Classical.choice` and `Quot.sound`. 16 of 16 mutants killed.
- Prolog: C-1 to C-6 pass, with F-2 and F-4 reproduced by C-5. MC-1 explores three universes (3,740, 3,856 and 630 states). MC-2: 0 divergences. COV-2: the core's preview and best_quantity equal the model's on 36,797 requests. 33 of 33 mutants killed (2 of them mutate the core's reads).
- near-tests: all 29 tests pass, on the host path and on two wasm builds (plain cargo and `--cfg near`). SH-8 alone makes 80,000 random host calls. 21 of 21 shell mutants killed.
- Sandbox: RT-PRED, RT-PRIVATE, RT-CALLBACK, RT-REVERT, RT-RACE and RES-1 pass on both wasm builds. The worst pool receipt is 12.56 Tgas at 256 records. RT-WEDGE reproduces F-1.
- Kani: no result yet, and no CI job.

Two findings are high. F-1: after an `observe` puts a metric out of bounds, a dispatched hedge can be neither settled (`Bounds` both ways) nor cancelled (`Pending`), and every later `observe` fails `Pending` (trace 0). F-2: in the supplied `risk` fixture, with every metric in bounds, once a hedge that relied on a position's reservation has completed, the executor's honest `settle(false)` for the unexecuted position fails `Bounds` and `cancel` and `observe` fail `Pending`, contrary to `docs/spec.md` (trace 209; variant F-2b fails `Arithmetic` instead, trace 208). The other findings, F-3 to F-6 and the shell's NT-F1 to NT-F4 (NT-F1 is SB-1), are in [strategy §4](projects/shared-pool/strategy.md). Every core finding but F-5 (version u32::MAX, out of reach of a trace) has a conformance trace.

[`shared-pool`](.github/workflows/shared-pool.yml) CI runs the pin check, status-lint, the trace `--check` and the runners of TLA+, Lean, Prolog, near-tests and the sandbox. The sandbox job runs only on manual dispatch. Kani is not in CI yet: its jobs are added, sized from its `RESULTS.md`, when the layer lands.

```bash
git submodule update --init projects/shared-pool/source-mirror
./tools/scripts/check-pin.sh shared-pool
(cd projects/shared-pool/conformance && cargo run --release --locked -- --check traces/core.txt --reads-check traces/reads.txt)
projects/shared-pool/tla/run.sh safety liveness trace mutants   # Java 17+
projects/shared-pool/lean/run.sh                                # fetches Lean via get-lean.sh
projects/shared-pool/prolog/run.sh                              # scryer-prolog 0.10.0
projects/shared-pool/near-tests/run.sh all                      # Rust 1.98, wasm32 target
projects/shared-pool/sandbox/run.sh                             # fetches near-sandbox 2.13.4
```

## ironclaw

In-Progress. The Verus layer models ironclaw's sanitizer. It does not check the source. `assume(false)` still stands in for proof steps, so a passing run proves nothing. The submodule gitlink is `d313f44`. [`status.toml`](projects/ironclaw/status.toml) still records `34550add`. That drift is known, and unfixed on purpose until the proofs are real.

### Plain Rust (no Verus)

```bash
cargo build   # the model crate as plain Rust types, no proofs
cargo test    # 8 unit tests for the sanitizer model
```

### Verus

Install a Verus release (zip with `verus` and Z3) from [verus-lang/verus releases](https://github.com/verus-lang/verus/releases) and put it on `PATH`. No version is pinned yet (`VERUS=` in `tools/versions.env`). To build from source instead: clone the repo, then in `verus/source` run `./tools/get-z3.sh`, `source ../tools/activate` and `vargo build --release`.

```bash
verus projects/ironclaw/verus/src/lib.rs --crate-type=lib --cfg 'feature="verus"'
```

The `--cfg` matters. The spec and proof modules are behind `cfg(feature = "verus")`, and without it Verus checks only the plain types.

To make progress, replace `assume(false)` one proof at a time, rerun `verus` after each, and update `projects/ironclaw/status.toml`. Do that before you tell anyone this proved something.

### Prolog

```bash
cargo install --locked scryer-prolog --version 0.10.0
./tools/scripts/run-prolog.sh ironclaw                     # all test files
./tools/scripts/run-prolog.sh ironclaw test_sanitizer.pl   # one file
```
