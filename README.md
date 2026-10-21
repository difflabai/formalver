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
| [ironclaw](projects/ironclaw/strategy.md) safety modules | In-Progress | Scaffold of [nearai/ironclaw](https://github.com/nearai/ironclaw) `src/safety/` |
| [strategy](strategy/README.md) | In-Progress | A plan for deriving a verification strategy from a codebase. No extractor yet. |
| [near-proofs](near-proofs/README.md) | In-Progress | Submissions to [NEAR Proof Arena](https://github.com/ilblackdragon/near-proof-arena). None yet. |

[MIT](LICENSE), copyright Differential AI Lab, same notice as trust-framework. The Verus twin in `projects/near-approval/verus/` is a copy of `approval-core` plus annotations.

How the layers fit, and when to use Kani or Verus: [`docs/architecture.md`](docs/architecture.md).

Tool versions are pinned in [`tools/versions.env`](tools/versions.env). CI (`.github/workflows/near-approval.yml`) runs the near-approval checks. On a PR, only the jobs whose inputs changed run (`tools/scripts/ci-areas.sh`).

## near-approval

Development Ready. Pin [`af2c704ecacdae809c18f27b0d645f771d45cdd3`](https://github.com/difflabai/trust-framework/commit/af2c704ecacdae809c18f27b0d645f771d45cdd3), trust-framework `main` (2026-10-21). `core/src/lib.rs` and `contract/src/lib.rs` match the previous pin `18f57cb`. The license fields in the `Cargo.toml` files, and the contract README, do not.

Reproducible wasm of this pin, from trust-framework's `reproducible wasm` job on that commit:

| | |
|---|---|
| sha256 | `36683fb50050cda51e6831e837f40a442cbe767b03d45cae8ac92602b7d9ef95` |
| NEAR code hash | `4fPDQYaQdSn6SkD7WYgD5pUrU1d6Ev8FQqE7iEYvUtyJ` |

The build records the commit, so this hash is not the hash of `18f57cb` (`BqEdznmvQiCG6XKTgpXbzEptV3GuL3VF274uUqkoseCv`). Same logic. Different artifact.

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
