# formalver

Formal verification of Rust repositories: the NEAR action-approval contract
in trust-framework, and IronClaw's safety modules.

## Projects

| Project | Target | Plan | Status |
|---|---|---|---|
| near-approval | [trust-framework](https://github.com/difflabai/trust-framework) `contracts/approval` (NEAR action-approval contract) | [strategy](projects/near-approval/strategy.md) | [status](projects/near-approval/status.toml) (core: Kani, TLA+, Lean, Prolog done; shell, sandbox, deployment next) |
| ironclaw | [nearai/ironclaw](https://github.com/nearai/ironclaw) safety modules | [strategy](projects/ironclaw/strategy.md) | [status](projects/ironclaw/status.toml) (Verus proofs scaffolded) |

[`strategy/`](strategy/README.md) is not a verification target: it analyzes a codebase's behavior (determinism, effects, trust boundaries) and derives which of the layers below a project needs.

How the layers fit together, and when to use Kani or Verus:
[`docs/architecture.md`](docs/architecture.md).

Submissions to [NEAR Proof Arena](https://github.com/ilblackdragon/near-proof-arena), aimed at the NEAR assumptions these projects rely on, go in [`near-proofs/`](near-proofs/README.md).

Tool versions are pinned in [`tools/versions.env`](tools/versions.env); CI
(`.github/workflows/near-approval.yml`) runs the near-approval checks below;
on a PR, only the jobs whose inputs changed run (`tools/scripts/ci-areas.sh`).

## near-approval: running the checks

All commands run from the repository root.

### Setup

```bash
# The pinned contract source (private: needs trust-framework access)
git submodule update --init projects/near-approval/source-mirror
./tools/scripts/check-pin.sh near-approval           # submodule = pinned_commit, file hashes match
```

Needs Rust (`RUST_TOOLCHAIN` in `tools/versions.env`), Python 3.11+, and Java
17+ for TLA+.

### Kani: the real core, bounded ([strategy §6](projects/near-approval/strategy.md))

The harnesses in `projects/near-approval/kani` run the real `approval-core`.
The same harness bodies run in two modes.

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

Harnesses are memory-bound: run them one at a time on a 16 GB machine. The
full matrix takes about 2 hours on one Mac. Results and run times are in
[`kani/RESULTS.md`](projects/near-approval/kani/RESULTS.md).

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

`replay` (REF-5L) needs the submodule and Rust; `graph` (MC-4) needs Java.

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

## ironclaw: running the checks

The Verus layer proves models of ironclaw's sanitizer, not the source itself.
The proofs are a scaffold: `assume(false)` still stands in for proof steps,
so a passing run proves nothing yet.

### Plain Rust (no Verus)

```bash
cargo build   # the model crate as plain Rust types, no proofs
cargo test    # 8 unit tests for the sanitizer model
```

### Verus

Install a Verus release (zip with `verus` and Z3) from
[verus-lang/verus releases](https://github.com/verus-lang/verus/releases) and
put it on `PATH`; no version is pinned yet (`VERUS=` in `tools/versions.env`).
To build from source instead: clone the repo, then in `verus/source` run
`./tools/get-z3.sh`, `source ../tools/activate` and `vargo build --release`.

```bash
verus projects/ironclaw/verus/src/lib.rs --crate-type=lib --cfg 'feature="verus"'
```

The `--cfg` matters: the spec and proof modules are behind
`cfg(feature = "verus")`, and without it Verus checks only the plain types.
`./tools/scripts/run-verus.sh ironclaw` still omits it (F-10b in the
near-approval strategy).

To make progress, replace `assume(false)` one proof at a time, rerun `verus`
after each, and update `projects/ironclaw/status.toml`.

### Prolog

```bash
cargo install --locked scryer-prolog --version 0.10.0
./tools/scripts/run-prolog.sh ironclaw                     # all test files
./tools/scripts/run-prolog.sh ironclaw test_sanitizer.pl   # one file
```
