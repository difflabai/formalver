# formalver
Formal Verification of repositories, starting with IronClaw

## Projects

| Project | Target | Plan | Status |
|---|---|---|---|
| ironclaw | [nearai/ironclaw](https://github.com/nearai/ironclaw) safety modules | [strategy](projects/ironclaw/strategy.md) | [status](projects/ironclaw/status.toml) |
| near-approval | [trust-framework](https://github.com/difflabai/trust-framework) `contracts/approval` (NEAR action-approval contract) | [strategy](projects/near-approval/strategy.md) | [status](projects/near-approval/status.toml) (core: Kani, TLA+, Lean, Prolog done; shell, sandbox, deployment next) |

Submissions to [NEAR Proof Arena](https://github.com/ilblackdragon/near-proof-arena), aimed at the NEAR assumptions these projects rely on, go in [`near-proofs/`](near-proofs/README.md).

## Running the Scaffolded Proofs

### Verus (Rust code verification)

**1. Install Verus:**

```bash
git clone https://github.com/verus-lang/verus.git
cd verus
./tools/get-z3.sh    # downloads the Z3 SMT solver
source ./tools/activate
vargo build --release
```

**2. Run verification:**

```bash
# From the workspace root
./tools/scripts/run-verus.sh ironclaw

# Or directly:
verus projects/ironclaw/verus/src/lib.rs --crate-type=lib
```

**What to expect:** Proof functions with `assume(false)` will trivially verify (the assumption makes all postconditions vacuously true). Replace `assume(false)` one at a time with actual proof steps, running `verus` after each change. Update `projects/ironclaw/status.toml` as proofs are completed.

**Standard cargo (no Verus required):**

```bash
cargo build   # compiles plain Rust types, no proofs
cargo test    # runs 8 unit tests for the sanitizer model
```

### Kani (near-approval)

The harnesses in `projects/near-approval/kani` run the real `approval-core`
from the pinned submodule. The same harness bodies run in two modes.

```bash
git submodule update --init projects/near-approval/source-mirror   # private: needs trust-framework access

# Plain mode: random tests, no Kani needed (not a proof)
(cd projects/near-approval/kani && cargo test --release)

# Kani: install the pinned version (tools/versions.env), then run every harness
cargo install --locked kani-verifier --version 0.68.0 && cargo kani setup
./tools/scripts/run-kani.sh near-approval            # or name harnesses: ... h_step_approve

# Core mutants: each must be killed (two equivalent ones must survive)
./tools/scripts/run-mutants.sh near-approval         # plain mode
./tools/scripts/run-mutants.sh near-approval --kani  # plus each mutant's Kani harness
```

Harnesses are memory-bound: run them one at a time on a 16 GB machine.
Results and run times are in [`kani/RESULTS.md`](projects/near-approval/kani/RESULTS.md).

### TLA+ (near-approval)

`projects/near-approval/tla` models the core in TLA+; Kani's `h_ref_*`
harnesses prove the real core refines it ([strategy §17](projects/near-approval/strategy.md)).

```bash
./tools/scripts/run-tla.sh near-approval             # fetches pinned TLC/Apalache (Java 17+); or name checks: safety liveness apalache trace mutants
./tools/scripts/run-mc3.sh near-approval             # MC-3: Prolog graph = TLC graph (slow, nightly in CI)
```

### Lean (near-approval)

`projects/near-approval/lean` transcribes the TLA+ model to Lean 4 and proves
its invariant, step properties and run properties for states of every size
([strategy §18](projects/near-approval/strategy.md)). Core library only, no
Mathlib.

```bash
export PATH="$(./tools/scripts/get-lean.sh):$PATH"   # pinned Lean release, sha256-checked
./tools/scripts/run-lean.sh near-approval            # proofs, audit, canaries, guards, REF-5L, MC-4, mutants
./tools/scripts/run-lean.sh near-approval build audit   # or name checks
```

`replay` (REF-5L) needs the submodule and Rust; `graph` (MC-4) needs Java for TLC.

### Prolog (requirements verification)

```bash
# Install scryer-prolog
cargo install --locked scryer-prolog --version 0.10.0

# Run all tests
./tools/scripts/run-prolog.sh ironclaw

# Run a specific test file
./tools/scripts/run-prolog.sh ironclaw test_sanitizer.pl
```

For near-approval (Scryer 0.10.0, pinned in `tools/versions.env`):
`./tools/scripts/run-prolog.sh near-approval` runs the requirement checks and MC-1;
MC-2 trace replay is a separate step in the `prolog` CI job ([strategy §8](projects/near-approval/strategy.md)).

