# formalver
Formal Verification of repositories, starting with IronClaw

## Projects

| Project | Target | Plan | Status |
|---|---|---|---|
| ironclaw | [nearai/ironclaw](https://github.com/nearai/ironclaw) safety modules | [strategy](projects/ironclaw/strategy.md) | [status](projects/ironclaw/status.toml) |
| near-approval | [trust-framework](https://github.com/difflabai/trust-framework) `contracts/approval` (NEAR action-approval contract) | [strategy](projects/near-approval/strategy.md) | [status](projects/near-approval/status.toml) (plan only) |

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

### Prolog (requirements verification)

```bash
# Install scryer-prolog
cargo install scryer-prolog

# Run all tests
./tools/scripts/run-prolog.sh ironclaw

# Run a specific test file
./tools/scripts/run-prolog.sh ironclaw test_sanitizer.pl
```
