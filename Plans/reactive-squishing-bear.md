# Formal Verification Workspace for Software Projects

## Context

We need a structured approach to formally verify software projects. The first target is [ironclaw](https://github.com/nearai/ironclaw), a secure AI assistant with a defense-in-depth safety module. We start by verifying the prompt injection detection in `src/safety/sanitizer.rs`.

The verification strategy is **hierarchical**:
- **Prolog** (scryer-prolog): verify logical consistency and completeness of security requirements
- **Verus**: verify Rust implementation correctness against those requirements
- Verification is incremental — parts verified, parts not, with status tracking

Since ironclaw is external code and Verus requires its own toolchain, we create **verified models** (faithful mirrors of critical code paths with Verus annotations) rather than annotating ironclaw directly.

---

## Directory Structure

```
albuquerque/
├── Cargo.toml                         # Rust workspace
├── docs/
│   └── architecture.md                # How verification layers interact
├── tools/
│   └── scripts/
│       ├── run-verus.sh               # Invoke Verus toolchain
│       └── run-prolog.sh              # Invoke scryer-prolog
├── projects/
│   └── ironclaw/
│       ├── strategy.md                # What we verify, why, how
│       ├── status.toml                # Machine-readable verification status
│       ├── source-mirror/             # Git submodule of ironclaw at pinned commit
│       ├── verus/                     # Verus verification crate
│       │   ├── Cargo.toml
│       │   └── src/
│       │       ├── lib.rs
│       │       ├── common/
│       │       │   ├── mod.rs
│       │       │   └── string_props.rs    # Substring containment, case-insensitive specs
│       │       └── safety/
│       │           ├── mod.rs
│       │           ├── sanitizer.rs       # Model of sanitizer types + pipeline
│       │           ├── sanitizer_spec.rs  # Specs: detection completeness, escape correctness
│       │           └── sanitizer_proof.rs # Proofs that model satisfies specs
│       └── prolog/
│           ├── requirements/
│           │   ├── security.pl            # Threat taxonomy, severity ordering, invariants
│           │   └── sanitizer_req.pl       # All 27+4 patterns as facts with category/severity
│           ├── verification/
│           │   └── consistency.pl         # Consistency, completeness, conflict queries
│           └── tests/
│               └── test_sanitizer.pl      # Runnable Prolog test suite
```

---

## Implementation Steps

### Step 1: Workspace Foundation
- Add ironclaw as git submodule in `projects/ironclaw/source-mirror/`
- Create workspace `Cargo.toml` with `projects/ironclaw/verus` as member
- Create `projects/ironclaw/strategy.md` documenting the hierarchical approach
- Create `projects/ironclaw/status.toml` with all modules listed, initially unverified

### Step 2: Prolog Requirements Layer
Create Prolog files encoding ironclaw's security requirements:

**`prolog/requirements/security.pl`** — threat categories, severity ordering, security invariants

**`prolog/requirements/sanitizer_req.pl`** — all 27 string patterns and 4 regex patterns from ironclaw's sanitizer as Prolog facts:
```prolog
injection_pattern("ignore previous", high, instruction_override).
injection_pattern("system:", critical, role_marker).
% ... all patterns from ironclaw/src/safety/sanitizer.rs
```

**`prolog/verification/consistency.pl`** — queries to check:
- Every pattern has a valid severity
- No conflicting actions for same category
- All known attack vectors have corresponding patterns
- No redundant patterns

**`prolog/tests/test_sanitizer.pl`** — executable tests that run the consistency queries

### Step 3: Verus Model of Sanitizer
Create verified models mirroring ironclaw's sanitizer code.

**Three-file pattern per module:**

| File | Contains |
|------|----------|
| `sanitizer.rs` | Model of `Sanitizer`, `SanitizedOutput`, `InjectionWarning`, `Severity` types and the detect/sort/escape pipeline |
| `sanitizer_spec.rs` | Spec functions stating properties: detection completeness, escape correctness, case insensitivity, severity ordering, benign content preservation |
| `sanitizer_proof.rs` | Proofs that the model satisfies the specs |

**Trusted boundaries** (not verified, assumed correct):
- Aho-Corasick pattern matching — modeled as abstract spec: "returns all matches of patterns in input"
- Regex engine — similarly abstracted

**Verified properties:**
- If input contains a critical pattern, output has that pattern escaped
- Severity sorting is correct (critical before high before medium before low)
- Non-matching content is preserved unchanged
- Case insensitivity of detection

**`common/string_props.rs`** — reusable spec functions for substring containment, case-insensitive comparison used across proofs.

Each model file has a header recording: upstream file path, pinned commit, which functions are modeled, and any simplifications.

### Step 4: Helper Scripts
- `tools/scripts/run-verus.sh` — wraps Verus binary invocation for the workspace
- `tools/scripts/run-prolog.sh` — wraps scryer-prolog invocation for running tests

### Step 5: Documentation
- `docs/architecture.md` — how the Prolog and Verus layers connect, the verified modeling approach, trusted boundaries

---

## Verification Status Tracking

`status.toml` tracks per-module, per-property verification state:

```toml
[project]
name = "ironclaw"
upstream = "https://github.com/nearai/ironclaw"
pinned_commit = "<sha>"

[modules.safety_sanitizer]
source = "src/safety/sanitizer.rs"
  [modules.safety_sanitizer.properties]
  detection_completeness = { status = "unverified", layer = "verus" }
  escape_correctness = { status = "unverified", layer = "verus" }
  requirement_consistency = { status = "unverified", layer = "prolog" }
```

Status values: `unverified` | `in-progress` | `verified` | `verified-with-assumptions` | `stale`

---

## Key Design Decisions

1. **Verified models, not direct annotation** — ironclaw is external; we mirror critical paths. Risk of model drift mitigated by pinned submodule + stale detection.
2. **Prolog for requirements, Verus for code** — Prolog checks requirement consistency (meta-level), Verus checks code correctness (implementation-level). Connected through shared pattern definitions.
3. **Aho-Corasick/regex as trusted boundary** — verifying string matching libraries is out of scope; we assume they work and verify the logic that uses their results.
4. **Incremental** — status.toml tracks what's done. Other safety modules (leak_detector, policy, validator) are listed but unverified until work begins.

---

## Verification

- **Prolog**: Run `scryer-prolog projects/ironclaw/prolog/tests/test_sanitizer.pl` — should report all consistency checks passing
- **Verus**: Run `verus projects/ironclaw/verus/src/lib.rs` — should verify all proof functions
- **Status**: Check `projects/ironclaw/status.toml` reflects current state

---

## Files to Create/Modify

| File | Action |
|------|--------|
| `Cargo.toml` | Create (workspace) |
| `docs/architecture.md` | Create |
| `projects/ironclaw/strategy.md` | Create |
| `projects/ironclaw/status.toml` | Create |
| `projects/ironclaw/verus/Cargo.toml` | Create |
| `projects/ironclaw/verus/src/lib.rs` | Create |
| `projects/ironclaw/verus/src/common/mod.rs` | Create |
| `projects/ironclaw/verus/src/common/string_props.rs` | Create |
| `projects/ironclaw/verus/src/safety/mod.rs` | Create |
| `projects/ironclaw/verus/src/safety/sanitizer.rs` | Create |
| `projects/ironclaw/verus/src/safety/sanitizer_spec.rs` | Create |
| `projects/ironclaw/verus/src/safety/sanitizer_proof.rs` | Create |
| `projects/ironclaw/prolog/requirements/security.pl` | Create |
| `projects/ironclaw/prolog/requirements/sanitizer_req.pl` | Create |
| `projects/ironclaw/prolog/verification/consistency.pl` | Create |
| `projects/ironclaw/prolog/tests/test_sanitizer.pl` | Create |
| `tools/scripts/run-verus.sh` | Create |
| `tools/scripts/run-prolog.sh` | Create |
