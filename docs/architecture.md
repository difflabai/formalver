# Formal Verification Architecture

## Overview

This workspace provides formal verification for software projects using a two-layer hierarchical approach:

```
┌─────────────────────────────────────────┐
│  Layer 1: Requirements (Prolog)         │
│  "Are the requirements consistent?"     │
│  Tool: scryer-prolog                    │
├─────────────────────────────────────────┤
│  Layer 2: Implementation (Verus)        │
│  "Does the code satisfy requirements?" │
│  Tool: verus                            │
└─────────────────────────────────────────┘
```

## Layer 1: Prolog Requirements Verification

**Purpose:** Verify that security requirements are internally consistent and complete.

**How it works:**
- Requirements are encoded as Prolog facts (e.g., `injection_pattern("system:", critical, role_marker_injection)`)
- Verification queries check for inconsistencies, gaps, and redundancies
- Tests can be run automatically to validate the requirement model

**What it catches:**
- Contradictory rules (e.g., same pattern with conflicting actions)
- Missing coverage (known attack vectors without detection patterns)
- Redundant patterns (substring relationships)
- Invalid severity classifications

## Layer 2: Verus Code Verification

**Purpose:** Prove that the implementation satisfies the requirements.

**How it works:**
- Verified models mirror the source code's types and algorithms
- Spec functions define formal properties (detection completeness, escape correctness)
- Proof functions demonstrate the properties hold
- External libraries (Aho-Corasick, regex) are trusted boundaries

**Three-file pattern per module:**
- `module.rs` — Model of the source code
- `module_spec.rs` — Formal specifications (properties to verify)
- `module_proof.rs` — Proofs that the model satisfies specs

## Trusted Boundaries

We do not verify everything. External dependencies are treated as trusted:
- **Aho-Corasick** — modeled as "returns all case-insensitive matches of all patterns"
- **Regex engine** — modeled as named boolean predicates per regex
- **Rust's String::replace** — modeled via abstract spec with axiom that target is removed

These assumptions are documented in each model file and tracked in status.toml.

## Verification Status

Each project has a `status.toml` tracking per-module, per-property verification state:
- `unverified` — no work done
- `in-progress` — model/specs/proofs being written
- `verified` — proofs pass, specs reviewed
- `verified-with-assumptions` — proofs pass but rely on trusted boundaries
- `stale` — upstream changed since verification

## Connection Between Layers

The same patterns appear in both layers:
- **Prolog:** `injection_pattern("system:", critical, role_marker_injection).`
- **Verus:** Pattern constant in the model with `Severity::Critical`

This intentional duplication allows each layer to verify different aspects. Prolog checks that the *set of requirements* makes sense. Verus checks that the *code processing those patterns* is correct.

## near-approval: a deeper stack

The two-layer picture above is ironclaw's. near-approval
([strategy](../projects/near-approval/strategy.md)) uses more layers, each
tied to the next by a mechanical check rather than by review:

| Layer | Tool | Role | Linked by |
|---|---|---|---|
| Requirements oracle | Prolog (Scryer) | `step/4` written from the requirements, not the code; C-checks on the requirement tables | MC-2 (traces vs the real core), MC-3 (graph = TLC's) |
| Code-shaped model | TLA+ (TLC, Apalache) | every event sequence, liveness under fairness | REF-1..5: Kani proves the real core refines it |
| Model at every size | Lean 4 | `Inv`, step and run properties without a size bound | MC-4 (graph = TLC's), REF-5L (core traces) |
| Real code, bounded | Kani | one step of the deployed `approval-core` from any `Inv` state within the bounds; CUTOFF.md argues those bounds suffice | — |
| Shell, runtime, deployment | near-sdk tests, near-workspaces sandbox, deploy checks | planned (M3, M6, M7) | — |

Verus (M5 path A) would replace the bounded step for the real code; it has
not started.
