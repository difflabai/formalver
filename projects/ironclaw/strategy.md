# Ironclaw Formal Verification Strategy

## Target
[ironclaw](https://github.com/nearai/ironclaw) — a secure personal AI assistant with defense-in-depth safety architecture.

Pinned commit: `34550add3ee85bab6fe1c670dff46871d1a41e04`

## Approach: Hierarchical Verification

### Layer 1: Requirements (Prolog)
Use scryer-prolog to encode and verify:
- Security requirements as logical facts and rules
- Consistency: no contradictory rules
- Completeness: all known attack vectors have detection patterns
- Redundancy: no unnecessary duplication

### Layer 2: Implementation (Verus)
Use Verus to verify Rust code correctness:
- Create verified models of ironclaw's security-critical code paths
- Prove properties like detection completeness, escape correctness, severity ordering
- Trust boundaries: Aho-Corasick and regex engines are assumed correct (external_body)

### Connection Between Layers
The same 27 string patterns + 4 regex patterns appear in both:
- Prolog facts (for requirement-level reasoning)
- Verus model constants (for code-level verification)

## Scope

### Phase 1: Prompt Injection Detection (sanitizer)
**Source:** `src/safety/sanitizer.rs` (435 lines)

Verified properties:
- Detection completeness: all defined patterns are detected
- Escape correctness: critical patterns are escaped in output
- Case insensitivity: detection is case-insensitive
- Severity ordering: results sorted critical-first
- Content preservation: non-matching content is unchanged

Trusted boundaries:
- `aho_corasick::AhoCorasick` — multi-pattern matching engine
- `regex::Regex` — regex matching engine

### Phase 2 (future): Secret Leak Detection
**Source:** `src/safety/leak_detector.rs` (838 lines)

### Phase 3 (future): Policy Engine
**Source:** `src/safety/policy.rs` (256 lines)

### Phase 4 (future): Input Validation
**Source:** `src/safety/validator.rs` (472 lines)

### Phase 5 (future): Credential Detection
**Source:** `src/safety/credential_detect.rs` (382 lines)

## Model Fidelity

Each Verus model file records:
- Upstream file path and pinned commit
- Which functions/structs are modeled
- Simplifications made
- What is marked as trusted (external_body)

When upstream changes, status tracking marks affected modules as `stale`.
