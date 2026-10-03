# strategy

Behavior analysis of an application or system, producing a **verification strategy**: what to verify, at which layer, with which tool, in what order, and what to trust.

Input: a codebase (a repo or a subfolder of one) to start. Later: wider systems (services, protocols, deployments).
Output: a machine-readable strategy plus a human-readable plan that the other `formalver` projects (Prolog requirements, Verus proofs) consume.

## Problem

Formal verification is expensive. Today the scoping decisions for a target (see `projects/ironclaw/strategy.md`) are made by hand: which modules matter, which properties are worth proving, which dependencies to trust. This project makes that decision explicit, repeatable, and checkable.

## Goals

1. **Characterize behavior at a high level.** Extract the structure and behavioral properties of a target without verifying it:
   - module/component boundaries and dependency graph
   - trust boundaries and external dependencies (candidates for `external_body` / axioms)
   - I/O, side effects, concurrency, `unsafe`, FFI, and failure modes
   - **Determinism analysis** of code sections: pure / deterministic, nondeterministic (time, randomness, IO, scheduling, hash-iteration order, network), and what source of nondeterminism each section depends on
   - other verification-relevant characteristics: termination (loops, recursion), state machines, data-flow of untrusted input, error propagation, resource bounds
2. **Model in Prolog.** Encode the extracted characteristics as facts, and the verification-selection logic as rules, so that strategy is derived by queries rather than ad-hoc judgment. Examples: "which sections are deterministic, pure, and security-relevant" → candidates for Verus; "which sections are nondeterministic" → model-check, property-test, or constrain the environment first.
3. **Derive a strategy.** For each section/component, recommend:
   - properties worth verifying (and why: criticality, blast radius, tractability)
   - technique/tool fit (Verus, Prolog requirements model, model checking, property/fuzz testing, leave unverified)
   - dependency order (verify leaves first, then what builds on them)
   - assumptions and trusted boundaries to declare
   - effort/risk estimate
4. **Be checkable and explainable.** Every recommendation traces back to facts and rules that produced it. The strategy itself can be queried, diffed, and re-run as code changes.
5. **Feed the rest of formalver.** Emit output that seeds `projects/<name>/strategy.md`, `status.toml`, the Prolog requirement skeleton, and the Verus model/spec/proof file layout.

## Non-goals

- Proving anything. This project decides *what* to prove and *how*; `projects/*` do the proving.
- Full static analysis soundness. Extraction is allowed to be approximate as long as imprecision is explicit (facts carry a confidence/provenance tag) and errs toward flagging, not hiding.
- Replacing human judgment on criticality. Humans supply or override priorities; the model reasons over them.

## Approach (sketch)

```
target code ──► extract ──► facts (Prolog) ──► rules/queries ──► strategy
                  │                                  ▲
        syntax/semantic analysis             criticality + tool-fit
        (tree-sitter / rust-analyzer /       knowledge base
         cargo metadata, later others)
```

1. **Extract** — language front-ends produce facts: `module/1`, `calls/2`, `uses_dep/2`, `has_effect/2`, `unsafe_block/1`, `nondeterministic/2`, `loop/2`, `recursion/1`, `handles_untrusted/1`, etc. Rust first (matches the workspace); front-ends are pluggable.
2. **Model** — Prolog (scryer-prolog, as elsewhere in the workspace) holds the facts and the rules for propagation (e.g. nondeterminism and effects propagate up the call graph) and classification.
3. **Strategize** — queries produce a ranked, justified plan per section.
4. **Report** — emit markdown + TOML for human review and downstream tools.

## Planned layout

```
strategy/
  README.md        this file
  extract/         language front-ends that emit Prolog facts
  prolog/          rules: propagation, classification, tool-fit, ordering
  tests/           fixtures with expected strategies
  reports/         generated strategies per target
```

## First milestone

Run against `projects/ironclaw/source-mirror` (starting with `src/safety/`) and reproduce, from derived facts, the scoping decisions already made by hand in `projects/ironclaw/strategy.md`: sanitizer is the Phase 1 target, regex/Aho-Corasick are trusted boundaries. Where the derived strategy disagrees with the hand-made one, that's a finding about one or the other.

## Open questions

- Fact granularity: function-level vs. basic-block vs. module-level (start function-level).
- How to represent confidence in extracted facts.
- Whether to model system-level behavior (concurrency, distributed protocols) in Prolog or defer to a TLA+/model-checking layer.
- Where the criticality knowledge base comes from (user-supplied, derived from threat model, or both).
