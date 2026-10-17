# strategy

Behavior analysis of an application or system, producing a **verification strategy**: what to verify, at which layer, with which tool, in what order, and what to trust.

Input: a codebase (a repo or a subfolder of one) to start. Later: wider systems (services, protocols, deployments).
Output: a machine-readable strategy plus a human-readable plan that the other `formalver` projects (Prolog requirements, Verus proofs) consume.

## Problem

Formal verification is expensive, and the scoping decisions are made by hand: which modules matter, which properties are worth proving, which technique fits, which dependencies to trust, in what order. `projects/ironclaw/strategy.md` is a few pages; `projects/near-approval/strategy.md` is 1,200+ lines (property catalogue, tiers, M0–M7, a trust-assumption table, a correspondence chain). Both are expert judgment, written once, and they go stale when upstream moves. This project makes that decision explicit, repeatable, and checkable.

The workspace already holds the decision space this project must reason over (see [`docs/architecture.md`](../docs/architecture.md)): Prolog requirements and reference semantics, Kani on unmodified Rust, TLA+ (TLC, Apalache) over every call sequence, Lean at every size, Verus, and sandbox tests on the built artifact. The question is which of them a given piece of code needs, and in what order.

## Goals

1. **Characterize behavior at a high level.** Extract the structure and behavioral properties of a target without verifying it:
   - module/component boundaries and dependency graph
   - trust boundaries and external dependencies (candidates for `external_body` / axioms)
   - I/O, side effects, concurrency, `unsafe`, FFI, and failure modes
   - **Determinism analysis** of code sections: pure / deterministic, nondeterministic (time, randomness, IO, scheduling, hash-iteration order, network), and what source of nondeterminism each section depends on
   - other verification-relevant characteristics: termination (loops, recursion), state machines, data-flow of untrusted input, error propagation, resource bounds
   - **core/shell separation**: is there a dependency-free, deterministic core holding the decisions, behind a thin layer that touches the environment? (near-approval's `approval-core` vs. its near-sdk shell is the model case; it is what lets Kani run on the deployed code unmodified.)
   - **bound sufficiency**: collection capacities, loop bounds and state-space size, i.e. whether a bounded check can be argued to cover every size, or an unbounded layer (Lean, Verus) is needed
   - **TCB from the lockfile**: external crates and runtime behavior the code relies on, each a candidate trusted boundary or named assumption
2. **Model in Prolog.** Encode the extracted characteristics as facts, and the verification-selection logic as rules, so that strategy is derived by queries rather than ad-hoc judgment. Examples: "which sections are deterministic, pure, and security-relevant" → candidates for Verus; "which sections are nondeterministic" → model-check, property-test, or constrain the environment first.
3. **Derive a strategy.** For each section/component, recommend:
   - properties worth verifying (and why: criticality, blast radius, tractability)
   - technique/tool fit over the layers the workspace has: Prolog requirements/oracle, Kani, TLA+, Lean, Verus, sandbox/runtime tests, mutation testing, or leave unverified
   - dependency order (verify leaves first, then what builds on them)
   - assumptions and trusted boundaries to declare (the `ASM-*` convention in `status.toml`)
   - the strongest evidence each layer can honestly claim, in the workspace's own vocabulary: `proof | model-proof | bounded-proof | model-check | test | review | check`. A Kani result is at most `bounded-proof`; a Lean result on a model is never a proof of the code. The strategy must not promise more than the tool can deliver.
   - cross-layer links that make a result in one layer mean something in the next (refinement, same-graph and trace-replay checks), and the vacuity guards each layer needs (covers, canaries, mutants)
   - effort/risk estimate
4. **Be checkable and explainable.** Every recommendation traces back to facts and rules that produced it. The strategy itself can be queried, diffed, and re-run as code changes.
5. **Feed the rest of formalver.** Emit output that seeds `projects/<name>/strategy.md`, `status.toml` (property IDs, `evidence`, `layer`, `depends_on`, assumptions), the Prolog requirement skeleton, and the per-layer file layout (Kani crate, TLA+/Lean models, Verus twin).
6. **Stay current.** A strategy is derived from a pinned revision. It records the commit and per-file hashes it was derived from, and it is invalidated, not silently reused, when the pin moves (same mechanism as `check-pin.sh` and `depends_on`).

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

1. **Extract** — language front-ends produce facts, following the precedent of near-approval's generated `prolog/extracted/{code,tla,api}_facts.pl` (checked in; regeneration must show no diff; `api_facts.pl` comes from the built wasm via `tools/scripts/wasm-surface.sh`, added at M3): `module/1`, `calls/2`, `uses_dep/2`, `has_effect/2`, `unsafe_block/1`, `nondeterministic/2`, `loop/2`, `recursion/1`, `handles_untrusted/1`, etc. Rust first (matches the workspace); front-ends are pluggable.
2. **Model** — Prolog (scryer-prolog, as elsewhere in the workspace) holds the facts and the rules for propagation (e.g. nondeterminism and effects propagate up the call graph) and classification.
3. **Strategize** — queries produce a ranked, justified plan per section: tiers and milestones with acceptance criteria and effort, in the shape `near-approval/strategy.md` uses.
4. **Report** — emit markdown + TOML for human review and downstream tools.

## How nondeterminism maps to technique

near-approval shows the pattern; the analysis should derive it rather than assume it.

| Source | Treatment |
|---|---|
| Input values (arguments, caller, time as a parameter) | Symbolic in Kani; any-`u64` arithmetic covered |
| Order of calls by many parties (interleavings) | TLA+ over every sequence; Lean for every size |
| Environment (runtime, SDK, signer identity, limits, I/O) | Pushed into a thin shell; stated as `ASM-*` assumptions; tested in a sandbox on the real artifact |
| Hash-iteration order, scheduling, randomness inside the core | A finding: remove it, or the core is not a Kani/Verus target as-is |
| External libraries (regex, Aho-Corasick, SDK) | Trusted boundary, modeled as a predicate or axiom, listed |

A section classified deterministic and pure is a candidate for verification on the real code. Anything else is routed per the table, and the routing is part of the strategy.

## Planned layout

```
strategy/
  README.md        this file
  extract/         language front-ends that emit Prolog facts
  prolog/          rules: propagation, classification, tool-fit, ordering
  tests/           fixtures with expected strategies
  reports/         generated strategies per target
```

Integration notes (from the current `main`):
- `tools/scripts/run-prolog.sh <project>` looks in `projects/<project>/prolog`, so it won't find `strategy/prolog`. Either generalize the script or give this project its own runner; `scryer-prolog` is pinned in `tools/versions.env` (`SCRYER`).
- `.github/workflows/near-approval.yml` triggers on `projects/near-approval/**` and `tools/**`, so `strategy/` changes don't run those jobs, but a change to `tools/scripts/*` does. This project gets its own workflow and a path-aware area script like `ci-areas.sh`.
- Any Rust crate here must be added to the root `Cargo.toml` `members`, or to `exclude` if it has in-tree path dependencies (as near-approval's does).

## First milestone

Calibrate against the two hand-made strategies. The derived strategy is the test; where it disagrees with the hand-made one, that is a finding about one or the other.

Code extraction alone cannot establish criticality, threats, or runtime assumptions, and the hand-made strategies depend on all three. So the calibration fixture has two parts, versioned together:
- the source: repo, pinned commit, file hashes;
- the human-supplied inputs: a criticality/threat file and an environment-assumption file, transcribed from the hand-made strategy (near-approval §3 for example). These are inputs, not outputs, and never a score.

The test is that decisions follow from *facts plus these inputs*: proof targets, technique per section, `ASM-*` boundaries, ordering. A disagreement is attributed to extraction, rules, or inputs by changing one at a time.

1. **near-approval** (`projects/near-approval/source-mirror`, pinned). The richer ground truth, and the one that exercises the full stack. From extracted facts plus those inputs, reproduce:
   - the split: `approval-core` (dependency-free, deterministic) is the proof target; the near-sdk shell and runtime are test targets
   - Kani first on the real core, because it needs no rewrite
   - a bound argument for Kani's state bounds, and an unbounded layer (Lean on the TLA+ model) where the bound matters
   - Verus on the real core as a spike with an explicit fit risk, not a commitment
   - the trusted boundaries (`ASM-*`) and the milestone order M0–M7
2. **ironclaw** (`src/safety/`). Reproduce the Phase 1 scoping: sanitizer first; regex and Aho-Corasick trusted. Expected disagreement: the ironclaw strategy proves a Verus *model*, while the workspace's own rule of thumb (`docs/architecture.md`) is to start with Kani on the real code. The derived strategy should say which fits the sanitizer, and why.

## Open questions

- Fact granularity: function-level vs. basic-block vs. module-level (start function-level).
- How to represent confidence in extracted facts.
- How much of the system-level behavior (interleavings, protocols) to model in Prolog. TLA+ is now in the workspace, so the default is to *route* to it, and keep Prolog for facts, rules and the requirements oracle.
- Whether the strategy's own rules need the vacuity guards the proof layers use (canaries, mutants of the rule base).
- Format of the criticality/threat and environment-assumption inputs. They are user-supplied and versioned with the source pin (see First milestone); open is whether a threat model can seed them mechanically.
