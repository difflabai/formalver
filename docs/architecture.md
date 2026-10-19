# Formal Verification Architecture

## Overview

Every technique in this workspace answers a different question. No single tool
answers all of them, so each project stacks several and links them so that a
result in one layer means something in the next.

| Question | Technique | Tool |
|---|---|---|
| Are the requirements consistent and complete? | Requirements as logic facts and checks | Prolog (Scryer) |
| Does the *deployed code* do the right thing on one call, within a bound? | Bounded model checking of the real Rust | Kani (CBMC) |
| Does the design stay safe over *every sequence* of calls, and make progress? | Model checking a state machine | TLA+ (TLC, Apalache) |
| Does the design stay safe at *every size*? | Interactive theorem proving on the model | Lean 4 |
| Does the deployed code do the right thing at every size? | Deductive verification of Rust | Verus (SMT) |
| Does the code behave the same on the real runtime? | Tests on the built artifact | near-workspaces sandbox |

Two projects use different subsets:
- **ironclaw** uses Prolog and Verus, with Verus proving *models* of the code
  (see [ironclaw](#ironclaw-two-layers)).
- **near-approval** uses Prolog, Kani, TLA+ and Lean today, and plans Verus on
  the real code as an optional upgrade.

## near-approval: how the layers fit

The contract splits into a dependency-free core (`approval-core`, every
authorization and state transition) and a thin near-sdk shell. All of the
proof layers target the core; the shell, the wasm and the runtime are covered
by tests and checks (M3, M6, M7).

```text
            requirements (R1-R6, D1-D16)
                     │ written from
                     ▼
            Prolog step/4 ─────── MC-3: same reachable graph ───────┐
                     │                                                │
          MC-2: same results on traces                                ▼
                     │                                   TLA+ ApprovalCore.tla
                     ▼                                 TLC: every sequence (small)
      ┌───── real approval-core (Rust) ◄── REF-1..5 ──── Apalache: Inv inductive
      │       Kani: one step, any Inv state         │                 │
      │       within bounds; CUTOFF.md says         │     MC-4 + REF-5L: same graph,
      │       the bounds suffice                    │     same traces │
      │                                             │                 ▼
      │                                             └──────── Lean machine
      │                                                     Inv, step and run
      ▼                                                     properties, every size
  near-sdk shell ─► wasm ─► deployed contract
  (M3 near-tests) (M6 sandbox)  (M7 deploy checks)
```

### What each layer contributes

| Layer | Proves | Bound | Tied to its neighbours by |
|---|---|---|---|
| **Prolog** `step/4` | An independent semantics written from the requirements, not the code. Requirement checks C-1..C-10 (authority matrix, guard order, messages, constants, traceability). | MC-1 explores depth 6 | MC-2 replays the same traces on Prolog and the real core. MC-3 shows Prolog's and TLC's reachable graphs are equal (21,670 stores, 41,706 edges). C-2t: Prolog's guard order equals TLA+'s and the code's. |
| **Kani** on `approval-core` | For one call from any state satisfying `Inv`: the exact result, the exact post-state, the invariant, the history properties. Also panics, overflow and paging over any `u64`. | ≤ 3 principals, requests, log entries and revocations per state; loops unwound to bounds derived from those capacities (U-1) | `h_ref_*` (REF-1..4) prove the core refines the TLA+ model: same errors, same effects, rejected calls stutter. CUT-1 + `CUTOFF.md` argue the state bounds suffice for every size. |
| **TLA+** | Every interleaving of every call by every party: `Inv`, step properties, liveness (`Live1` under approver fairness). Apalache shows `Inv` is inductive. | TLC: ≤ 3 requests, 2 keys, 3 accounts. Apalache: arrays ≤ 3 before the step | REF-5 replays real-core traces through TLC. MC-3 and MC-4 against Prolog and Lean. |
| **Lean** | The TLA+ model's `Inv`, step properties, TR-1/2/3 and liveness (`Live1`, plus a strong-fairness variant) for **every** state size, key type and `MaxPending`. Kernel-checked, three standard axioms only. | none | MC-4: Lean's graph equals TLC's. REF-5L: 2,000 real-core traces replay step for step. Guard order equals `tla_facts.pl`. |
| **Shell** (M3, `near-tests/`) | The real contract over near-sdk's mocked runtime refines `MemStore`: 10k × 50 random calls with a Borsh reload every step, equal results, panics, events, views and storage keys (ST-4, SH-2..7). Golden layout bytes (ST-6), storage and log-size bounds (RES-1/2). | tests | `wasm-surface.sh` pins the wasm's exports and imports (SH-11/12) and regenerates `api_facts.pl` for C-6. 12 shell mutants must fail the suite. |
| **Sandbox** (M6, `sandbox/`) | The reproducible wasm (sha256 pinned in `status.toml`) on near-sandbox: signer identity, relays, own-account code, delegate actions, function-call key scope, atomicity of failed receipts, batches, account reset, forged events (RT-*); init, deposits, page size (SH-9/10, RES-3). | tests, recorded outcomes | RT-TRACE replays the checked-in Prolog and core traces on the wasm, step for step against the host core. Observed outcomes are copied into the `[assumptions]` they test. |
| **Deploy and verify** (M7) | `check_deployment.sh <net>`: code hash, lock-at-deploy, owner, function-call-only registered keys, balance (DEP-1), code hash over time, no full-access keys since deploy (VER-2/3), per-proof key scope (VER-8). `verifier_rules.pl` states VER-1..8. | checks | Demonstrated on the sandbox chain with passing and failing deployments; no public-network deployment yet. |

### Reading the chain

The claim "the deployed core is safe" is assembled from links, and each link
says which kind of evidence it is:

1. **Lean** proves the model safe, and live under approver fairness, at every size (proof).
2. **MC-4, REF-5L** show the Lean machine is the TLA+ model (equality on a
   graph where every guard and error fires, and on real traces; checked, not
   proved).
3. **REF-1..3 (Kani)** prove the real core refines the TLA+ model, one step at
   a time, within the state bounds (bounded proof).
4. **CUT-1 + `CUTOFF.md`** argue the bounds lose nothing (Kani-checked
   footprint plus a paper argument; mechanising it in Lean is the optional
   L2 step).
5. **Prolog** guards against all of the above faithfully implementing the
   wrong thing: it is written from the requirements, and MC-2/MC-3 show it
   agrees with the code and the model.

The remaining gaps are named assumptions in `status.toml` (`ASM-*`):
the small-scope step for the code (`ASM-MODEL`), the Lean transcription
(`ASM-LEAN-TLA`), the specs meaning what we intend (`ASM-SPEC`, which needs a
human reviewer), and the NEAR runtime behaviour the shell relies on (tested on
near-sandbox by M6, with the observed outcomes recorded on each assumption).

`tools/scripts/check-status.sh` (status-lint, in the `pin` job) keeps
`status.toml` honest: every claimed property has its artifact or `PROP` tag,
evidence matches the layer, and no Kani property reaches `verified*` without a
named spec reviewer.

## Kani vs Verus

Both verify Rust, but they are different kinds of tool and they fit different
jobs.

| | Kani | Verus |
|---|---|---|
| Method | Bounded model checking: compiles the Rust to a goto program, unwinds loops, hands CBMC a SAT problem | Deductive verification: you write `requires`/`ensures`, invariants and lemmas; Z3 discharges the obligations |
| Code it checks | **Unmodified** Rust, generics and std included. Harnesses live outside the crate | Code inside `verus!` blocks, in the subset Verus supports. Real code needs a "verified twin" plus an erasure check, or a hand-written model |
| Result | "No violation within these bounds": state sizes and loop unwinding | Holds for **all** inputs and sizes, if the proof goes through |
| Effort | Low per property: write the property as an assertion over symbolic inputs | High: specs, loop invariants and proof steps, and friction with closures, iterators and `String` |
| Failure mode | Too slow at larger bounds; the bound itself must be argued | Proof does not go through, or the code cannot be expressed without rewriting it |
| Best at | Exact per-step contracts, panics, overflow and arithmetic over full `u64`, mutant killing, refinement against a model | Unbounded invariants on code you can annotate |

**How near-approval uses them.** Kani comes first because it checks the code
that is deployed, with no rewrite, and gives the most assurance per day. Its
gap is the bound. Two things close it: `CUTOFF.md` argues the bounds suffice,
and Lean proves the properties at every size, but on the TLA+ model rather
than the code. Verus (M5 path A) is the only route to an unbounded proof
**of the real code**: wrap a copy of the core in `verus!`, prove refinement
`ensures` against an abstract view of the store, and require the stripped twin
to be token-identical to upstream. It would retire `ASM-MODEL` for the core.
It has not started: a 2-day spike decides whether the core fits Verus's
subset. Path B, a Verus model of the machine, is dropped, because Lean
already proves that model and is linked to it mechanically.

**How ironclaw uses Verus.** Ironclaw's Verus layer targets models that mirror
the source, not the source itself, so its results will be model proofs. The
sanitizer proofs are still a scaffold (`sanitizer_proof.rs` says so), and F-10
in the near-approval strategy lists the tooling defects found there. External
libraries (Aho-Corasick, regex) are trusted boundaries.

**Rule of thumb.** Start with Kani on the real code. Then add an unbounded
layer only where the bound matters: Lean or Verus on a model is cheaper,
Verus on the code is stronger.

## ironclaw: two layers

```
┌─────────────────────────────────────────┐
│  Layer 1: Requirements (Prolog)         │
│  "Are the requirements consistent?"     │
├─────────────────────────────────────────┤
│  Layer 2: Implementation model (Verus)  │
│  "Does the modelled code satisfy them?" │
└─────────────────────────────────────────┘
```

- **Prolog:** requirements are facts (for example
  `injection_pattern("system:", critical, role_marker_injection)`). Queries
  find contradictory rules, attack vectors with no detection pattern,
  redundant patterns and invalid severities.
- **Verus:** a three-file pattern per module. `module.rs` models the source's
  types and algorithms, `module_spec.rs` states the properties (detection
  completeness, escape correctness), and `module_proof.rs` proves them.
- **Connection:** the same patterns appear in both layers on purpose. Prolog
  checks that the *set of requirements* makes sense; Verus checks that the
  *code processing those patterns* is correct. The link is shared constants
  and review, not a mechanical check.

## Trusted boundaries

Nothing is verified all the way down. What each project trusts is listed and
tracked:
- **ironclaw:** Aho-Corasick ("returns all case-insensitive matches"), the
  regex engine (named boolean predicates), `String::replace`. Documented in
  each model file.
- **near-approval:** the `[assumptions.ASM-*]` table in `status.toml`
  (strategy §3.3). Each has a confidence level and the check that covers it.
  NEAR-facing assumptions also cite the Nomicon pages they rely on.

## Verification status

Each project has a `status.toml` tracking per-module, per-property state:
- `unverified`: no work done
- `in-progress`: model, specs or proofs being written, or passing but not yet
  signed off
- `verified`: proofs pass, specs reviewed
- `verified-with-assumptions`: proofs pass but rely on trusted boundaries or
  bounds
- `stale`: upstream changed since verification

near-approval also records each property's `evidence`
(`proof | model-proof | bounded-proof | model-check | test | review | check`)
and its `layer`, so a Kani result can never be reported as more than a
bounded proof, and a Lean result never as a proof of the code (strategy §12).
