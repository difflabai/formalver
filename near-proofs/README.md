# near-proofs

Submissions from formalver to [NEAR Proof Arena](https://github.com/ilblackdragon/near-proof-arena),
a judged arena for NEAR state-transition proof systems with a pinned Lean
semantics of nearcore. Nothing is submitted yet.

## Why this lives in formalver

The near-approval proofs (`projects/near-approval`) rest on assumptions about
NEAR itself: who `signer_account_pk` and `predecessor_account_id` are, what a
function-call key can do, per-receipt atomicity, finality. Today they are
cited to the Nomicon (`source` in `projects/near-approval/status.toml`) and are
to be checked by runtime tests, not by proof. The arena is the closest thing to
a machine-checked NEAR model, but its v1 scope excludes exactly those areas.
Each assumption's `arena_excludes` lists the exclusions that would have to be
lifted. Work here is meant to close that gap from the arena side. That can be a
candidate for an existing challenge, or a proof about a slice that an assumption
needs.

## Pin

| | |
|---|---|
| Arena commit read | `cb16c4090a82a6179d8e1a23d6e83e74e9d5d017` (2026-10-09) |
| Submission contract | `arena-candidate-v1` (`docs/AGENT_CONTRACT.md` there) |
| Published challenge | `near-transfer-receipt-v1` (nearcore 2.13.4, PV86): Transfer receipts only |
| Drafts of interest | `near-chunk-v3` (unsigned; function calls and WASM, lane `v3-d3`) |

`tools/upstream-watch.toml` tracks the arena's `spec/`, `challenges/` and
contract docs. The weekly `upstream-watch` workflow opens an issue when they
change.

## Layout

One directory per candidate, in the arena's package layout (contract v1, §1):

```
near-proofs/
  candidates/
    <name>/              # [a-z0-9-]{1,48}, also the manifest `name`
      candidate.toml     # manifest, schema "arena-candidate-v1"; unknown fields are rejected
      source/            # all source the build may use, vendored (cargo vendor)
      dependency-locks/  # Cargo.lock copies and vendored-dir digests
      formal/            # Lean 4 project with the certificate
      build-recipe/      # build.sh: offline, --locked, bit-reproducible
      README.md          # proof system, obligations, limits
```

Start a candidate with the arena CLI so the layout matches the pinned contract:

```bash
arena init-candidate near-proofs/candidates/<name> --challenge <chl_…>
arena check-local near-proofs/candidates/<name>    # before any submission
```

Rules the judge enforces, which also apply here:

- No `sorry`, `admit`, `native_decide` or new axioms.
- Two clean builds must produce bit-identical outputs.
- Every claim is restricted to the challenge's `semantic_scope` minus its
  `excludes`.

Candidates stay out of the root Cargo workspace (`exclude` in `Cargo.toml`).
