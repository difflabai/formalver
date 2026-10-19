# Verus twin of approval-core (M5 path A)

`src/lib.rs` is the pinned `contracts/approval/core/src/lib.rs` with Verus
annotations added. `tools/scripts/erasure-check.py` strips the annotations and
requires the rest to equal the upstream file token for token, except the
functions in `REWRITES.toml`.

| File | What it holds |
|---|---|
| `src/lib.rs` | The twin: upstream code + `requires`/`ensures`, the `Store` trait's contract, `MemStore` proofs |
| `src/abs.rs` | `AbsStore` (the store as maths), the spec machine (`*_spec`), `inv`, association-list lemmas |
| `src/inv.rs` | `inv`, INV-5 and INV-13 preserved by every operation, at every store size |
| `src/trusted.rs` | Everything taken on trust; listed in `TRUSTED.toml` |
| `src/witness.rs` | A concrete trace to an approved request (preconditions satisfiable) |
| `canary/false_lemma.rs` | Must fail |
| `mutants.toml` | Spec and code mutants; each must be rejected |

Run: `PATH=$(tools/scripts/get-verus.sh):$PATH tools/scripts/run-verus.sh near-approval`.
