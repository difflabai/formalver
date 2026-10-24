# Verus twin of approval-core (M5 path A)

`src/lib.rs` is the pinned `contracts/approval/core/src/lib.rs` with Verus
annotations added. The twin is a copy of upstream `approval-core` (MIT, copyright Differential AI Lab). The notice is `LICENSE` at the repo root. `tools/scripts/erasure-check.py` strips the annotations and
requires the rest to equal the upstream file token for token, except the
functions in `REWRITES.toml`.

| File | What it holds |
|---|---|
| `src/lib.rs` | The twin: upstream code + `requires`/`ensures`, the `Store` trait's contract, `MemStore` proofs |
| `src/abs.rs` | `AbsStore` (the store as maths), the spec machine (`*_spec`), `inv`, association-list lemmas |
| `src/inv.rs` | `inv` (what the code's own preconditions need) preserved by every operation; the `Op` enum and `op_spec` |
| `src/props.rs` | `full_inv` (INV-0..16, LEM-2) on the empty store and preserved by every operation (`lemma_full_inv`); LEM-1/3/4 |
| `src/hist.rs` | Step properties `hist` (HIST-1..10); INV-10 and TR-4 under ASM-TIME; TR-6 per key |
| `src/runs.rs` | Runs of any length: TR-1 (provenance from init), TR-2, TR-3, TR-7 |
| `src/reads.rs` | RD-1, RD-2/5 (exact pages), RD-4 (client loop), RD-7, RD-8 |
| `src/trusted.rs` | Everything taken on trust; listed in `TRUSTED.toml` |
| `src/witness.rs` | A concrete trace on the real core to approved, rejected and void (revoked, re-added, approve fails) |
| `canary/false_lemma.rs` | Must fail |
| `mutants.toml` | Spec, code and paired (spec and code together) mutants; each must be rejected |

Every property is proved over the spec machine at every store size, and the
core functions' `ensures refines(..)` carry it to the real code on any
`Store` meeting the trait contract (ASM-STORE). Property IDs are tagged
`PROP:` next to the predicate or lemma that proves them; `status.toml` lists
each one's lemmas under `harness`.

Run: `PATH=$(tools/scripts/get-verus.sh):$PATH tools/scripts/run-verus.sh near-approval`.
