# Why ≤ 3 is enough: the cutoff argument (CUT-2)

Status: paper proof, checked against the code at `3426c92`. CUT-1
(`h_cut_*`, `src/cutoff.rs`) machine-checks the one premise that depends on
the code's shape, the footprint. This replaces the informal "small-scope"
line of strategy §6.3 for the step harnesses.

## The question

The step harnesses check, for each operation `op` and each property `P`:

    ∀ s ∈ Inv ∩ B.  ∀ op.  P(s, op, step(s, op))

where `B` is the harness bound: ≤ 3 principals, requests, log entries and
revocations (`gen::MAX_P/R/V`, `Shape` below 4), keys and accounts from 4
values each (`NK`, `NA`), registration ids below 8, and `G = #P + #V`. We
want the same with `B` dropped. The unwind bound is a separate matter:
Kani's unwinding assertions already prove it sufficient for `B` (any loop
that could run longer fails the run), so only the state bound needs an
argument.

## The theorem

> **Cutoff.** Let `s ∈ Inv` be of any size, and let `step(s, op)` violate a
> step property `P` (TX, POST, HIST, INV, REG or REF part). Then there is
> `s₀ = ρ(s) ∈ Inv ∩ B` and `op₀` such that `step(s₀, op₀)` violates `P`,
> **unless** the violation depends on a counter at its threshold:
> - **E1:** a principal's `pending` at `MAXP − 1` or `MAXP` (request's
>   `TooManyPending`), or
> - **E2:** `G`, `#R` or `#L` at `u64::MAX` (the three `LogFull` guards).

So the step harnesses are complete for every behaviour except E1 and E2,
and those need harnesses whose counters are free. Section "Exceptions"
lists which harnesses cover them and which don't yet.

## The restriction ρ

Pick a **kept set** `W = (K, I, J)`: keys whose principals stay, request
positions that stay, and revocation entries that stay. Then `ρ_W(s)` is:

| Part | Kept | Renamed |
|---|---|---|
| Principals | entries with key in `K`, original order | `active_from' = #{i ∈ I : i < active_from}`; `pending' = Pend` over kept requests (INV-9 by construction) |
| Requests | positions in `I`, original order | `id' = rank in I`; recorded keys and accounts recoloured (below) |
| Log | exactly the slots of kept approved requests, original order | values `id'`; `approval_index' = rank among kept slots` |
| Registration ids | live ids of kept principals, ids of `J`, and one extra revoked id `r*` | order-preserving onto `0..G'`, `G' = #P' + #V'` (INV-15 by construction). Every recorded id in a kept request that is neither live in `P'` nor in `J` maps to `r*`. |
| Keys, accounts | | Values outside the kept principals are recoloured so that every equality the code or a property tests on kept data keeps its truth value. Within one request the agent and approver key (INV-6) and account (INV-5) must differ, so a request needs ≤ 2 fresh colours. |
| Ghost | per kept key and kept request | same renaming |

`ρ_W(s) ∈ Inv` for any `W`: every invariant is either a property of one
entity or pair (INV-0, 1, 2, 5, 6, 8, 10, 11, 12, 13, 14, 16, LEM-1),
which a sub-structure inherits once ids are renamed monotonically, or a
count (INV-7, 9, 15, LEM-2, 3) or order (TR-4) that the renaming
recomputes or that a subsequence inherits.

## Why ρ commutes with a step

Three facts about the core, each checked:

1. **Footprint (CUT-1).** Each operation calls the store a fixed number of
   times, and each call reads or writes at most one entry, found by key or
   position. So it touches at most these pre-state entries:

   | op | principals | requests | log | revocations |
   |---|---|---|---|---|
   | add | 1 (the key, if registered) | 0 | 0 | 0 |
   | revoke | 1 | 0 | 0 | 0 |
   | request | 1 (signer key) | 0 (appends) | 0 | 0 |
   | approve | 2 (signer key, agent key) | 1 | 0 (appends) | 0 |
   | reject | 2 | 1 | 0 | 0 |

   The rest is three counters (`G`, `#R`, `#L`). A lookup that misses is a
   fact about the whole map, so a missed key is kept only as a value
   absent from `K`, and ρ keeps it absent.
2. **Order and equality only.** The core compares ids, keys and accounts
   with `==`, and request ids with `active_from` and the counters with `≤`
   or `<`. Monotone renaming and equality-preserving recolouring keep every
   comparison's result, so with the footprint in `W`, every store call on
   `ρ(s)` returns the renamed answer it returned on `s`.
3. **Counters only meet constants at E1 and E2.** `pending` is tested only
   against `MAXP`, and `G`, `#R`, `#L` only against `u64::MAX`. ρ lowers
   them, so these guards are the only ones whose result can change.

Outside E1/E2, then, `step(ρ(s), op') = ρ'(step(s, op))`, where `op'` is
`op` renamed and `ρ'` is ρ for the same `W` plus the appended entry.

## Which `W` keeps a violation

An untouched entity keeps its pre-state values, and `s ∈ Inv`. So a broken
invariant over ≤ 2 entities involves at least one touched or new entity,
plus at most one **partner**. Counts and the potential `Φ` change only
through touched entities, and ρ preserves their deltas. POST, REF and
atomic failure compare states entry by entry, so one differing entry is the
witness. Hence `W = footprint ∪ one partner ∪ closure`, where the closure
adds the log slot of every kept approved request and `r*`.

Partners by property (pre-state entities added on top of the footprint):

| Property | Partner |
|---|---|
| TX, POST, TX-0 atomic failure, REF | the one entry that differs (≤ 1 of any kind) |
| INV-0, INV-11 (pairs of principals) | 1 principal |
| INV-12 (pairs of revocations) | 1 revocation |
| INV-1 (`id = position`) | the request at position `id`, when the renaming could merge them |
| INV-3, INV-4, LEM-1, TR-4 (log ↔ request, log order) | 1 request and its log slot (TR-4: a kept subsequence keeps an inversion, since inversions in a sequence imply one between neighbours) |
| INV-8, INV-16 (principal ↔ request binding) | 1 request, or 1 principal |
| HIST-1, 2, 5, 8, 9 (per request) | 1 request |
| HIST-3 (per log slot) | 1 log slot and its request |
| HIST-6 (per key), HIST-10 (per revocation) | 1 principal, or 1 revocation |
| INV-2, 5, 6, 10, 13, 14 (one request) | none: the touched request |
| INV-7, INV-9, INV-15, LEM-2, LEM-3, HIST-4, TR-6 (counts) | none: deltas |
| GH (ghost agreement) | 1 key or 1 request |

## Sizes needed

Worst case per operation, maximised over properties (one property's
partner at a time), pre-state:

| op | principals | requests | log | revocations | keys | accounts |
|---|---|---|---|---|---|---|
| add | 1 + 1 = **2** | 1 | 1 | 1 + `r*` = **2** | 2 + 2 = 4 | ≤ 4 |
| revoke | 2 | 1 | 1 | 1 + `r*` = 2 | 4 | ≤ 4 |
| request | 2 | 1 | 1 | 1 + `r*` = 2 | 4 | ≤ 4 |
| approve | 2 + 1 = **3** | 1 + 1 = **2** | 2 | 1 + `r*` = 2 | **4** | ≤ 4 |
| reject | 3 | 2 | 2 | 2 | 4 | ≤ 4 |
| harness bound `B` | 3 | 3 | 3 | 3 | 4 | 4 |

Keys: approve keeps 2 registered keys; a partner request whose agent and
approver are not kept needs 2 fresh colours, total 4; a partner principal
instead of a partner request gives 3. Accounts: the §6.3 count (owner plus
3) still holds, since recoloured request accounts can reuse existing values
when only their inequality within the request is tested.

**Result: `B` covers every case with one slot to spare on requests, log
and revocations, and exactly (tight) on keys for approve and reject.**
Lowering `NK` to 3 would break completeness; lowering `MAX_R` to 2 (the
§6.3 cost fallback 3) would still be complete. Raising nothing is needed.

## Exceptions E1 and E2: who covers them

| Guard | Covered by | Status at `3426c92` |
|---|---|---|
| request `TooManyPending` at `pending = MAXP`, and INV-9 across `MAXP − 1 → MAXP` | `h_raw_request` (free `u32` pending): exact result, `Ok ⇒ pend < MAXP`, `pend' = pend + 1`, both boundary covers | **covered** |
| add `LogFull` at `G = MAXU` | `h_raw_add` (free `G`) | **covered** |
| request `LogFull` at `#R = MAXU` | `h_proto_request` on `Sparse` (strategy §6.2) | **not covered**: `ArrStore` cannot hold `MAXU` requests, so no current harness reaches it |
| approve `LogFull` at `#L = MAXU` | `h_proto_approve` on `Sparse` | **not covered** for the same reason; unreachable from `Inv` (LEM-3), so it matters only for ROB-2 |

The two gaps are the M2 `Sparse` harnesses, already planned. Until they
land, ROB-2 for request and approve rests on the code review in §4.

## Reads, BMC, refinement

- **Reads** (`h_read*`) quantify over one request or one page. A page is
  clamped to `#L` (`approvals` ends at `min(from + min(limit, 100), #L)`),
  and RD properties relate one page entry to one request, so the same ρ
  with `W` = that request applies. The page's own arithmetic over any
  `u64` is `h_page_arith`'s job (M2, not built).
- **BMC** (`h_bmc_from_init`, depth 5) is not covered by this theorem: it
  explores histories from `Init`, not single steps. It exists for trace
  properties' witnesses; their safety half follows from the step harnesses
  by induction over `Inv ∧ GH`.
- **Refinement** (`h_ref_*`) checks `α(step(s)) = Next(α(s))` entry by
  entry, so it is a POST-shaped property and falls under the theorem. With
  ρ, TLC's own small `MaxReg`/`Payloads` model is then the only bounded
  part left, and CUT-3 (TLAPS) is what would remove it.

## What this rests on

- CUT-1's footprint (machine-checked per operation).
- That the core compares ids, keys and accounts only by `==`, `<`, `≤`
  (by inspection of `core/src/lib.rs` at `3426c92`: no arithmetic on ids
  except `+ 1` on counters and `saturating_sub` on `pending`; the
  `#![forbid(unsafe_code)]` core has no hashing or ordering of keys).
  A pin bump re-reads this.
- The `Store` laws (ST-1) for `ArrStore`, so a lookup by key or position
  really touches one entry.
