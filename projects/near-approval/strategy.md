# NEAR Approval Contract Formal Verification Strategy

## Target

[`difflabai/trust-framework`](https://github.com/difflabai/trust-framework)
`contracts/approval/`: a NEAR contract where an agent requests an action with
its registered key (event `approval_requested`), an approver approves it with
its own key (event `action_approved`), and approval proofs are publicly
readable per request or as a paged log.

| | |
|---|---|
| Pinned commit | `3426c9246cee98dbfaa3ff7980bd85ff839d60d6`, the head of trust-framework PR #15 (adds `reject`, registration ids and revocation times, key events). This pin is **provisional**: it is on branch `claude/near-approval-contract-qin858`. Re-pin when the branch merges (OQ-1). Previous pin: `5736251`. |
| Crates | `approval-core` (`core/src/lib.rs`, 749 lines incl. docs). A dependency-free state machine, generic over account `A` and key `K`, holding *all* authorization and transition logic. `approval-contract` (`contract/src/lib.rs`, 976 lines incl. tests). A near-sdk 5.29 shell: env → `Caller`, `Store` over `LookupMap`, NEP-297 events, JSON views. |
| In the TCB via `Cargo.lock` | near-sdk 5.29.1, near-sdk-macros 5.29.1, near-sdk-core 4.2.3, near-sdk-env 0.1.6, near-account-id 2.6.0, near-sys 0.2.14, borsh 1.8.1, serde_json 1.0.151 |
| Mirror | git submodule `projects/near-approval/source-mirror` (same pattern as ironclaw) |

The split is deliberate. Every decision is in `approval-core`, which has no
dependencies, so Kani and Verus can target **the deployed logic itself**
rather than a model of it. The shell is thin enough to cover with tests,
review and wasm inspection.

**Status: plan only.** Kani, Verus, scryer-prolog, near-sdk and
near-workspaces could not be downloaded in the authoring environment, so none
of them has run. Claims about those tools and about NEAR runtime behaviour
come from memory and carry **[conf: high|med|low]**. What did run, offline,
against the pinned core:
- its 21 tests, including a randomized state-machine spec with an exact-error
  oracle, frame conditions and a ghost-state model of revocation;
- 29 hand-seeded mutants: 27 killed, 2 equivalent (F-14);
- a plain-mode prototype of the Kani harness design, against the previous
  core API (not committed; §6.1).

---

## 1. What we want to establish

For the contract deployed at account `C`, assuming its code hash equals the
reproducible build of the pin and the assumptions in §3 hold:

- **(a) Provenance.** Every published proof `π` comes from:
  - a request signed by key `π.agent_key`, registered as **Agent** to
    `π.agent_account_id`;
  - followed by an approval signed by key `π.approver_key`, registered as
    **Approver** to a **different** account.

  The approval call carried exactly `π.action`. The agent key's registration
  under which the request was made was **continuously** in force from request
  to approval. Each call came from the signing account itself: directly, or
  via code deployed on that account. VER-8 rules the second case out for each
  proof.
- **(b) Permanence.**
  - Requests and proofs are never changed or removed.
  - A request is approved at most once.
  - A request whose agent key is revoked while pending is void forever.
- **(c) Public readability.**
  - `get_approval(i)` returns exactly the recorded proof.
  - The paged log yields every proof exactly once, in approval order, under
    the documented client loop.
- **(d) Robustness.**
  - The core never panics.
  - A call the core rejects writes nothing and emits nothing.
  - An agent key can't hold more than 16 pending requests.
  - Every accepted request stays approvable within runtime log limits.

  A call that fails *after* acceptance (out of gas after the emit, or
  `LackBalanceForState`) writes nothing, but its log may survive in the failed
  outcome (ASM-ATOMIC, VER-1).

### Tiers: what each budget buys

| Tier | Milestones | Effort | Result |
|---|---|---|---|
| **1. Code-level core** | M0–M3 | 8–13 days | Bounded proofs (Kani) of every transition contract, invariant step, history and read property **on the real `approval-core`**, with counters and paging over all `u64`. Plus a differential store test and exact shell tests. The most assurance per day: it checks the logic that is actually deployed. |
| **2. Operational** | M4, M6, M7 | 8–11 days | Requirement consistency and an independent reference semantics (Prolog). Runtime assumptions tested on the reproducible wasm (sandbox). Deployment lock and verifier rules. |
| **3. Unbounded** | M5 | 9–15 days | Verus on the real core, removing the small-scope step. If the spike fails, Verus on a spec machine instead, which yields model-proofs only. |

Recommendation: do Tier 1 now. Tier 2 before any mainnet deployment. Tier 3
only if "formally verified" will be claimed externally.

---

## 2. Scope

**In scope**
- **`approval-core`:**
  - Functions: `add_principal`, `revoke_key`, `authenticate` (private,
    covered through its callers), `live_agent_registration` (private),
    `request_action`, `approve`, `request_status`, `approval`, `approvals`,
    `ActionRequest::proof`.
  - `ApprovalError`: all 16 variants and their messages.
  - Constants: `MAX_ACTION_LEN`, `MAX_PENDING_PER_KEY`, `DEFAULT_PAGE_SIZE`,
    `MAX_PAGE_SIZE`.
  - The `Store` trait contract, and `MemStore` as the harness store.
- **`approval-contract`:**
  - The `Store` impl.
  - `caller()`, `now()` and `ok()`.
  - All 13 `#[near]` methods.
  - Events, views and conversions.
  - Init and deposit handling.
  - Storage layout.
  - The wasm export and import surface.
- **NEAR runtime behaviour relied on** (tested, not proven):
  - signer-key identity;
  - relaying;
  - function-call key scoping;
  - atomicity and batching;
  - log, gas, return-size and storage limits.
- **Deployment configuration and off-chain verifier rules:** specified and
  checked, not implemented.

**Non-goals**
- Correctness of the TCB (§3).
- Economics and liveness. The contract stays funded only by operations. The
  pending cap bounds agent-driven growth, but approved and void requests
  accumulate.
- Features the contract deliberately lacks: rejection, expiry, M-of-N, key
  events, ownership transfer, upgrade.
- What an `action` means, and how UIs render it (ASM-DISPLAY).
- Owner honesty (ASM-OWNER).
- Off-chain consumers such as `trust-framework/ledger`.

---

## 3. Threats and trust assumptions

### 3.1 Adversaries

| ID | Adversary | Capabilities |
|---|---|---|
| ADV-AG | Malicious or compromised agent | Holds registered agent keys. Picks any `action` of 1–2048 bytes, including control and bidi characters. Calls anything, any number of times. Controls its own accounts and contracts. |
| ADV-AP | Rogue approver | The same, with an approver key. |
| ADV-RC | Malicious contract or relayer | Gets a key holder to sign a transaction to it. Relays meta-transactions. |
| ADV-OW | Compromised owner | `add_agent`, `add_approver`, `revoke_key`. |
| ADV-CA | Holder of a full-access key on `C` | Can redeploy or delete the contract. |
| ADV-GR | Griefer | Unregistered caller, or a registered agent spamming requests. |
| ADV-RPC | Lying or non-final RPC | Shows wrong or not-yet-final state. |

### 3.2 Threats → mitigating properties

| T | Threat | Mitigated by | Residual |
|---|---|---|---|
| T1 | Approval with no genuine approver, or self-approval | TX-5, INV-5, INV-6, TR-1, VER-4 | Sybil accounts registered by the owner (ASM-OWNER) |
| T2 | Request attributed to another agent | TX-3, TX-4, TR-1, SH-1; ASM-SIGNER, ASM-PRED | none |
| T3 | Action changed after request or approval | HIST-1, HIST-2, SH-12 | Redeploy (T11) |
| T4 | Unregistered, wrong-role or revoked key acts | TX-3, TR-3, HIST-8 | none |
| T5 | Approver approves content it didn't review | TX-5 (`ActionMismatch`), TR-1 | UI rendering (ASM-DISPLAY) |
| T6 | Double approval, or log inflation | TX-5, INV-3, INV-4, TR-2 | none |
| T7 | A rogue approver approves anything | By design. TR-1 gives accountability; TR-3 stops it after revocation. | yes |
| T8 | Relayed signature (phishing contract) | TX-3 (`IndirectCall`), RT-RELAY, RT-FCKEY, DEP-1, VER-8 | none if VER-8 is applied; otherwise code on the signer's own account (F-9) |
| T9 | Owner compromise | HIST-6, HIST-7: can't rewrite history. DEP-1: owner is a multisig. VER-4: verifier allowlist. | New approvals; DoS via revocation |
| T10 | Revoked agent's queued requests get approved after re-registration | TR-3, HIST-8, INV-8 | none (was R-1, fixed) |
| T11 | Contract redeployed, deleted or recreated | SH-12, DEP-1 (lock at deploy), VER-2, VER-3, VER-6, RT-CODEHASH, RT-RESET | Governance keys, if allowed |
| T12 | Storage exhaustion by an agent | INV-9 (≤16 pending per key), TR-6, RES-1 | Approved and void requests accumulate |
| T13 | Unregistered callers grief the contract | TX-0: nothing is written, and the caller pays gas | none |
| T14 | Accepted request can never be approved (log limit) | RES-2 (F-4) | none |
| T15 | Expensive views | RD-2 (≤100 per page), ROB-4, RES-3 | none |
| T16 | Spoofed `EVENT_JSON` from another contract | VER-1, RT-SPOOF | Verifier bugs |
| T17 | Event from a failed receipt | VER-1, RT-REVERT, RT-BATCH | none, if verifiers follow VER-1 |
| T18 | Non-final or forked reads | VER-1, VER-5; ASM-FINAL | RPC honesty |
| T19 | Paging client misses proofs | RD-4 | none |
| T20 | Init hijack or re-init | SH-9 | none |
| T21 | Hidden entrypoints | SH-11 | none |
| T22 | Attached funds | SH-10 | Plain transfers to `C` are locked forever (accepted) |
| T23 | Proof replayed for a second execution | VER-7 (executor dedup, max age) | Executor bugs |

### 3.3 Trust assumptions (TCB)

Each row is an `[assumptions.<ID>]` entry in `status.toml`, with a `level`
field (`high | med | low | policy | n/a`) for C-10. A mixed level is recorded
as its lowest component. Any Verus `external_body`
or `assume_specification` must cite one of these IDs.

No NEAR-maintained formal model of the protocol exists to cite (checked
2026-10-09). Each NEAR-facing entry therefore carries `source` (the Nomicon
pages, or NEPs and near-sdk docs, it relies on, read at
`[protocol_reference].nomicon_commit`) and, where relevant, `arena_excludes`
(the [near-proof-arena](https://github.com/ilblackdragon/near-proof-arena)
scope exclusions that keep a machine-checked model of it out of reach; see
`near-proofs/`). `upstream-watch` reports changes to both.

| ID | Assumption | Level | Checked by |
|---|---|---|---|
| ASM-SIGNER | `signer_account_pk()` is the key whose signature over the originating tx was verified, and it was an access key of `signer_account_id()` at that time. Signatures are unforgeable. | high | RT-KEY |
| ASM-PRED | `predecessor_account_id()` can't be forged. It equals the signer for the tx's first receipt, **and** when code deployed on the signer's own account makes the call (F-9). | high | RT-RELAY, RT-SELFACCT |
| ASM-ATOMIC | Atomicity is per receipt. A panic, out-of-gas or `LackBalanceForState` reverts every write of that receipt. Several FunctionCall actions in one tx share one receipt, so a later failing action reverts the earlier ones. Logs of a failed receipt may remain visible. | high (revert); med (logs) | RT-REVERT, RT-BATCH |
| ASM-SEQ | Receipts on one account execute one at a time. The contract creates no promises, so there is no reentrancy. Each successful action is one atomic model step. | high | SH-12, review |
| ASM-TIME | `block_height` and `block_timestamp` never decrease across receipts on one account. | med (height high, timestamp med-high) | Used only by INV-10, TR-4 |
| ASM-FINAL | State at finality `final` is never reverted. | high | none |
| ASM-CODE | Code changes only through `DeployContract` or `UseGlobalContract` on `C` (both need a full-access key on `C`). If `C` uses a NEP-591 global contract referenced by account id, it also changes through `DeployGlobalContract` by that account. `DeleteAccount` erases state, and a recreated account starts empty. | med | RT-RESET, DEP-1 |
| ASM-SDK | `#[init]` panics if state exists. `#[private]` requires predecessor = current account. Non-payable change methods reject deposits. `&self` methods never write. Only `#[near]` impl methods are exported. `PanicOnDefault` blocks default init. | high | SH-9, SH-10, SH-11, `cargo expand` review |
| ASM-STORE | `store::LookupMap` is a map keyed by `prefix ‖ borsh(key)`. Its writes are flushed when the contract struct drops after `state_write`. | high (semantics); med (flush) | ST-4, ST-5, ST-6 |
| ASM-IDENT | `PartialEq` on `AccountId` and `PublicKey` is an equivalence matching equality of their Borsh bytes, and `clone` preserves it. The core uses `A`/`K` only via `Clone` and `PartialEq` (`#![forbid(unsafe_code)]`, no `Ord`/`Hash`). This **parametricity** justifies small identities in harnesses. | high | Harnesses instantiate `A`/`K` with opaque newtypes (`Acct(u8)`, `Key(u8)`) implementing only `Clone`, `PartialEq`, `Debug` and a hand-written `kani::Arbitrary`, so any new trait bound upstream breaks the harness build |
| ASM-STAKE | The account must hold `storage_usage × 10^19` yocto, with about 40 bytes of overhead per record. | med (rule high, constants med-high) | RES-1 |
| ASM-LIMITS | `max_total_log_length` 16384 B. 100 logs. 4 MiB return data. 300 TGas per call. The view gas cap is set per node. | med | RES-2, RES-3 |
| ASM-META | NEP-366: the inner receipt has signer = relayer, so relayed calls fail `IndirectCall`. The same holds for NEP-518 eth-implicit accounts. | med | RT-METATX |
| ASM-FCKEY | Function-call keys restrict receiver and methods, can't attach a deposit, and have an allowance. Function-call keys can't add keys. | high | RT-FCKEY |
| ASM-COMPILE | rustc/LLVM/wasm-opt preserve core semantics from host to wasm32. The release profile keeps `overflow-checks = true`. The only on-chain `usize` use is `action.len() > MAX_ACTION_LEN`; every value is far below 2³², so host and wasm32 agree (`MemStore` is off-chain). `cfg(feature = "borsh")` gates only `use` and `derive` items, so Kani (borsh off) and the wasm (borsh on) compile the same logic. | n/a | RT-CODEHASH, RT-TRACE, `check-pin.sh` grep |
| ASM-MODEL | *Until M5 (code-level Verus):* a core step on a state larger than the Kani bound behaves like one within it (the §6.3 small-scope argument). | med | Plain-mode random traces of ≤200 steps, MC-2. Removed by M5 path A. |
| ASM-SPEC | The specs (`spec.rs`, Verus, Prolog) state the intended behaviour. | n/a | Independent authorship, signed off by a **named human who did not write `approval-core`** (`[review] spec_reviewer`), required before any K/V property is `verified*`. Also traceability (C-7), mutants and three-way trace replay. |
| ASM-TOOLS | Kani (CBMC, unwinding assertions on), Verus with Z3, and scryer-prolog are sound at the pinned versions. | n/a | `tools/versions.env`, the canary lemma must fail, mutants must be caught |
| ASM-OWNER | The owner registers keys honestly. It could otherwise register two accounts it controls and approve anything. | policy | DEP-1 (multisig/DAO), VER-4 |
| ASM-DEPLOY | The deployed code is the reproducible build of the pin, locked at deploy. | policy | DEP-1, VER-2, VER-3 |
| ASM-DISPLAY | The approver UI renders `action` faithfully (escaped). The approver's tx commits to the text (TX-5); this assumption covers only its rendering. | policy | none |
| ASM-STRLEN | *(M5 only.)* `String::len` is the UTF-8 byte length, and `is_empty ⇔ len = 0`. | high | none |

---

## 4. Findings

### Resolved upstream before pinning

These were found by review and planning on the first draft, and fixed in
`5736251`:

| | Finding | Fix |
|---|---|---|
| R-1 | Re-registering a revoked agent key revived its pending requests | `Principal.active_from`. Only requests with `id ≥ active_from` are approvable. Void is terminal. |
| R-2 | Error messages contained one another as substrings, which made `should_panic` tests ambiguous | Messages rewritten, plus test `error_messages_are_distinct` |
| R-3 | The README paging loop truncated when `limit > 100` and never ended when `limit = 0` | Stop on an empty page (README, doc comments, test) |
| R-4 | Approvals weren't bound to content | `approve(request_id, action)`, plus `ActionMismatch` |
| R-5 | Any agent key could drain the storage balance | `MAX_PENDING_PER_KEY = 16`, plus `TooManyPending` |
| R-6 | The randomized test checked only ok/err, not which error | Exact first-failing-guard oracle |

Fixed in `3426c92` (PR #15):

| | Finding | Fix |
|---|---|---|
| R-7 (was F-8) | Key registry changes emitted no events | `key_added` / `key_revoked` events |
| R-8 (was F-12) | No `[package.metadata.near.reproducible_build]` or `repository` | Both added (pinned `cargo-near` image and digest); upstream CI builds the reproducible wasm |
| R-9 (was F-13) | `approval-contract` had never been built against real near-sdk | Upstream CI runs `cargo test -p approval-contract`, the reproducible build and near-workspaces sandbox tests |

### Open

| ID | Finding | Resolution path |
|---|---|---|
| F-4 | `MAX_ACTION_LEN` is coupled to the 16 KiB log limit. The worst-case `action_approved` line is about 13.0 KB (2048 control bytes escaped to `\u00XX`, 64-char accounts, secp256k1 keys, max `u64`s). The limit breaks above about 2.6 KB. Upstream has a doc comment but no test. | RES-2 unit test (OQ-4) |
| F-6 | `revoke_key` calls `remove_principal` before knowing the key exists. The core's "no writes on `Err`" holds only because removing an absent key is a no-op (L-REMOVE-ABSENT). On-chain the call panics before any flush, so nothing is written. | ST-2 records it. Optionally reorder upstream (OQ-5). |
| F-7 | `approve`'s `LogFull` branch is unreachable under `Inv`: a pending request implies `#L < #R ≤ MAXU`. | Kept as defence in depth. LEM-3. |
| F-9 | `predecessor == signer` also admits code deployed on the signer's own account. | DEP-1 requires registered keys to be function-call keys with receiver `C`. RT-SELFACCT. |
| F-10 | **formalver tooling defects:** <br>(a) `run-prolog.sh` ends with `\|\| true` and runs `-g "run_tests, halt."`; a failing `run_tests` falls through to the toplevel, which exits 0 at EOF. Failures never fail the script. <br>(b) `run-verus.sh` and the README's direct `verus` command omit `--cfg 'feature="verus"'`, so ironclaw's `cfg(feature="verus")` spec and proof modules are never compiled [conf: high]. The README's `./tools/get-z3.sh` lives under `source/` in the Verus repo. <br>(c) ironclaw proofs take their conclusion as a `requires`. <br>(d) ironclaw's gitlink `d313f44` ≠ recorded pin `34550ad`. <br>(e) No CI. | M0 fixes (a), (b) and (e), and decides (d) (OQ-6). Rule for this project: no proof assumes its conclusion. |
| F-15 | PR #15 changes the shell: a `reject` method, `action_rejected`, `key_added` and `key_revoked` events, `agent_key_revoked_at` / `approver_key_revoked_at` on proof views, `get_revocation`, and a `v` storage prefix for revocations. SH-4..SH-8, SH-10, SH-11 (export count), C-4, ST-5 and RES-1 still describe the `5736251` shell. | Rewrite them at M3, before any is checked. The core-level properties (§5.1–5.5) are already updated. |
| F-16 | `insert_revocation` is "written at most once per id" by contract, and the stores disagree otherwise: `MemStore` keeps the first write, the contract's `LookupMap` the last. The core writes `P(k).reg` on revoke, which INV-11 keeps out of `V`, so the case is unreachable from `Init`. | INV-11/INV-12 prove the law holds on reachable states. ST-2 records the call. |
| F-14 | Two equivalent mutants. In `live_agent_registration`, dropping the role check or the account check survives all tests: under INV-8 both are implied by `active_from ≤ id`. They are kept as defence in depth. | LEM-4 proves the redundancy, so the equivalence is established and not merely assumed. |

---

## 5. Property catalogue

### 5.0 Notation

- **State** `s = ⟨o, P, R, L, G, V⟩`:
  - `o` is the owner.
  - `P : K ⇀ ⟨acct, role, reg, from, pend⟩` is the registry. `reg` is
    `registration_id`, `from` is `active_from` and `pend` is `pending`.
  - `R[i] = ⟨id, aa, ak, ag, act, rt, ap, rj⟩` is a request, with `ag` the
    agent's registration id, `ap : Option⟨ix, ba, bk, bg, at⟩` and
    `rj : Option⟨ba, bk, bg, at⟩` (`bg` the approver's registration id).
  - `L : Seq<u64>` is the approval log.
  - `G : u64` is the registration counter; `V : RegId ⇀ BlockTime` records
    when each revoked registration was revoked.
- **Constants:** `#R`, `#L` are the store counters. `MAXU = 2⁶⁴−1`,
  `N = 2048`, `MAXP = 16`, `PG = 100`, `DPG = 50`. `len` is the UTF-8 byte
  length. `⊕` is saturating `u64` addition (`saturating_add`), and `∸` is
  truncated subtraction.
- **Caller** `c = ⟨pred, sig, key⟩`.
- **Predicates:**
  - `Holds(s,c,ρ) ≜ c.pred = c.sig ∧ P(c.key).acct = c.sig ∧ P(c.key).role = ρ`
  - `Live(s,i) ≜ P(R[i].ak) = ⟨R[i].aa, Agent, f, _⟩ ∧ f ≤ i`
  - `Pend(s,k) ≜ #{i ≥ P(k).from : R[i].ak = k ∧ R[i].ap = None ∧ R[i].rj = None}`
  - `Decidable(s,i)`: the first failing guard of `RequestNotFound`
    (`i ≥ #R`), `AlreadyApproved`, `AlreadyRejected`, `AgentRevoked`
    (`¬Live(s,i)`), shared by `approve` and `reject`.
  - `Status(s,i)`: `Approved` if `R[i].ap ≠ None`, else `Rejected` if
    `R[i].rj ≠ None`, else `Pending` if `Live(s,i)`, otherwise `Void`.
- **Operations:** `Add(a,k,acct,ρ)`, `Revoke(a,k,t)`, `Req(c,act,t)`,
  `Appr(c,i,act,t)`, `Rej(c,i,t)`. `next(s,op)` is the post-state, equal to
  `s` on failure. `Init(o) = ⟨o,∅,[],[],0,∅⟩`. `Reach` is the set of states reachable from
  `Init`, and `Inv` is the conjunction of the INV properties.

**Technique codes:**

| Code | Meaning | `evidence` |
|---|---|---|
| **K** | Kani on the real `approval-core` (`MemStore<u8,u8>` or a ghost store) | `bounded-proof` |
| **Kp** | Same harness bodies as random tests (plain `cargo test`) | `test` |
| **VC** | Verus on the real core (M5 path A) | `proof` |
| **VM** | Verus spec machine (M5 path B) | `model-proof` (+ ASM-MODEL) |
| **P / PM** | Prolog consistency check / bounded model check or trace replay | `check` / `model-check` or `test` |
| **D** | near-sdk unit or differential test (`near-tests/`) | `test` |
| **S** | near-workspaces sandbox on the reproducible wasm | `test` |
| **W** | CI static check of the wasm | `check` |
| **R** | Review, signed off in `status.toml` | `review` |
| **X** | Deployment check script | `check` |

### 5.1 Transition contracts (TX): real code

Each TX property states `result = expected(s, op)`, with the **exact** error
being the first failing guard in the listed order. Panic strings are API.

| ID | Function | Statement | Check |
|---|---|---|---|
| TX-0 | all five mutators | **Atomic failure:** `Err ⇒ s' = s`. No `Store` mutator runs on failure, except `remove_principal` of an absent key in `revoke_key` (F-6, a no-op). | K / VC, Kp |
| TX-1 | `add_principal(s,a,k,acct,ρ)` | `Ok(p) ⇔ a = o ∧ k ∉ dom P ∧ G ≠ MAXU`. Errors: `NotOwner`, `KeyAlreadyRegistered`, `LogFull`. `p = ⟨acct,ρ,G,#R,0⟩`, `P' = P[k ↦ p]`, `G' = G+1`. `R`, `L`, `V`, `o` unchanged. | K / VC, PM |
| TX-2 | `revoke_key(s,a,k,t)` | `Ok(P(k)) ⇔ a = o ∧ k ∈ dom P`. Errors: `NotOwner`, `KeyNotRegistered`. `P' = P \ {k}`, `V' = V[P(k).reg ↦ t]`. | K / VC, PM |
| TX-3 | `authenticate(s,c,ρ)` | `Ok(P(c.key)) ⇔ Holds(s,c,ρ)`. Read-only. Errors: `IndirectCall`, `UnknownKey`, `WrongRole`, `KeyAccountMismatch`. | K (through TX-4, TX-5) |
| TX-4 | `request_action(s,c,a,t)` | `Ok(r) ⇔ Holds(s,c,Agent) ∧ 1 ≤ len(a) ≤ N ∧ P(c.key).pend < MAXP ∧ #R ≠ MAXU`. Errors: TX-3, then `EmptyAction`, `ActionTooLong`, `TooManyPending`, `LogFull`. <br>`r = ⟨#R, c.sig, c.key, P(c.key).reg, a, t, None, None⟩`, `R' = R·r`, `P' = P[c.key ↦ pend+1]`. `L`, `o` unchanged. | K / VC, PM |
| TX-5 | `approve(s,c,i,a,t)` | `Ok(π) ⇔ Holds(s,c,Approver) ∧ Decidable(s,i) ∧ R[i].act = a ∧ c.sig ≠ R[i].aa ∧ #L ≠ MAXU`. Errors: TX-3, then `RequestNotFound`, `AlreadyApproved`, `AlreadyRejected`, `AgentRevoked`, `ActionMismatch`, `SelfApproval`, `LogFull`. <br>`R' = R[i].ap ↦ Some⟨#L, c.sig, c.key, P(c.key).reg, t⟩`, `L' = L·i`, `P' = P[R[i].ak ↦ pend−1]`. `π = proof(R'[i]) = approval(s',i)`; its `request_id` is the stored `R[i].id` (`= i` by INV-1). | K / VC, PM |
| TX-7 | `reject(s,c,i,t)` | `Ok(r) ⇔ Holds(s,c,Approver) ∧ Decidable(s,i) ∧ c.sig ≠ R[i].aa`. Errors: TX-3, then `RequestNotFound`, `AlreadyApproved`, `AlreadyRejected`, `AgentRevoked`, `SelfApproval`. <br>`R' = R[i].rj ↦ Some⟨c.sig, c.key, P(c.key).reg, t⟩`, `P' = P[R[i].ak ↦ pend−1]`, `r = R'[i]`. `L`, `G`, `V`, `o` unchanged. | K / VC, PM |
| TX-6 | owner authority | `o` is set only at init and never changes. Owner checks compare the caller account the shell passes with `o`. That the shell passes the **predecessor** is SH-1. | K / R |

### 5.2 State invariants (INV): for every `s ∈ Reach`

Checked by K (`h_init` plus an inductive step from an arbitrary `Inv` state
within bounds), VC/VM (unbounded), PM and Kp.

| ID | Statement |
|---|---|
| INV-0 | `P` is a function: one registration and one role per key (`MemStore` has no duplicate keys). |
| INV-1 | Dense ids: `∀i<#R. R[i].id = i` |
| INV-2 | `∀i<#R. 1 ≤ len(R[i].act) ≤ N` |
| INV-3 | Log → request: `∀j<#L. L[j] < #R ∧ R[L[j]].ap = Some(x) ∧ x.ix = j` |
| INV-4 | Request → log: `R[i].ap = Some(x) ⇒ x.ix < #L ∧ L[x.ix] = i` |
| INV-5 | Separation of duties: `R[i].ap = Some(x) ⇒ x.ba ≠ R[i].aa`, and the same for `R[i].rj` |
| INV-6 | Distinct keys: `R[i].ap = Some(x) ⇒ x.bk ≠ R[i].ak`, and the same for `R[i].rj` |
| INV-7 | Registration bound: `∀k ∈ dom P. P(k).from ≤ #R` |
| INV-8 | **Registration provenance:** `k ∈ dom P ∧ R[i].ak = k ∧ i ≥ P(k).from ⇒ R[i].aa = P(k).acct ∧ P(k).role = Agent ∧ R[i].ag = P(k).reg` |
| INV-9 | **Pending count:** `∀k ∈ dom P. P(k).pend = Pend(s,k) ≤ MAXP`. For approver keys this is 0, by INV-8. |
| INV-10 | Time order (traces with non-decreasing time, ASM-TIME): `R[i].ap = Some(x) ⇒ x.at ≥ R[i].rt` component-wise, and the same for `R[i].rj` |
| INV-11 | Live registrations: `∀k ∈ dom P. P(k).reg < G ∧ P(k).reg ∉ dom V`, and `reg` is injective on `dom P` |
| INV-12 | Revocations: `∀g ∈ dom V. g < G`, and each id is revoked once (`insert_revocation`'s write-once law, F-16) |
| INV-13 | **One decision:** `¬(R[i].ap ≠ None ∧ R[i].rj ≠ None)` |
| INV-14 | Recorded ids were issued: `R[i].ag < G`, and `bg < G` on every approval and rejection |
| INV-15 | **Registration accounting:** `#dom P + #dom V = G`. With INV-11/12, every issued registration is exactly one of live or revoked. |
| INV-16 | **Registration binding:** `P(k).reg = R[i].ag ⇒ k = R[i].ak ∧ P(k) = ⟨R[i].aa, Agent, …⟩`; `P(k).reg = x.bg ⇒ k = x.bk ∧ P(k) = ⟨x.ba, Approver, …⟩` for every approval or rejection `x` |
| LEM-1 | `L` has no duplicates. |
| LEM-2 | `#L = #{i : R[i].ap ≠ None} ≤ #R` |
| LEM-3 | An unapproved request exists ⇒ `#L < #R ≤ MAXU`, so `approve`'s `LogFull` is unreachable (F-7). |
| LEM-4 | Under INV-8: `Live(s,i) ⇔ i < #R ∧ R[i].ak ∈ dom P ∧ P(R[i].ak).from ≤ i`. The role and account conjuncts are redundant (F-14). |

### 5.3 History properties (HIST): `s → s'`, transitively closed

| ID | Statement | Check |
|---|---|---|
| HIST-1 | Request content is immutable and never removed: `#R' ≥ #R` and `R'[i].{id,aa,ak,act,rt} = R[i].{…}` | K / VC, Kp |
| HIST-2 | Decisions are immutable: `R[i].ap = Some(x) ⇒ R'[i].ap = Some(x)`, and the same for `rj` | K / VC |
| HIST-3 | The log is append-only: `L ⊑ L'` | K / VC |
| HIST-4 | Counter deltas: `#R` grows by 1 exactly on a successful `Req`, and `#L` grows by 1 exactly on a successful `Appr`. Otherwise both deltas are 0. | K / VC |
| HIST-5 | Proof stability: `approval(s,i) = Some(π) ⇒ approval(s',i) = Some(π)` | K / VC |
| HIST-6 | Registry discipline: `o' = o`. `P'` differs from `P` only by (a) a successful `Add`/`Revoke` with caller `o`, or (b) the `pend` field of the requesting or decided request's agent key on a successful `Req`/`Appr`/`Rej`. | K / VC |
| HIST-7 | The owner can't rewrite history: `Add`/`Revoke` leave `R`, `L` unchanged, and `Rej` leaves `L` unchanged, from **any** state. | K |
| HIST-8 | **Void is terminal:** `Status(s,i) = Void ⇒ Status(s',i) = Void` | K / VC, PM |
| HIST-9 | **Rejected is terminal:** `Status(s,i) = Rejected ⇒ Status(s',i) = Rejected` | K / VC, PM |
| HIST-10 | Registration and revocation records: `G' = G + [successful Add]`; `V` gains one entry exactly on a successful `Revoke`; `V(g) = Some(t) ⇒ V'(g) = Some(t)`. | K / VC |

### 5.4 Trace properties (TR): over `run(o, ops)`

| ID | Statement | Check |
|---|---|---|
| **TR-1** | **Provenance (headline).** If `approval(s,i) = Some(π)` for `s ∈ Reach`, there are steps `k₁ < k₂` where: <br>(a) `ops[k₁]` is a successful `Req(c₁, π.action, π.requested_at)` creating `i`, with `c₁.pred = c₁.sig = π.agent_account_id`, `c₁.key = π.agent_key`, and `P_{k₁}(π.agent_key)` an Agent registration of that account; <br>(b) `ops[k₂]` is a successful `Appr(c₂, i, π.action, π.approved_at)` with `c₂.pred = c₂.sig = π.approver_account_id ≠ π.agent_account_id`, `P_{k₂}(π.approver_key)` an Approver registration of that account, and `π.approval_index = #L_{k₂}`; <br>(c) `π.agent_key` was registered **continuously** (same registration) over `[k₁, k₂]`; <br>(d) `π.agent_registration_id` is the registration of (a) and (c), and `π.approver_registration_id` the one of (b). <br>With ASM-SIGNER and ASM-PRED: each key holder signed a tx from its own account that reached `C` directly, or through code on that account (F-9; excluded by VER-8). | K: ghost-history invariant `GH` (§6.1) checked in `h_init` and every `h_step_*` inductive step, plus `h_bmc_from_init` witnesses / VC, PM |
| TR-2 | At most once: each `i` has at most one successful `Appr` or `Rej` in any trace. | K (HIST-2, INV-13, `AlreadyApproved`/`AlreadyRejected` in `h_step_approve` and `h_step_reject`; `h_bmc_from_init`) / VC, PM |
| TR-3 | **Durable revocation:** if the registration of `R[i].ak` under which `i` was made is removed while `R[i]` is pending, then `R[i]` is never approved in any extension. This holds even if the key is re-registered to the same account and role. | K (HIST-8 + `AgentRevoked` in `h_step_*`; `h_bmc_from_init` witness: revoke, re-add, approve fails) / VC, PM (MC-1 must find **no** revival) |
| TR-4 | Time order along the log (ASM-TIME): `j₁ < j₂ ⇒ approved_at(L[j₁]) ≤ approved_at(L[j₂])` | K / VC |
| TR-5 | **Non-vacuity:** <br>• a witness reaches an approved, a rejected and a void state; <br>• every `ApprovalError` is produced by some reachable step, except `approve`'s `LogFull` (LEM-3); <br>• `request_action`'s `LogFull` only at `#R = MAXU` (ghost store). | K covers / VC, PM |
| TR-6 | **Agent storage bound,** as a one-step potential: `Φ(s) = Σ_{k agent} (MAXP − pend_k) ≥ 0` (INV-9). A successful `Req` decreases `Φ` by exactly 1. `Φ` increases only on a successful `Appr` or `Rej` (by 1) or `Add` of an agent key (by `MAXP`). So a trace segment without decisions or `Add` makes at most `Φ` successful requests: storage growth without approver or owner action is bounded. | K (`h_step_*` for the `Φ` step; `h_raw_request` for the cap boundary) / VC |
| TR-7 | **Revocation record:** `V` lists exactly the successful `Revoke`s of the trace, each under the registration id it removed (as issued, fresh, by `Add`) and with its time. With RD-8, a verifier learns from `proof_revocations` whether, and when, either key behind a proof was later revoked. | K: `GH` (ghost revocation log) in `h_init` and `h_bmc_from_init` / VC |

### 5.5 Reads (RD)

| ID | Statement | Check |
|---|---|---|
| RD-1 | `approval(s,i) = Some(π) ⇔ i < #R ∧ R[i].ap ≠ None`, with `π = proof(R[i])` field by field and `L[π.approval_index] = i`. | K / VC |
| RD-2 | **Exact page (under Inv):** for all `f, l ∈ u64`, `approvals(s,f,l) = [proof(R[L[j]]) | j ∈ f..e]` where `e = min(f ⊕ min(l,PG), #L)`. Its length is exactly `e ∸ f`: neither `filter_map` drops anything. | K / VC |
| RD-3 | **Page arithmetic, any store:** for all `f, l, count ∈ u64`, including `MAXU`: no panic or overflow; reads only `approval_count()` once, `approved_request_id(j)` for `j ∈ [f,e)`, and `request(id)` for each id those calls return; no writes. | K (`Window` store) |
| RD-4 | **Client enumeration:** with `l ≥ 1` and `from_{k+1} = from_k + len_k`, stopping at the first empty page (the documented rule), or at `from ≥ get_approval_count()`, yields `L` exactly once and in order. This holds at one `block_id`, or across states (HIST-3, HIST-5). | VC/VM / Kp, PM |
| RD-5 | View consistency: `p ∈ approvals(s,f,l) ⇒ approval(s, p.request_id) = Some(p)`, and `approval(s,i) = Some(π) ⇒ approvals(s, π.approval_index, 1) = [π]`. So a proof is findable by `request_id` (from `approval_requested`) or by `approval_index` (from `action_approved`). | K / VC |
| RD-6 | Views are pure: the core reads take `&S`, and every `get_*` takes `&self`. | K / R |
| RD-7 | `request_status(s,i) = Some(Status(s,i))` for `i < #R`, and `None` otherwise. | K / VC |
| RD-8 | `proof_revocations(s,π) = ⟨V(π.ag), V(π.bg)⟩`. Under `Inv` (INV-11, 15, 16), for `π = approval(s,i)` each component is `None` exactly when that registration is still its key's current one. | K / VC |

### 5.6 Robustness and the store contract (ROB, ST)

| ID | Statement | Check |
|---|---|---|
| ROB-1 | **No panics:** no core function panics, overflows or indexes out of bounds, for any arguments and any `MemStore` within the §6.3 bounds (beyond them, ASM-MODEL), **including non-`Inv` states**. | K (`h_raw_*`, no `assume(inv)`) |
| ROB-2 | `LogFull` guards turn counter exhaustion into a clean `Err` before the shell's `+= 1`, which would otherwise panic (overflow-checks). `request_count = MAXU` with all earlier guards passing ⇒ `Err(LogFull)`, no writes. `approval_count = MAXU` with all earlier guards passing ⇒ `Err(LogFull)`, no writes. Approve's case needs a non-`Inv` state (LEM-3). | K (raw `Sparse`, symbolic counters) |
| ROB-3 | Length boundaries in **bytes**: 0 → `EmptyAction`; 1 → ok; N → ok; N+1 → `ActionTooLong`; 1025 two-byte characters (2050 bytes) → `ActionTooLong`. | K (`h_action_len`) / Kp |
| ROB-4 | Bounded work: each mutator makes ≤ 4 `Store` reads (approve: caller principal, request, agent principal, approval count) and ≤ 3 writes. `approvals` makes ≤ `2·min(l,PG)+1` reads. No unbounded loops in mutators. | K (`Counting` store) |
| ST-1 | **Store laws** that every `Store` must satisfy: map semantics for principals (with L-REMOVE-ABSENT); `push_request` appends at `request_count()`; `replace_request` overwrites at `r.id`; the log is a sequence; reads are pure. | K (`MemStore`, `Sparse`) |
| ST-2 | **Store protocol (the correspondence hinge).** The core's mutating `Store` calls are exactly: <br>• add → `[increment_registration_count(), insert_principal(k)]`, with `k ∉ dom P` and `G < MAXU`; <br>• revoke → `[remove_principal(k), insert_revocation(P(k).reg, t)]`, the first also on failure with `k ∉ dom P` (F-6), the second with `P(k).reg ∉ dom V` (F-16); <br>• request → `[insert_principal(c.key, pend+1), push_request(r)]`, with `r.id = #R < MAXU`; <br>• approve → `[insert_principal(R[i].ak, pend−1), replace_request(r), push_approval(i)]`, with `r.id = i < #R`, `r` equal to `R[i]` except `ap` going from `None` to `Some`, and `#L < MAXU`; <br>• reject → `[insert_principal(R[i].ak, pend−1), replace_request(r)]`, with `r.id = i < #R` and `r` equal to `R[i]` except `rj` going from `None` to `Some`; <br>• any other failure → no calls. <br>This makes the on-chain impl's differences from `MemStore` unreachable: `replace_request` inserts unconditionally (`MemStore` drops an out-of-range write), and `+= 1` at `u64::MAX` panics under overflow-checks instead of returning `LogFull`. | K (recording `Sparse`) |
| ST-3 | `Sparse`, a line-by-line transliteration of `impl Store for ApprovalContract` with each `LookupMap` replaced by an association list, refines `MemStore`: same results, same abstraction `α`. | K (`h_refine_*`) |
| ST-4 | **The real store refines `MemStore`:** `ApprovalContract` and `MemStore<AccountId,PublicKey>` run random op sequences (10k × 50) through the core and through the public methods. **Before each step the contract is persisted and reloaded** (`state_write`, drop, `state_read`), so every step reads Borsh from cold storage. After every step, results and `α` are equal. | D (`store_diff.rs`) |
| ST-5 | Storage layout: prefixes `p`, `r`, `a` are pairwise distinct and distinct from `STATE`. After random runs, every key is `STATE` or `p|r|a ‖ borsh(key)`. | D / R |
| ST-6 | Layout stability: golden Borsh bytes for `STATE` and one value of each map (ed25519 and secp256k1 keys; approval `Some` and `None`). A diff must be flagged as storage-breaking in the pin-bump PR. | D |

### 5.7 Resource limits (RES)

| ID | Statement | Check |
|---|---|---|
| RES-1 | **Storage growth per operation:** <br>• `Req` adds one record of ≤ `B_req` bytes and rewrites one principal at the same size (`pend` is fixed-width); <br>• `Appr` grows one request by ≤ `B_ap` and adds a log record of `B_log`; <br>• `Add` adds ≤ `B_p`; <br>• failures add nothing. <br>The bounds come from the Borsh layout (D), and the deltas are measured on-chain (S). With INV-9, the worst case an agent key can lock without an approver is 16 × `B_req` (about 0.36 NEAR). | D / S |
| RES-2 | Every accepted request is approvable within log limits: for `1 ≤ len(a) ≤ N`, the worst-case `approval_requested` and `action_approved` lines are each ≤ 16384 B (about 13.0 KB today, F-4). | D (explicit-limit unit test) / S |
| RES-3 | `get_approvals(0,100)` over 100 maximum-size, fully escaped proofs stays under the view gas cap and the 4 MiB return limit (estimate about 1.3 MB). | S |

### 5.8 Contract shell (SH)

| ID | Statement | Check |
|---|---|---|
| SH-1 | **Env mapping:** `caller() = ⟨predecessor, signer, signer_pk⟩` and `now() = ⟨block_height, block_timestamp⟩`, probed with pairwise-distinct context values. `add_agent` passes `Agent`, `add_approver` passes `Approver`. All three owner methods pass the **predecessor**: a DAO owner works, and an owner's signature relayed by another contract fails. | D (upstream tests cover part) / R |
| SH-2 | One core transition per change call, with no other writes (`α` compared around each public call). | D |
| SH-3 | **Exact errors:** a core `Err(e)` panics with exactly `e.as_str()`, compared exactly via `catch_unwind` after extracting `panic_msg` from the mocked runtime's payload (payload format recorded at M3), and nothing is logged. On-chain the failure message is `"Smart contract panicked: " ‖ as_str` [conf: high on the prefix]. | D, S |
| SH-4 | `approval_requested` is exactly one log line, `EVENT_JSON:{"standard":"trust_approval","version":"1.0.0","event":"approval_requested","data":RequestView(r)}`, with `status: "pending"`. The method returns `r.id`. The emit happens only after the core returned `Ok`. The only failures after it are gas exhaustion and `LackBalanceForState` (ASM-ATOMIC, VER-1). | D / R |
| SH-5 | `action_approved` is exactly one line. Its `data` = the return value = `get_approval(i)` now and later (HIST-5). | D |
| SH-6 | No other method logs. | D |
| SH-7 | **View mapping:** <br>• `get_approval` is `approval`, and `get_approvals(f?,l?)` is `approvals(f.unwrap_or(0), l.unwrap_or(50))`; <br>• `get_request(i)` is `None` for `i ≥ #R`, otherwise a `RequestView` with every field equal to `R[i]` and `status = request_status`; <br>• `get_principal(k)` is `None` for `k ∉ dom P`, otherwise `account_id`, `role` and `pending` equal `P(k)`; <br>• `get_owner` is `o`; <br>• the counts are the store counters. | D |
| SH-8 | **JSON shape:** <br>• field names as in the README; <br>• `*_ns` are strings (`U64`); ids, indices and heights are numbers; <br>• arguments `{}`, or `from_index`/`limit` set to `null`, give the defaults; whole-args `null` and empty input fail with near-sdk's deserialization panic (message recorded); <br>• `From` conversions and `request_view` preserve every field. | D, S |
| SH-9 | **Init:** `new` succeeds once (`#[init]`) and only from `C` (`#[private]`). Every method fails before init (`PanicOnDefault`). Post-init state is `Init(owner_id)`. Wrapper-only, so unit tests can't see it [conf: high]. | S / R |
| SH-10 | **Deposits:** call all 13 exports with 1 yocto attached, using **full-access** keys (function-call keys can't attach deposits), calling `new` on a fresh, uninitialized deployment. Every change method and `new` must fail with near-sdk's non-payable panic; record the outcome for each `get_*` [conf: med that the wrapper checks `&self` methods]. | S |
| SH-11 | **Export surface:** function exports are exactly the 13 methods plus `contract_source_metadata` and, if the build embeds the ABI, `__contract_abi` [conf: med]. Non-function exports are exactly `memory` (plus `__data_end`/`__heap_base` if present). `wasm-surface.expected` lists both sets. No `Store` method, upgrade or owner transfer is exported. | W / S |
| SH-12 | **No escape hatches:** wasm imports include no `promise_*` (which covers create, then, batch, yield, and, return), no deploy, no delete, and no transfer. The only storage keys written are those of ST-5. | W / R |

### 5.9 Runtime assumption tests (RT): sandbox, reproducible wasm

| ID | Establishes | For |
|---|---|---|
| RT-KEY | A function-call key `k` of account `a` arrives as `signer = predecessor = a` with `signer_pk = k`. An unregistered key on the right account gets `UnknownKey`. A registered key added to another account gets `KeyAccountMismatch`. | ASM-SIGNER |
| RT-RELAY | `request_action`/`approve` through a third-party relay contract fails with `IndirectCall`. | ASM-PRED |
| RT-SELFACCT | A contract on the signer's own account calling `C` **succeeds** (documents F-9). | ASM-PRED |
| RT-METATX | NEP-366 delegate action: record the outcome (expected `IndirectCall`). | ASM-META |
| RT-FCKEY | An agent function-call key scoped to `request_action` can't call `approve` or `add_agent`. Assert `InvalidTxError::InvalidAccessKeyError(MethodNameMismatch)`, not a contract panic: the contract would also reject both calls, so only the error kind shows the runtime enforced the scope. | ASM-FCKEY |
| RT-REVERT | Force failures, including `LackBalanceForState` after draining `C`'s balance, and a call with just enough gas for the core step. State and views must be unchanged. Record whether the event survives in the failed outcome. | ASM-ATOMIC |
| RT-BATCH | One tx `[request_action("a"), request_action("")]`, signed by a **full-access** key of the agent account that is also its registered agent key (a function-call key can sign only single-action txs). The outcome fails at action index 1 with "action is empty", and the counters are unchanged. Record whether the first event appears. | ASM-ATOMIC |
| RT-RESET | Delete and recreate `C`: counters reset. VER-3 (a full-access key or a `DeleteAccount` since `b₀`) detects it. VER-6 is only a heuristic that catches it while counters are below cached values. | ASM-CODE |
| RT-SPOOF | A spoofer contract logs a forged `EVENT_JSON`. The VER-1 `executor_id` rule rejects it. | VER-1 |
| RT-CODEHASH | The wasm under test is the `cargo near build reproducible-wasm` output. Record its sha256 (hex) **and** the NEAR `code_hash` (base58 of sha256). *Was blocked by F-12 (resolved upstream, R-8).* | ASM-DEPLOY, ASM-COMPILE |
| RT-TRACE | **Main flows on the deployed artifact.** Replay every `conformance/traces/*.txt`, plus 200 random sequences of ≤30 ops, on the reproducible wasm. For each step, these must equal `spec.rs`: the result or return value, the exact failure message, the receipt logs, and the `get_*` views (including `{}` args, nulls, `limit = 0`, and values > 2⁵³). *Was blocked by F-12 (resolved upstream, R-8).* | ASM-COMPILE, ASM-SDK |

### 5.10 Deployment and verifier rules (DEP, VER)

**DEP-1 Deployment configuration** (X: `deploy-checks/check_deployment.sh <net>`)
1. `code_hash(C)` equals the reproducible build of the pin.
2. **Locked at deploy.** The deploy, `new`, and deletion of every full-access
   key on `C` happen in one transaction at block `b₀`. Function-call keys
   can't add keys, and the code has no deploy, add-key or delete path (SH-12).
   So an empty full-access key list at `b₀+1` rules out any later redeploy
   [conf: high]. `C`'s code must come from a local `DeployContract` (or a
   NEP-591 global contract referenced by code hash). `check_deployment.sh`
   fails if `view_account` reports a global contract referenced by account id,
   whose owner could replace the code.
3. The owner is a multisig or DAO.
4. Every registered key exists on its bound account as a **function-call
   key**: receiver `C`, `method_names = [request_action]` for agents or
   `[approve]` for approvers, finite allowance. The contract can't list its
   keys, so the registered-key set is rebuilt by replaying every successful
   `add_agent`/`add_approver`/`revoke_key` receipt to `C` since `b₀` from an
   indexer (or NEAR Lake). This is a point-in-time check. VER-8 is the
   per-proof version.
5. `C`'s free balance ≥ current storage plus a configured buffer.

**Verifier rules.** Specified in P (`verifier_rules.pl`) and demonstrated in S.

| ID | Rule |
|---|---|
| VER-1 | Accept proof `π` for `(C,i)` only from `get_approval(i)` at finality `final`, or from an `action_approved` log in a **successful** receipt with `executor_id = C` in a final block. Events are hints. |
| VER-2 | `code_hash(C)` = expected, at the proof's block (archival) and now. |
| VER-3 | No full-access key on `C` since `b₀` (archival query plus SH-12). If governance keys are allowed: an indexer scan of every receipt to `C` since `b₀` finds no `DeployContract`, `UseGlobalContract`, `AddKey` or `DeleteAccount`. |
| VER-4 | Check `π.action` and both accounts against what is expected. Check `approver_*` against the verifier's own allowlist if the owner isn't fully trusted. |
| VER-5 | Enumerate with the RD-4 loop, reading every page at one `block_id`. |
| VER-6 | A counter decrease or a code-hash change invalidates every cached `(C,i)`. |
| VER-7 | Executors deduplicate on `(C, request_id)` and enforce their own maximum age on `approved_at_ns`. Approvals never expire or get consumed on-chain. |
| VER-8 | For each accepted `π`, archival `view_access_key(π.agent_account_id, π.agent_key)` at the block that included the request tx, and `view_access_key(π.approver_account_id, π.approver_key)` at the block that included the approval tx, both return a function-call permission with `receiver_id = C` and the DEP-1.4 method names. This closes F-9 per proof. |

### 5.11 Requirement checks (C) and Prolog model checks (MC)

| ID | Check | Tool |
|---|---|---|
| C-1 | **Authority matrix:** each change method has exactly one authority; owner, agent and approver method sets are disjoint; no key can both request and approve. | P |
| C-2 | **Guard table:** every `ApprovalError` comes from ≥1 guard. Each guard yields one error. Specified precedence = generated `code_precedence/2`. | P |
| C-3 | Error messages are pairwise distinct and substring-free (R-2; expected to pass). | P |
| C-4 | Each event comes from exactly one method. Every authority- or proof-changing operation emits an event, or has an `accepted_risk`. Since `3426c92` admin operations emit `key_added` / `key_revoked` (R-7). | P |
| C-5 | Generated constants equal the requirement constants: `DPG ≤ PG`, `MAXP ≥ 1`, and `N` within the RES-2 bound. | P |
| C-6 | The generated API surface (wasm exports and ABI) equals the requirements' API table. | P |
| C-7 | Traceability both ways: every requirement maps to ≥1 property, and every property to ≥1 requirement or threat. | P |
| C-8 | Every threat has `mitigated_by` or `accepted_risk`. | P |
| C-9 | Property and assumption IDs in `status.toml` = IDs in `traceability.pl`. | P |
| C-10 | Warn when a `verified*` property depends on an assumption with `level` below `high` whose check hasn't passed. | P |
| MC-1 | Bounded model check of the reference `step/4`: owner `o`, accounts `{a,b}`, keys `{k1,k2,k3}`, depth **6**, with state deduplication. With the real constants it must find no INV, separation-of-duties, double-approval, pending-count or revival violation, and must reach an approved state, a void state and every error except `approve`'s `LogFull`, `request_action`'s `LogFull` and `TooManyPending`. **MC-1s** reruns with scaled constants `max_pending = 2`, `max_u = 2` (C-5 checks the real ones) and must also reach `TooManyPending` and `request_action`'s `LogFull`. `approve`'s `LogFull` stays unreachable (LEM-3). Each run prints its state count, and CI enforces `mc1_state_floor` (recorded at M4 sign-off). | PM |
| MC-2 | **Trace replay:** `gen_traces.pl` writes every trace to depth *d*, with per-step results and the final views. These are replayed on the real core, on `spec.rs` (Kp), and on the wasm (RT-TRACE). | PM / Kp / S |

### 5.12 Traceability

| Requirement | Properties |
|---|---|
| R1: agent requests with its key | TX-3, TX-4, TR-1, SH-1, RT-KEY |
| R2: emits `approval_requested` | SH-4, SH-6, C-4, RT-TRACE |
| R3: approver approves with its key | TX-3, TX-5, INV-5, INV-6, TR-1, RT-KEY, RT-RELAY |
| R4: emits `action_approved` | SH-5, SH-6, C-4, RT-TRACE |
| R5: proof for a specific event is public | RD-1, RD-5, HIST-5, SH-7, SH-8, VER-1 |
| R6: all approvals public, paged | RD-2, RD-3, RD-4, RD-5, SH-7, RES-3, VER-5 |
| D1 key+account identity, D2 caller = signer | TX-3, INV-8, RT-KEY, RT-RELAY, RT-SELFACCT, RT-METATX, RT-FCKEY, DEP-1, VER-8 |
| D3 owner manages keys | TX-1, TX-2, TX-6, HIST-6, HIST-7, SH-1 |
| D4 one role per key | INV-0, INV-6, C-1 |
| D5 approver ≠ agent account | INV-5 |
| D6 approved at most once | TX-5, HIST-2, TR-2 |
| D7 durable revocation | TR-3, HIST-8, INV-8, LEM-4, RD-7 |
| D8 append-only paged log | INV-1, INV-3, INV-4, INV-7, LEM-1, LEM-2, HIST-3, HIST-4, RD-2, RD-4 |
| D9 bounded storage (action ≤ 2048 B, ≤ 16 pending/key) | INV-2, INV-9, ROB-3, TR-6, RES-1, RES-2 |
| D10 approval commits to content | TX-5, TR-1 |
| D11 no upgrade, rejection, expiry or threshold | SH-11, SH-12, C-1 |
| D12 atomic, bounded execution | TX-0, ROB-1, ROB-2, ROB-4, ST-1, ST-2, ST-3, ST-4, ST-5, ST-6, SH-2, SH-3, RD-6, LEM-3 |
| D13 timestamps recorded and ordered | INV-10, TR-4 |
| D14 deployed artifact = verified source | RT-CODEHASH, RT-RESET, RT-TRACE, DEP-1, VER-2, VER-3, VER-6 |
| D15 verification hygiene (ASM-SPEC, ASM-TOOLS) | TR-5, MC-1, MC-2, C-2, C-3, C-5, C-6, C-7, C-8, C-9, C-10 |
| D16 verifier and executor discipline | VER-1, VER-4, VER-5, VER-7, VER-8 |

---

## 6. Kani on the real core (M1–M2)

### 6.1 Crate

`projects/near-approval/kani/` is a standalone `[workspace]`. Its only
dependency is `approval-core` from the mirror (path,
`default-features = false`, so no borsh). `A`/`K` are instantiated with
opaque newtypes `Acct(u8)` and `Key(u8)` that implement only `Clone`,
`PartialEq`, `Debug` and a hand-written `kani::Arbitrary` (ASM-IDENT).

| Module | Contents |
|---|---|
| `spec.rs` | `inv`; `expected(s, op)`, the exact `Result` in guard order (needs no `Inv`); `check_step` (result, atomicity, history, post-state, frame); `check_read`; `check_page`; `abs` (`α`); the precedence table. **Ghost history** `H`: per request, the `Req` caller and the agent registration in force; per approval, the `Appr` caller. **Invariant** `GH(s,H)`: every approved `i` has `H` records satisfying TR-1 (a)–(c). Every function is tagged `// PROP: <ID>`. |
| `gen.rs` | Bounded arbitrary-state builders: `Inv`-satisfying (with a consistent `H`) and raw. |
| `ghost.rs` | Stores: `Sparse` (contract-shaped, recording, sha256 of `contract/src/lib.rs` in its header), `Window` (paging over any `u64`), `Counting`. |
| `checks.rs` / `proofs.rs` / `plain.rs` | Harness bodies; `#[kani::proof]` wrappers; random-mode tests. |
| `src.rs` | **Dual mode.** Harness bodies are written against a `Src` trait. `Sym` uses `kani::any`/`assume`: **the proof**. `Rng` uses xorshift with hints toward `Inv` states: **not a proof**. Plain mode debugs specs in seconds and gates CI without Kani. `kani/kani-stub/` lets `RUSTFLAGS="--cfg kani --cfg kani_stub" cargo check` type-check `proofs.rs`. |

During planning, a plain-mode prototype of this design (about 1,150 lines) was
validated against the pre-`5736251` core API: 11/11 tests passed and it killed
12/12 seeded mutants. It is **not committed**. M1 implements the design
against the pinned API.

### 6.2 Harnesses and covers

`run-kani.sh` fails the run on any `UNSATISFIABLE`/`UNREACHABLE` cover. Use
`--fail-uncoverable` if the pinned Kani has it [conf: low-med].

| Harness | Pre-state | Properties | Covers (must be SATISFIED) |
|---|---|---|---|
| `h_init` | `MemStore::new(OWNER)`, empty `H` | INV and GH at init | none |
| `h_step_add` | arbitrary `Inv ∧ GH` state, `#P,#R,#L ≤ 3` | TX-0, TX-1, TX-6, HIST-*, INV, GH and LEM-1..2 step, TR-6 `Φ` step | Ok, NotOwner, KeyAlreadyRegistered |
| `h_step_revoke` | same | TX-0, TX-2, TX-6, HIST-*, HIST-8, INV, GH and LEM-1..2 step, TR-3 step, TR-6 `Φ` step | Ok, NotOwner, KeyNotRegistered, a pending request becomes void |
| `h_step_request` | same; actions from the §6.3 alphabet | TX-0, TX-3, TX-4 (except the cap boundary), TX-6, HIST-*, INV, GH and LEM-1..2 step, TR-6 `Φ` step | Ok, the 4 TX-3 errors, EmptyAction |
| `h_step_approve` | same; time monotone | TX-0, TX-3, TX-5, TX-6, HIST-*, INV, GH and LEM-1..3 step, INV-10, TR-2, TR-3, TR-4 steps, TR-6 `Φ` step | Ok, the 4 TX-3 errors, RequestNotFound, AlreadyApproved, AlreadyRejected, AgentRevoked, ActionMismatch, SelfApproval |
| `h_step_reject` | same; time monotone | TX-0, TX-3, TX-7, TX-6, HIST-* (HIST-9), INV (INV-13), TR-2 step, TR-6 `Φ` step | Ok, the 4 TX-3 errors, RequestNotFound, AlreadyApproved, AlreadyRejected, AgentRevoked, SelfApproval |
| `h_raw_{op}` | arbitrary store, **no** `assume(inv)`; `pend` any `u32`, `from`, `G` and registration ids any `u64` | ROB-1, TX-0, TX-1..5 and TX-7 exact result via `expected`, HIST-7 (add, revoke, reject); for request: the INV-9 bound step (`Ok ⇒ pend < MAXP ∧ pend' = pend + 1`) and the TX-4 cap boundary | Ok per op; add: LogFull at `G = MAXU`; request: Ok at `pend = MAXP − 1` and TooManyPending at `pend = MAXP` |
| `h_bmc_from_init` | `Init` + ≤ 6 ops, ghost history | TR-1, TR-2, TR-3, TR-7 witnesses (bounded) | approved; rejected; revoke → re-add → approve old id fails with AgentRevoked |
| `h_read` | like `h_step`; `id`, `from`, `limit` any `u64` | RD-1, RD-2, RD-5, RD-7, RD-8, LEM-4 | non-empty page; void status; rejected status; a proof whose agent key was revoked |
| `h_page_arith` | `Window`: `from`, `limit`, `count`, `offset` any `u64`; out-of-page reads and any write panic; `#[kani::unwind(102)]` | RD-3, RD-6, and the page clamp | non-empty page at `count = MAXU` |
| `h_proto_{request,approve}` | `Sparse` **raw** state (no `assume(inv)`), counters any `u64` ≥ stored size. ST-2 is also checked from `Inv` states with counters equal to size. | ST-2, ROB-2 | Ok; LogFull (approve's only from non-`Inv` states, per LEM-3) |
| `h_proto_{add,revoke}` | same | ST-2 | Ok, each error |
| `h_count_{op}` | `Counting` over `MemStore` | ROB-4 | none |
| `h_refine_{op}` | the same `Inv` state in `MemStore` and `Sparse` | ST-3 | none |
| `h_store_laws_{mem,sparse}` | small arbitrary stores | ST-1, INV-0 (`MemStore`) | none |
| `h_action_len` | agent registered; `len ∈ {0, 1, 2048, 2049}` with the 1-byte case `" "`, plus the 2050-byte multi-byte case | ROB-3 | Ok, EmptyAction, ActionTooLong |
| `h_canary` | any | asserts a false property; must report FAILED | none |

### 6.3 Bounds and the small-scope argument

| Dimension | Bound | Justification |
|---|---|---|
| Accounts | 4 (owner = 0) | ASM-IDENT parametricity. `approve` reads 5 account terms: predecessor, signer, `P(c.key).acct`, `R[i].aa`, `P(R[i].ak).acct`. The guard order forces predecessor = signer = `P(c.key).acct` before the last two comparisons, so at most 3 values plus the owner are ever distinguished, and 4 values realize every reachable pattern. |
| Keys | 4 | ≤ 3 stored keys plus one "absent" value. |
| Principals / requests / log / revocations | ≤ 3 each | A step touches ≤ 2 principals (caller, agent), ≤ 1 request, ≤ 1 log slot, ≤ 1 revocation. Any one-step violation of an INV involves the touched elements plus ≤ 1 witness. |
| Registration ids, `G` | `Inv` states: ids from `0..8`, `G = #P + #V`; raw states: any `u64` | INV-15 forces `G = #P + #V ≤ 6` and INV-11/12/14 put every id below `G`, so `0..8` loses nothing within the other bounds. Ids are only compared for equality and with `G`. `G = MAXU` (add's `LogFull`) needs a raw state. |
| `from`, `pend` | In `Inv` states, `from ≤ #R` and INV-9 forces `pend = Pend(s,k) ≤ #R ≤ 3`. The cap boundary (`pend` near `MAXP`) is reachable only in `h_raw_request`, where `pend` is any `u32`. | INV-7, INV-9 |
| Ids, counters, `from_index`, `limit` | **any `u64`** | `Sparse`/`Window` stores. These are the only arithmetic-dependent paths. |
| Action | content from `{"a", " ", "é"}` in step harnesses (whitespace kills the `trim`-empty mutant; two one-byte values for equality; one multi-byte value) | The core uses only `is_empty`, `len`, `==` and `clone`. |
| Time | any `u64` | Only copied, and compared in INV-10. |
| History | inductive step (one op from an arbitrary `Inv ∧ GH` state); BMC from `Init` only for TR witnesses at depth 6 | This covers histories whose states stay within bounds. Beyond them it rests on ASM-MODEL until M5 path A. |

**Cost fallback** if a harness exceeds 20 min on a GitHub runner, applied in
order, with the bounds used recorded in `status.toml`:
1. Split further.
2. `#[kani::solver(kissat)]` (needs `kissat` on PATH) or `minisat`, whichever
   is faster. CaDiCaL is already the default [conf: med].
3. Bound requests and log at 2.
4. Use the two actions `""` and `" "` in the step harnesses: the minimum that
   keeps EmptyAction, ActionMismatch and the `trim`-empty kill.
5. In `h_action_len`, assert only the error kind.
6. In `h_page_arith`, have `Window::request` return `None` or a request whose
   `action` is `String::new()`. Content equality (RD-2) stays in `h_read`.

Counterexamples are replayed with `--concrete-playback=print` [conf: med].

### 6.4 Mutants

`kani/mutants/*.patch` are applied to a temporary copy of the core. Each must
be killed by its listed harness under Kani and by plain mode. 27 of these were
seeded against the upstream suite during planning (27/27 killed).

| Killed by (milestone) | Mutants |
|---|---|
| `h_step_*` (M1) | self-approval check; relay check; key-account binding; double log push; drop-empty; `trim`-empty; `active_from` dropped / strict / +1 / 0; no increment; no decrement; no principal write-back; action-mismatch dropped; already-approved dropped; three guard swaps; void reported as pending (`h_read`); revoke not owner-only; `approval_index` from request count; proof copies agent as approver; `push_approval` before the checks |
| `h_step_*`, `h_read` (M1, PR #15 API) | reject: self-approval check dropped, no decrement, rejection records the agent's registration; already-rejected dropped; revocation not recorded; registration count not incremented; request records registration 0; `proof_revocations` swapped (`h_read`); rejected reported as pending (`h_read`) |
| `h_raw_*` (M1) | cap off-by-one (`>=` changed to `>`) (`h_raw_request`); add's `LogFull` dropped (`h_raw_add`: the counter overflows) |
| `h_action_len` (M2) | length off-by-one; chars-vs-bytes |
| `h_page_arith` (M2) | page clamp removed; page addition wraps |
| `h_proto_*` (M2) | `LogFull` request dropped; `LogFull` approve dropped |
| `h_store_laws_mem` (M2) | `MemStore` insert pushes duplicates |
| **Must survive** (equivalent, F-14) | role check dropped / account check dropped in `live_agent_registration`. If either is killed, INV-8 or LEM-4 is wrong. |

---

## 7. Verus (M5): real code first, model as fallback

**Spike (2 days).** Wrap a copy of `approval-core` in `verus!` (a "verified
twin"). Try to verify `request_action`, `approve`, `approvals`,
`live_agent_registration` and `MemStore::{principal, insert_principal,
remove_principal}` **without changing executable code**, against
`ensures`-refinement specs over an abstract `view()` of `Store`. The known
friction is:
- generic `==`/`clone` on `A`/`K`;
- `String::len` and `String != &str` (ASM-STRLEN as `assume_specification`);
- `ok_or()?`, `Option::filter` with closures, `iter().find`/`position`, and the
  `filter_map` chains in `approvals` [conf: low-med that vstd covers them].

**Path A (preferred; 8–13 days).** If the spike succeeds:
- `Store` gains `spec fn view(&self) -> AbsState` and `spec fn wf(&self)`.
- Each public core fn `ensures`:
  `Ok ⇒ store@ == effect(old@, op)` and
  `Err(e) ⇒ err_of(old@, op) == Some(e) ∧ store@ == old@`.
- `MemStore` is verified against the trait spec. This is the satisfiability
  witness that shows the trait's `ensures` aren't contradictory.
- INV, HIST, TR and RD are proved over `view()`, unbounded, as
  `evidence = proof`. ASM-MODEL is retired for them.
- `tools/erasure-check` strips the ghost code, runs `rustfmt`, and requires
  token equality with the upstream file. The allowlisted differences are:
  - `mod tests;`
  - the functions listed in `verus/REWRITES.toml`, each with a Kani
    equivalence harness (`twin::f == upstream::f` within the §6.3 bounds) and
    reported with ASM-MODEL.
- `TRUSTED.toml` may hold ASM-IDENT, ASM-STRLEN, and std-library
  specifications missing from vstd (each tagged ASM-TOOLS).
- **Upstream adoption** (optional; replaces twin and erasure check) needs all
  of:
  - Verus crates resolve from crates.io;
  - `vstd` builds for `wasm32-unknown-unknown`;
  - `cargo near build reproducible-wasm` succeeds;
  - wasm growth ≤ 5%;
  - maintainer agreement.

**Path B (fallback; 7–10 days).** If the spike fails, write a spec machine in
`verus/src/approval/{machine,machine_spec,machine_proof}.rs`, following the
formalver three-file pattern:
- `err_of`, `effect`, `next` and `run` over `AbsState` (principals as a `Map`,
  `act: Seq<u8>`, `nat` counters with `MAXU` guards);
- lemmas for INV-0..10, LEM-1..4, HIST-1..8, TR-1..6 and RD-4/5;
- `evidence = model-proof` plus ASM-MODEL. **Never reported as a proof of the
  code.**
- Drift between `machine.rs` and `spec.rs` is controlled by shared `// PROP:`
  IDs, paired review, and MC-2 replay.

**Hygiene gate (both paths):**
- No proof assumes its conclusion: a `requires` states only well-formedness,
  such as `inv(s)` (F-10c).
- No `assume`, `admit`, `external_body` or `assume_specification` outside
  `verus/TRUSTED.toml`, and each entry there maps to an ASM ID.
- `verus/canary/false_lemma.rs` must **fail**.
- Spec mutants (drop separation of duties; drop `from ≤ i`; append to the log
  before the checks) must each break a lemma.
- `run-verus.sh` fails below `verus_min_verified`.

---

## 8. Prolog (M4)

| File | Contents |
|---|---|
| `requirements/approval_req.pl` | `requirement/2` (R1–R6, D1–D16), `method/3` (name, kind, authority), `emits/2`, `guard/4` (op, order, error, condition), `error_message/2`, `constant/2` |
| `requirements/threat_model.pl` | `adversary/2`, `threat/3`, `assumption/3` (with level), `mitigated_by/2`, `accepted_risk/2` |
| `requirements/traceability.pl` | `verified_by/2`, `property/3` |
| `model/approval_machine.pl` | `step(S0, Op, Result, S1)`: reference semantics written **from the requirements**, not transcribed from Rust. Actions are abstracted to `empty`, `ok(Tag)`, `too_long`. Constants are parameters, so MC-1s can scale them. |
| `verification/{consistency,model_check,gen_traces,verifier_rules}.pl` | C-1..10, MC-1/MC-1s, MC-2, VER-1..8 |
| `extracted/{code_facts,api_facts}.pl` | **Generated:** `code_facts` by a plain-mode test in `kani/` (exhaustive `match` over `ApprovalError`, constants, the `spec.rs` precedence table); `api_facts` by the near-unit job (wasm exports and ABI). CI fails on regeneration diff. |
| `tests/test_approval.pl` | `run_tests`, run under `run-prolog.sh`, which must halt non-zero on failure or exception |

---

## 9. Shell, runtime and deployment (M3, M6, M7)

- **Toolchain.** `tools/versions.env` pins `RUST_TOOLCHAIN` for near-tests,
  the M0 build and the sandbox helper contracts. rustc ≥ 1.82 enables wasm
  features (reference-types, multivalue) that nearcore has rejected [conf:
  med], so deployability is smoke-tested in M0, not first discovered in M6.
- **Lockfile** (near-tests and sandbox). Seed each crate's lockfile with the
  mirror's `Cargo.lock`, let Cargo add the missing entries once, commit the
  result, and build with `--locked`. CI fails if any package present in both
  lockfiles differs in version or checksum.
- **`near-tests/`** (standalone `[workspace]`; CI only, needs crates.io):
  - **Universe:** 4 accounts and 4 real ed25519/secp256k1 keys.
  - **`tests/store_diff.rs`:** ST-4, SH-2, with persist and reload every step.
  - **`tests/shell.rs`:** SH-1, SH-3..8, ST-5, ST-6, RES-1 (computed),
    RES-2.
  - **`mutants/*.patch`, each must fail the suite:**
    - `add_agent` registers Approver;
    - `caller()` uses the signer as predecessor;
    - `now()` swaps height and timestamp;
    - emit before `ok()`;
    - status mapping inverted;
    - default `limit` set to 100;
    - `revoke_key` passes the signer;
    - `push_request` keyed by `count+1`;
    - two maps sharing a prefix;
    - `request_view` sets `requested_at_block` from `timestamp_ns`.
- **`tools/scripts/wasm-surface.sh`:** the exports (SH-11) and imports (SH-12)
  of the `cargo near build non-reproducible-wasm` output, in the near-unit job
  (M3). It is repeated on the reproducible wasm in the sandbox job (M6; OQ-2
  is answered upstream).
- **`sandbox/`** (standalone, near-workspaces, same lockfile rule):
  - **Tests:** RT-*, SH-9, SH-10, RES-1..3.
  - **Contracts in `res/`:** `relay/`, `selfacct/` and `spoofer/`, about 30
    lines each.
- **`deploy-checks/check_deployment.sh <net>`:** DEP-1, VER-2, VER-3. These
  need an archival RPC and an indexer (DEP-1.4, VER-3).

---

## 10. Correspondence and staleness

**The chain.** Each link is checked mechanically except where marked.

| Link | Checked by |
|---|---|
| requirements ↔ code facts | C-2, C-3, C-5, C-6 |
| Prolog semantics ↔ real core ↔ `spec.rs` | MC-2 |
| `spec.rs` ↔ real core | Kani (bounded); VC (unbounded, M5 path A) |
| *Verus model ↔ `spec.rs` (path B only)* | shared IDs plus paired review (not mechanical) |
| real core ↔ shell | ST-2..4, SH-* (host); RT-TRACE (wasm) |
| shell ↔ on-chain code | RT-CODEHASH, DEP-1, VER-2, VER-3 |
| proof ↔ signing keys | VER-8 |

**Vacuity guards:** TR-5, covers, both mutant suites (including the
must-survive pair), the Kani and Verus canaries, and the `MemStore`
satisfiability witness (path A).

**Staleness:**
- **Every PR:** `check-pin.sh near-approval` checks gitlink = `pinned_commit`
  and recomputes `[source_hashes]`. Every model, spec and harness file header
  carries the upstream path, pin, sha256 of the mirrored file, the items it
  covers, its simplifications and its trusted items, following
  `sanitizer.rs`. `check-pin.sh` also greps that `cfg(feature = "borsh")` in
  the core gates only `use` and `derive` items (ASM-COMPILE).
- **Pin bump:** a changed file flips every property whose `depends_on` lists
  it to `stale`. The `depends_on` lists in `status.toml` are authoritative. In
  outline:
  - `core/src/lib.rs` → TX, INV, LEM, HIST, TR, RD, ROB, ST;
  - `core/src/tests.rs` → the planning claims about upstream tests and mutants
    (F-14);
  - `contract/src/lib.rs` → ST-3..6, SH, RES, RT;
  - `Cargo.lock` → ST-4..6, SH, RES, RT, and the ASM-SDK/STORE/LIMITS checks.

  The bump PR re-runs everything. Path B statuses return only after re-review
  against the diff.
- **Weekly:** diff the pin against trust-framework `main` for
  `contracts/approval/**` and open an issue listing affected IDs.
- `ghost::Sparse` carries the sha256 of `contract/src/lib.rs`, and
  `check-pin.sh` fails if it's stale.

---

## 11. Layout

```text
formalver/
├── Cargo.toml          # exclude += near-approval/{source-mirror,kani,near-tests,sandbox}
│                       # (in-tree path deps otherwise become members and pull borsh);
│                       # members += near-approval/verus at M5
├── .gitmodules         # + projects/near-approval/source-mirror (shallow)
├── .github/workflows/near-approval.yml
├── tools/
│   ├── versions.env    # KANI, TLA2TOOLS, APALACHE, VERUS, SCRYER, CARGO_NEAR, NEAR_SANDBOX, RUST_TOOLCHAIN
│   └── scripts/        # run-prolog.sh (fixed), run-verus.sh (fixed), run-kani.sh, run-tla.sh,
│                       # check-pin.sh, check-status.sh, check-hygiene.sh, wasm-surface.sh
└── projects/near-approval/
    ├── strategy.md  status.toml  wasm-surface.expected
    ├── source-mirror/                 # submodule → trust-framework @ pinned_commit
    ├── prolog/{requirements,model,verification,extracted,tests}/
    ├── conformance/traces/            # generated, checked in
    ├── kani/{src,tests,mutants,kani-stub}/
    ├── tla/{*.tla,*.cfg,mutants}/     # §17; build/ is generated
    ├── verus/                         # M5: twin + erasure check + REWRITES.toml (A) or machine (B);
    │                                  # TRUSTED.toml; canary/
    ├── near-tests/{src,tests,mutants}/
    ├── sandbox/{res,tests}/
    └── deploy-checks/check_deployment.sh
```

## 12. `status.toml` conventions

The ironclaw format is kept. **Status values** are unchanged:
`unverified | in-progress | verified | verified-with-assumptions | stale`.

**Optional property keys:**

| Key | Meaning |
|---|---|
| `id` | catalogue ID |
| `evidence` | the target evidence: `proof | model-proof | bounded-proof | model-check | test | review | check` |
| `layer` | primary technique: `kani | plain | verus | prolog | tla | unit | difftest | sandbox | wasm-check | review | deploy-check` |
| `cross` | cross-check techniques |
| `harness` | the `// PROP:` tag must appear in it before the property leaves `unverified` |
| `depends_on` | paths relative to `upstream_path` |
| `assumptions` | ASM IDs |
| `blocked_by` | OQ ID |

**Allowed evidence per layer:**
- `kani` → `bounded-proof`
- `plain` → `test`
- `verus` → `proof` or `model-proof`
- `prolog` → `check`, `model-check` or `test`
- `tla` → `model-check` (TLC) or `bounded-proof` (Apalache inductive step)
- `unit`, `difftest` → `test`
- `sandbox` → `test` or `check`
- `wasm-check`, `deploy-check` → `check`
- `review` → `review`

**Status ceilings:**
- A Kani result is at most `verified-with-assumptions` with
  `evidence = "bounded-proof"`.
- Only path-A Verus yields `evidence = "proof"`. Its status stays
  `verified-with-assumptions` while `TRUSTED.toml` or the property's
  `assumptions` are non-empty, per `docs/architecture.md`.
- No K or V property leaves `unverified` without `[review] spec_reviewer`.

**Tables:**
- `[tools]`
- `[source_hashes]`
- `[assumptions.<ID>]` with `statement`, `level`, `checked_by`, `status`
- `[deployment.<net>]` with `contract_account`, `expected_code_hash` (base58)
  and `wasm_sha256` (hex)
- `[review]` with `spec_reviewer` and `spec_reviewed_at`

---

## 13. Milestones

Effort is in engineer-days, for someone with Kani and Verus experience. M1 and
M3 run in parallel. Each milestone ends by updating the statuses it lists.

| # | Deliverable | Acceptance | Effort |
|---|---|---|---|
| **M0** | Bootstrap and gates | • **OQ-7 resolved:** a deploy key or token lets the `pin` job check out the private submodule. <br>• Submodule at the provisional pin, `[source_hashes]` filled. <br>• Root `exclude` added; a clone without submodules still builds ironclaw. <br>• F-10 fixes: `run-prolog.sh` runs `-g "(catch(run_tests,E,(write(E),nl,halt(2))) -> halt(0) ; halt(1))" </dev/null` without `\|\| true` and exits non-zero if any file fails; `run-verus.sh` passes `--cfg 'feature="verus"'` and enforces the floor; `check-pin.sh` works and reports the ironclaw drift (OQ-6 decided). <br>• `tools/versions.env` pins every tool and `RUST_TOOLCHAIN`. CI skeleton green. <br>• **F-13 gate:** `cargo test -p approval-contract` passes, and `cargo near build non-reproducible-wasm` with `RUST_TOOLCHAIN` produces a wasm that deploys to the pinned near-sandbox and answers `get_owner` after `new`. <br>• OQ-1..5 raised upstream; OQ-3 answered. | 1–2 |
| **M1** | Kani step, raw, read and BMC harnesses on the real core | • Plain mode passes in CI. <br>• Under Kani (unwinding assertions on), `h_init`, `h_step_*`, `h_raw_*`, `h_read`, `h_bmc_from_init` pass and `h_canary` fails, with every cover in §6.2 satisfied. <br>• Each harness takes < 20 min, or the §6.3 ladder is applied and recorded. <br>• Every §6.4 mutant assigned to an M1 harness is killed, and the 2 equivalent ones survive. <br>• Every K property has a PROP tag. <br>• Spec reviewer sign-off recorded. <br>• **Statuses:** TX, INV-1..10, LEM, HIST, TR-1..4, TR-6, RD-1/2/5/7 and ROB-1 become `verified-with-assumptions` (`bounded-proof`). | 4–6 |
| **M1.5** | TLA+ model refined by Kani (§17) | • `run-tla.sh near-approval safety liveness apalache trace mutants` passes: TLA-SAFE, TLA-IND, TLA-LIVE-1/2, witnesses, REF-5, every spec mutant killed. <br>• `h_ref_*` pass under Kani with covers satisfied. <br>• **Statuses:** TLA-*, REF-1..5 updated. | 2–3 |
| **M2** | Ghost-store harnesses | • `h_page_arith`, `h_proto_*`, `h_count_*`, `h_refine_*`, `h_store_laws_*` and `h_action_len` pass, with their covers satisfied. <br>• Every §6.4 mutant except the must-survive pair is killed by Kani and by plain mode. <br>• RD-4 plain check passes (log ≤ 250; `l ∈ {1, 2, 99, 100, 101, 200}`). <br>• **Statuses:** INV-0, TR-5, RD-3, RD-4, RD-6, ROB-2..4 and ST-1..3 updated. | 1–2 |
| **M3** | near-sdk shell and store | • `store_diff.rs` (10k × 50, with reload) passes. <br>• `shell.rs` passes. <br>• All shell mutants are killed. <br>• Golden Borsh bytes are committed. <br>• `wasm-surface.sh` diff on the non-reproducible build is clean. <br>• `api_facts.pl` generated. <br>• **Statuses:** ST-4..6, SH-1..8, SH-11, SH-12, RES-1 and RES-2 updated. | 2–3 |
| **M4** | Prolog | • `run-prolog.sh near-approval` exits 0 (strict). <br>• C-1..10 pass, or each failure has a recorded decision (C-4/F-8). <br>• MC-1 and MC-1s meet the §5.11 criteria, each in < 5 min, and `mc1_state_floor` is recorded. <br>• Traces checked in; MC-2 replay passes on the core and `spec.rs`. <br>• `code_facts.pl` regeneration shows no diff. <br>• **Statuses:** C-1..10, MC-1 and MC-2 updated. | 3–4 |
| **M5** | Verus (2-day spike, then path A or B) | • Spike decision recorded. <br>• `verus/canary/false_lemma.rs` fails. <br>• **Path A:** the twin verifies with refinement `ensures` for every public core fn and `MemStore`; the erasure check passes; every `REWRITES.toml` entry has a passing Kani equivalence harness. Core properties become `verified-with-assumptions` / `proof`, with trusted ASM-IDENT, ASM-STRLEN and listed std specs. <br>• **Path B:** all lemmas in §7 are proved under the hygiene gate; spec mutants each break a lemma. Status becomes `verified-with-assumptions` / `model-proof` + ASM-MODEL. | 9–15 |
| **M6** | Sandbox | Needed F-12, resolved upstream (R-8). <br>• RT-* (including RT-TRACE and RT-BATCH), SH-9 and SH-10 pass on a pinned neard with the reproducible wasm. <br>• `wasm-surface.sh` diff on the reproducible build is clean. <br>• RES measured, with thresholds and both hashes recorded. <br>• RT-METATX outcome documented. <br>• `[assumptions]` statuses filled from observations. <br>• `cargo expand` review of SH-9/RD-6 signed off. <br>• **Statuses:** RT-*, SH-9, SH-10 and RES-3 updated. | 3–5 |
| **M7** | Deployment and automation | • A testnet deployment with the DEP-1 lock batch and at least one agent key and one approver key registered; `check_deployment.sh` passes; `[deployment.testnet]` filled. <br>• `verifier_rules.pl` encodes VER-1..8; RT-SPOOF and a VER-8 check against the testnet proof demonstrate them. <br>• Every CI job live; pin-bump procedure documented; `docs/architecture.md` gains the Kani, shell and deployment layers. <br>• **Statuses:** DEP-1 and VER-1..8 updated. | 2 |

**Total: M0–M7 about 25–39 days.** Kani precedes Verus because it checks the
deployed code itself and buys the most assurance per day.

## 14. CI (`.github/workflows/near-approval.yml`)

| Job | Trigger | Fails on |
|---|---|---|
| `pin` | PR, push | gitlink ≠ pin; hash drift; release profile without `overflow-checks = true` or borsh feature gating (ASM-COMPILE). Every other job depends on it. |
| `plain` | PR, push | any failure; drift in generated `code_facts.pl` |
| `kani` | PR touching near-approval; nightly (60 min timeout, matrix by harness group) | any failure; any unsatisfied cover; `h_canary` passing |
| `mutants` | weekly | a core or shell mutant survives; an equivalent mutant is killed |
| `tla` | PR, push | any §17.3 check failing; a witness or the unfair liveness run passing; a spec mutant surviving |
| `prolog` | PR, push | any failure; drift in `conformance/traces`; MC-1/MC-1s state count below the floor |
| `verus` | PR, push (from M5) | any error; count below the floor; canary verifies; a spec mutant verifies; hygiene |
| `near-unit` | PR, push | any failure; lockfile version mismatch; export or import diff (non-reproducible build) |
| `sandbox` | nightly; submodule bump; manual (from M6) | any failure; export or import diff (reproducible build); threshold exceeded |
| `status-lint` | PR | a non-`unverified` ID without its artifact or PROP tag; `verified*` without a passing harness in this run; `evidence` not allowed for its `layer` (§12); a K/V property past `unverified` without spec sign-off |
| `upstream-watch` | weekly (`.github/workflows/upstream-watch.yml`) | none; opens an issue when a path in `tools/upstream-watch.toml` changed (near-proof-arena specs and challenges; the Nomicon pages the assumptions cite) |
| `deploy-check` | manual; weekly | any DEP or VER violation |

trust-framework is private, so CI needs a deploy key or fine-grained token for
the submodule (OQ-7, resolved in M0).

## 15. Risks

| Risk | Mitigation |
|---|---|
| Kani too slow at these bounds [conf: low on timing] | §6.3 ladder; per-op split; plain mode keeps CI useful |
| `assume(inv)` makes step proofs vacuous | Covers on every outcome; `h_raw_*` without the assumption; must-survive mutants |
| Spec bugs (ASM-SPEC) | Three independent semantics with replay; mutants; traceability; human spec sign-off |
| Runtime assumptions wrong (META, LIMITS, logs on failure) | Levelled assumptions; M6 tests; conditional statements |
| Upstream churn (the contract is new) | Provisional pin; per-file staleness; weekly watch |
| Point-in-time deployment checks miss a later key or code change | DEP-1 lock at deploy; VER-3 since `b₀`; VER-8 per proof; NEP-591 global-contract check |
| Verus can't handle the real core | M5 path B; Tier 1 and Tier 2 keep full value without M5 |
| Tool pins conflict (Verus rustc vs cargo-near rustc) | Path A adoption gate; the twin is the steady state |
| Everything except plain mode needs network access | CI-only jobs; plain mode works offline |

## 16. Open questions

1. **OQ-1:** Merge `claude/near-approval-contract-qin858` and re-pin to the
   merge commit.
2. **OQ-2 (F-12):** *Answered in `3426c92` (R-8).*
3. **OQ-3 (F-13):** *Answered in `3426c92`: upstream CI (R-9).*
4. **OQ-4 (F-4):** Keep `MAX_ACTION_LEN = 2048` behind the RES-2 test, or
   lower it?
5. **OQ-5 (F-6):** Reorder `revoke_key` to check before removing, or keep it
   documented?
6. **OQ-6 (F-10d):** Fix ironclaw's pin drift in the M0 PR, or scope
   `check-pin.sh` per project?
7. **OQ-7:** CI access to private trust-framework; runners with Docker (for
   reproducible builds) and an archival RPC (for VER-2/3).
8. **OQ-8:** Is separation by account id enough, or should the owner account
   be barred from holding agent or approver keys? MC-1 can flag it.
9. **OQ-9:** Admin events (F-8): *answered in `3426c92` (R-7); C-4 and the
   SH rows follow at M3 (F-15).*

---

## 17. TLA+ over every event sequence, refined by Kani (M1.5)

The Kani harnesses prove one step of the real core from any `Inv` state
within their bounds, plus a depth-6 BMC from `Init`. They say nothing
directly about **sequences**: liveness, or safety at a depth the BMC doesn't
reach. M1.5 adds a TLA+ model of the core that is checked over all event
sequences, and connects it to the code: every assumption the TLA+ model makes
about the Rust is a Kani obligation on the real core.

```text
real core  ⊑  tla.rs  ≡  ApprovalCore.tla  ⊨  Inv at every depth  (Apalache)
  Kani REF-1..4    REF-5 trace     ⊨  StepProps, witnesses  (TLC)
                   validation      ⊨  Live1 under fairness  (TLC)
```

### 17.1 The model (`tla/`)

| File | Contents |
|---|---|
| `ApprovalCore.tla` | The state machine. Variables `principals` (total over `Keys`, `reg = FALSE` for absent keys; with registration id `rid`), `requests` (with agent, approver and rejecter registration ids), `log`, `regs` (the registration counter `G`) and `revoked` (the revocation map's keys): the image of a store under the abstraction map α. Ghost `ghost` (per request: was the agent registration unbroken at the decision, was the decider an Approver) for TR-1. One error operator per entry point (`AddErr`, `RevokeErr`, `RequestErr`, `ApproveErr`, `RejectErr`; the last two share `DecideErr`, the core's `decidable_request`), the first failing guard in the core's order, and one action enabled exactly when it is `"Ok"`. A rejected call is a stutter (TX-0). `GuardOrder` lists each entry point's errors in order. |
| `ApprovalProps.tla` | `TypeOK` (as predicates), INV-3..9, INV-11..16 (registration ids, revocations, one decision per request), INV-5/6 for rejections, LEM-1/2, `Provenance` (TR-1), `RidLive` (the `active_from` check agrees with the registration ids), `Approvable` (TLA-LIVE-2, approve and reject): together `Inv`. Action properties HIST-1/2/3/7/8/9/10 (`StepProperty`). `Witness_*` invariants that must be violated (TR-5). |
| `MC_Safety.{tla,cfg}` | TLC: accounts `{o, a1, a2}`, keys `{k1, k2}`, payloads `{x, y}` plus `Empty` and `TooLong`, `MaxPending = 2` (scaled), at most 3 requests. Symmetry on accounts and keys; a `VIEW` replaces registration ids by their rank among the ids the state refers to. The core only copies ids and the properties compare them only for order and equality, so this is a bisimulation quotient and the unbounded add/revoke cycles stay finite. |
| `MC_Liveness.{tla,cfg}`, `MC_Liveness_Unfair.cfg` | TLC: `Live1` under weak fairness of approvers; bounds inside the actions (`MaxReg` registrations), no symmetry or view. Without fairness `Live1` must fail. |
| `MC_Apalache.tla` | Apalache: `Init ⇒ Inv`, `Inv ∧ Next ⇒ Inv'` and `Inv ∧ Next ⇒ StepProps` from any state with at most 3 requests, all integers symbolic, `MaxPending = 2` (scaled so the cap binds; Kani covers the real 16). |
| `TraceCheck.{tla,cfg}` | REF-5: replays traces of the real core (`build/TraceData.tla`, generated). |
| `mutants/*.patch` | Spec mutants; each must be killed by trace, apalache or liveness. |

**Abstractions**, each discharged in §17.2:
- Accounts and keys are small symmetric sets (ASM-IDENT parametricity).
- Actions are four classes: two distinct storable payloads, `Empty` and
  `TooLong`. The core reads an action only through `is_empty`, `len` and
  `==`.
- Block times are dropped: the core stores them and never branches on them.
- Counters are unbounded naturals: `LogFull` fires only at `u64::MAX`
  (LEM-3, ROB-1, ROB-2).

### 17.2 The refinement link

| # | TLA+ assumption about the Rust | Discharged by |
|---|---|---|
| A1 | **Guard exactness:** the core's error is the TLA+ error operator's, so `Ok` exactly when the action is enabled | **REF-1**, `h_ref_*` (Kani) |
| A2 | **Effect exactness:** on `Ok`, α(post) is the action's post-state | **REF-2**, `h_ref_*` |
| A3 | **Rejected calls stutter:** on `Err`, α(post) = α(pre) | **REF-3**, `h_ref_*`; also TX-0 |
| A4 | Small symmetric account and key sets suffice | ASM-IDENT (opaque `Acct`/`Key` in the harness build) |
| A5 | Four payload classes suffice | REF-1/2 over the 2-byte alphabet and `""` (`h_ref_*`), and `h_ref_toolong` for `TooLong` |
| A6 | Counters don't overflow in any reachable state | LEM-3, ROB-1; ROB-2 (M2) |
| A7 | Time is irrelevant to control flow and α | **REF-4**: `tla.rs` never reads a `BlockTime`, so REF-1/2 hold for every time |
| A8 | Each successful call is one atomic step | ASM-SEQ, ASM-ATOMIC (runtime; not provable in Kani) |
| — | `tla.rs` transcribes `ApprovalCore.tla` | **REF-5**: random core traces (60 × 80 calls over `MemStore`) are checked against `tla.rs` on every step, then TLC must accept each as a behaviour of `ApprovalCore`. The generator re-registers revoked keys so revival attempts occur (≥ 5 required), and requires ≥ 20 successful rejections and revocations. |

`kani/src/tla.rs` holds α, the error operators and `next`. The `h_ref_*`
harnesses reuse the `h_step_*` state and operation generators with only the
refinement checks (`PART_REF`), so the existing harnesses keep their cost.
Plain mode runs the refinement checks inside every step test.

### 17.3 What is checked

| ID | Property | Check | Bound |
|---|---|---|---|
| TLA-SAFE | `Inv` and `StepProperty` (HIST-1/2/3/7/8, TR-2, TR-3 as `□(Void ⇒ □Void)`) in every reachable state and step | TLC, `MC_Safety` | ≤ 3 requests, 3 accounts, 2 keys, `MaxPending = 2`, any number of add/revoke |
| TLA-IND | `Inv` is inductive, and every step from an `Inv` state satisfies `StepProps`: both hold at every depth | Apalache, `MC_Apalache` | arrays ≤ 3 before the step; integers unbounded; `MaxPending = 2` |
| TLA-LIVE-1 | `<>[]Eligible(i) ⇒ □(Pending(i) ⇒ ◇¬Pending(i))` under `WF(ApproveReq(i))`: if an eligible approver eventually always exists and approvers are fair, no request stays pending (it ends approved, rejected or void; fairness is on approval only, so progress never relies on a rejection) | TLC, `MC_Liveness` (must fail without fairness) | ≤ 2 requests, 2 keys, ≤ 4 registrations |
| TLA-LIVE-2 | `Approvable`: a pending request is approvable and rejectable by every Approver key of another account | in `Inv` (TLC and Apalache) | as above |
| TLA-WIT | Approved, rejected, void, revival-attempt and pending-cap states are reachable | TLC, inverted invariants | as TLA-SAFE |
| REF-1..4 | §17.2 | Kani `h_ref_*`, plain mode | Kani step bounds (§6.3) |
| REF-5 | `.tla` ≡ `tla.rs` ≡ core on traces | plain + TLC | 60 traces × 80 calls |

`Live1` needs its premise. Weak fairness alone is not enough when the owner
can revoke every approver key: then no approval is ever enabled, and that is
the contract working as designed, not a liveness bug. Strong fairness would
not help either, for the same reason.

**What this does not give.** TLC and Apalache use small constants, and Kani
proves REF only within its step bounds. The chain is "bounded model plus
parametricity" (ASM-IDENT, ASM-MODEL), not an unbounded proof; M5 (Verus)
removes the small-scope step for the code, not for the TLA+ constants.

### 17.4 Running and CI

`tools/scripts/run-tla.sh near-approval [safety|liveness|apalache|trace|mutants]`.
`tools/scripts/get-tla-tools.sh` fetches the jar and Apalache pinned in
`tools/versions.env`, sha256-checked. CI job `tla` runs all checks plus the
mutants on PRs; the `kani` job's matrix adds the `h_ref_*` family.

### 17.5 Interaction with the Prolog model (M4)

Prolog stays the **independent** semantics, written from the requirements
(ASM-SPEC); TLA+ mirrors the code. M4 is designed against these interfaces:

| Link | Check | What it catches |
|---|---|---|
| P1 guard table | **C-2t:** TLA+ `GuardOrder` = `guard/4` order = `code_precedence/2` | a reordered or missing guard, before TLC runs |
| P2 constants | C-5 extended to the `.cfg` files; scaled values tagged `scaled`, and C-10 warns on a `verified*` property backed only by scaled runs | a model checked with the wrong constants |
| P3 graph equivalence | **MC-3:** Prolog `step/4` and TLC export the full labelled reachable graph for one universe (TLC through a `lastOp` history variable kept in the fingerprint and projected out by the exporter); state and edge sets must be equal | any divergence between requirements-derived and code-derived semantics, at the exact `(state, op)` |
| P4 shared traces | MC-2 uses REF-5's trace format: every source (`gen_traces.pl`, `trace.rs`) is replayed by every model (core, `spec.rs`, `tla.rs`, `step/4`, `TraceCheck`) | long-trace divergence that P3's small universe misses |

With MC-3 in place, MC-1's own invariant checks repeat TLC's on an equal
graph, so MC-1 shrinks to coverage (every error, an approved and a void
state). The new IDs (TLA-*, REF-*, C-2t, MC-3) enter `traceability.pl` with
layers `tla`, `kani` and `prolog`, so C-7 and C-9 cover them.

### 17.6 Following trust-framework PR #15

The model was first written at pin `5736251` and moved with the pin to
`3426c92` (PR #15). What changed:

| #15 change | TLA+ | `tla.rs` / Kani |
|---|---|---|
| `reject` (Approver key, not the agent's account) frees the pending slot; `AlreadyRejected` after `AlreadyApproved`, in `approve` too; status `Rejected` | `Reject` action, `RejectErr`, `DecideErr`; request fields `rj`, `racct`, `rkey`, `rrid`; HIST-2 covers rejections (HIST-9); `Live1` ends in approved, rejected or void | `Op::Rej`, `h_ref_reject` |
| registration ids from `registration_count`, recorded in principals, requests and decisions; `add_principal` returns `LogFull` at `u64::MAX` | `regs`, `rid`, `arid`, `rrid`; INV-11/14/15/16. `LogFull` stays unreachable (A6; under `Inv` the harness counter is ≤ 6) | α gains the ids and `G` |
| `revoke_key` records `(registration_id, revoked_at)` | `revoked`, a set (times stay abstract, A7); INV-12, HIST-10 | α gains the revocation keys; REF-4 still holds |
| add and revoke emit events | none (events are shell, not core) | none |

The registration ids replace the old `epoch` ghost: a request's registration
is unbroken exactly when its key still holds the id the request recorded,
because ids are never reused. `RidLive` states that the core's `active_from`
check decides the same thing, now over real state rather than a ghost.
`live_agent_registration` is unchanged, so TR-3 and its mutant carry over.
