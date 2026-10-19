# NEAR Approval Contract Formal Verification Strategy

## Target

[`difflabai/trust-framework`](https://github.com/difflabai/trust-framework)
`contracts/approval/`: a NEAR contract where an agent requests an action with
its registered key (event `approval_requested`), an approver approves it with
its own key (event `action_approved`), and approval proofs are publicly
readable per request or as a paged log.

| | |
|---|---|
| Pinned commit | `8635ca7b8b1d64bb226eb0b3b3a35779fcbf461b`, trust-framework `main` (2026-10-14). PR #15 (adds `reject`, registration ids and revocation times, key events) was squash-merged as `cbb16dd`; the later commits on `main` touch only CI and 3 lines of `README.md`, so `contracts/approval/` code is identical to the PR #15 head `3426c92` that every model and harness was written against. Previous pins: `3426c92`, `5736251`. |
| Crates | `approval-core` (`core/src/lib.rs`, 749 lines incl. docs). A dependency-free state machine, generic over account `A` and key `K`, holding *all* authorization and transition logic. `approval-contract` (`contract/src/lib.rs`, 976 lines incl. tests). A near-sdk 5.29 shell: env → `Caller`, `Store` over `LookupMap`, NEP-297 events, JSON views. |
| In the TCB via `Cargo.lock` | near-sdk 5.29.1, near-sdk-macros 5.29.1, near-sdk-core 4.2.3, near-sdk-env 0.1.6, near-account-id 2.6.0, near-sys 0.2.14, borsh 1.8.1, serde_json 1.0.151 |
| Mirror | git submodule `projects/near-approval/source-mirror` (same pattern as ironclaw) |

The split is deliberate. Every decision is in `approval-core`, which has no
dependencies, so Kani and Verus can target **the deployed logic itself**
rather than a model of it. The shell is thin enough to cover with tests,
review and wasm inspection.

**Status (2026-10-19, formalver main `519528c`, pin `081a3a6`).** Every
milestone except M5 is built and green in CI. What keeps the contract short
of "fully verified" is the spec sign-off, the testnet deployment and the
unmechanised steps listed under "Next".

| Layer | Milestone | State |
|---|---|---|
| Bootstrap, pin job, CI | M0 | Done. CI runs on self-hosted macOS runners (`vars.CI_RUNNER`), path-aware on PRs (`ci-areas.sh`). |
| Kani on the real core | M1 | `h_init`, `h_step_*` (5 parts each), `h_raw_*`, `h_read`, `h_bmc_*`, `h_ref_*`, `h_cut_*` green; `h_canary` fails; every cover satisfied; core mutants killed and the 2 equivalent ones survive, in plain mode and under Kani (§6). |
| Kani bounds | §6.3 | CUT-1 (`h_cut_*`), U-1 (`kani-loops.py`, job `loops`). The size bound is closed by L2 (§18.6); CUT-2 (`kani/CUTOFF.md`) stays on paper. |
| TLA+ refined by Kani | M1.5 | TLC safety and liveness, Apalache inductive step, witnesses, REF-1..5, 15 spec mutants killed (§17). TLC pinned to 1.7.4. |
| Lean | M1.6 | `Inv`, the step properties and TR-1/2/3 proved for states and runs of every size; MC-4 and REF-5L tie it to TLC and the core (§18). |
| Lean L2 (oracle store) | §18.6 | ST-8, LINK and LEAN-DELTA: the core steps like the model at every store size. ST-7 and RT-TIME added. LINK's domain is mechanised (§18.6.1): LEAN-COVER and K-LINK-T prove its 14,310 views cover every view; ST-8W runs ST-8 over enough accounts for any footprint. |
| Prolog requirements oracle | M4 | C-1..C-10 and C-2t pass; MC-1 51,568 states; MC-2 agrees both ways; MC-3 (Prolog graph = TLC graph) nightly (§8). |
| Ghost-store harnesses | M2 | `h_page_arith`, `h_proto_*`, `h_count_*`, `h_refine_*`, `h_store_laws_*`, `h_oracle_*`, `h_action_len(_multi)` green; nightly mutants job. |
| Shell and store | M3 | `near-tests/` (`store_diff.rs`, `shell.rs`, `ident.rs`, golden Borsh), shell mutants killed, `wasm-surface.sh` clean, `api_facts.pl` generated; job `near-unit`. |
| Verus | M5 | Not started. Path B superseded by §18; path A spike is a pending decision. |
| Sandbox | M6 | RT-*, RT-TRACE, SH-9/10, RES-1, RES-3 and the reproducible-wasm surface diff pass on near-sandbox 2.13.4; job `sandbox`. Assumptions move to `in-progress` as their tests land. |
| Deployment | M7 | `check_deployment.sh` and `verifier_rules.pl` pass against a sandbox deployment; job `deploy-check`. No testnet deployment. |

**Statuses.** No K or V property has left `in-progress`: §12 requires a
named spec reviewer (`[review] spec_reviewer`), and none is recorded. The
`status-lint` job enforces this. The proofs above pass in CI;
`status.toml` will say so once that sign-off lands.

**Next.** Decisions: the spec reviewer (also signs off the `cargo expand`
review of SH-9/RD-6), the testnet deployment for M7 (needs an archival
RPC for VER-2/3), OQ-4, OQ-5, OQ-8, the Verus path A spike, and what (if
anything) to submit to near-proof-arena. Buildable without a decision:
narrowing ASM-TLA-SCOPE for liveness. The ASM-IDENT/LINK domain argument is
mechanised (§18.6.1); what it leaves trusted is ASM-NU. ASM-FINAL, ASM-TOOLS, ASM-OWNER and ASM-DISPLAY stay trusted.

*Planning history.* The plan was written before any tool could be installed;
the `[conf: …]` tags in this document date from then. Against the original
pin it ran the core's 21 tests and 29 hand-seeded mutants (27 killed, 2
equivalent, F-14) offline.

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
| **3. Unbounded** | M1.6, M5 | 12–19 days | Lean (M1.6, §18): the model's safety at every size. Verus on the real core (M5), removing the small-scope step for the code. If the spike fails, §18 is the unbounded result, as model-proofs. |

Recommendation: do Tier 1 now. Tier 2 before any mainnet deployment. Tier 3
only if "formally verified" will be claimed externally.

---

## 2. Scope

**In scope**
- **`approval-core`:**
  - Functions: `add_principal`, `revoke_key`, `authenticate` (private,
    covered through its callers), `live_agent_registration` (private),
    `request_action`, `approve`, `reject`, `request_status`, `status_of`,
    `proof_revocations`, `approval`, `approvals`, `ActionRequest::proof`.
  - `ApprovalError`: all 17 variants and their messages.
  - Constants: `MAX_ACTION_LEN`, `MAX_PENDING_PER_KEY`, `DEFAULT_PAGE_SIZE`,
    `MAX_PAGE_SIZE`.
  - The `Store` trait contract, and `MemStore` as the harness store.
- **`approval-contract`:**
  - The `Store` impl.
  - `caller()`, `now()` and `ok()`.
  - All 16 `#[near]` methods (13 before PR #15).
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
- Features the contract deliberately lacks: expiry, M-of-N, ownership
  transfer, upgrade. (Rejection and key events were added in PR #15.)
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
| ASM-TIME | `block_height` and `block_timestamp` never decrease across receipts on one account. | med (height high, timestamp med-high) | RT-TIME (sampled). Used only by INV-10, TR-4 |
| ASM-FINAL | State at finality `final` is never reverted. | high | none |
| ASM-CODE | Code changes only through `DeployContract` or `UseGlobalContract` on `C` (both need a full-access key on `C`). If `C` uses a NEP-591 global contract referenced by account id, it also changes through `DeployGlobalContract` by that account. `DeleteAccount` erases state, and a recreated account starts empty. | med | RT-RESET, DEP-1 |
| ASM-SDK | `#[init]` panics if state exists. `#[private]` requires predecessor = current account. Non-payable change methods reject deposits. `&self` methods never write. Only `#[near]` impl methods are exported. `PanicOnDefault` blocks default init. | high | SH-9, SH-10, SH-11, `cargo expand` review |
| ASM-STORE | `store::LookupMap` is a map keyed by `prefix ‖ borsh(key)`. Its writes are flushed when the contract struct drops after `state_write`. | high (semantics); med (flush) | ST-4, ST-5, ST-6 |
| ASM-IDENT | `PartialEq` on `AccountId` and `PublicKey` is an equivalence matching equality of their Borsh bytes, and `clone` preserves it. The core uses `A`/`K` only via `Clone` and `PartialEq` (`#![forbid(unsafe_code)]`, no `Ord`/`Hash`). This **parametricity** justifies small identities in harnesses: any footprint (at most 8 accounts, 4 keys) maps injectively into the harness identities (ST-8W, §18.6.1), so which identities the code compares needs no argument. | high | Harnesses instantiate `A`/`K` with opaque newtypes (`Acct(u8)`, `Key(u8)`) implementing only `Clone`, `PartialEq`, `Debug` and a hand-written `kani::Arbitrary`, so any new trait bound upstream breaks the harness build. ST-7 checks the equality half on the locked near-sdk |
| ASM-STAKE | The account must hold `storage_usage × 10^19` yocto, with about 40 bytes of overhead per record. | med (rule high, constants med-high) | RES-1 |
| ASM-LIMITS | `max_total_log_length` 16384 B. 100 logs. 4 MiB return data. 300 TGas per call. The view gas cap is set per node. | med | RES-2, RES-3 |
| ASM-META | NEP-366: the inner receipt has signer = relayer, so relayed calls fail `IndirectCall`. The same holds for NEP-518 eth-implicit accounts. | med | RT-METATX |
| ASM-FCKEY | Function-call keys restrict receiver and methods, can't attach a deposit, and have an allowance. Function-call keys can't add keys. | high | RT-FCKEY |
| ASM-COMPILE | rustc/LLVM/wasm-opt preserve core semantics from host to wasm32. The release profile keeps `overflow-checks = true`. The only on-chain `usize` use is `action.len() > MAX_ACTION_LEN`; every value is far below 2³², so host and wasm32 agree (`MemStore` is off-chain). `cfg(feature = "borsh")` gates only `use` and `derive` items, so Kani (borsh off) and the wasm (borsh on) compile the same logic. | n/a | RT-CODEHASH, RT-TRACE, `check-pin.sh` grep |
| ASM-MODEL | *Until M5 (code-level Verus):* a core step on a state larger than the Kani bound behaves like one within it (the §6.3 small-scope argument). | med | Plain-mode random traces of ≤200 steps, MC-2. Discharged at every store size by the L2 chain (§18.6): ST-8 (code = `expect`/`protocol`), LINK (`expect`/`protocol` = Lean `cstep` on every footprint view of a finite domain), LEAN-DELTA (`cstep` = the model's step). LINK's domain covers every view by LEAN-COVER and K-LINK-T (§18.6.1). What stays trusted is ASM-IDENT (parametricity), ASM-NU and ASM-LEAN-TLA. Removed by M5 path A. |
| ASM-SPEC | The specs (`spec.rs`, Verus, Prolog) state the intended behaviour. | n/a | Independent authorship, signed off by a **named human who did not write `approval-core`** (`[review] spec_reviewer`), required before any K/V property is `verified*`. Also traceability (C-7), mutants and three-way trace replay. |
| ASM-TOOLS | Kani (CBMC, unwinding assertions on), Verus with Z3, and scryer-prolog are sound at the pinned versions. | n/a | `tools/versions.env`, the canary lemma must fail, mutants must be caught |
| ASM-OWNER | The owner registers keys honestly. It could otherwise register two accounts it controls and approve anything. | policy | DEP-1 (multisig/DAO), VER-4 |
| ASM-DEPLOY | The deployed code is the reproducible build of the pin, locked at deploy. | policy | DEP-1, VER-2, VER-3 |
| ASM-DISPLAY | The approver UI renders `action` faithfully (escaped). The approver's tx commits to the text (TX-5); this assumption covers only its rendering. | policy | none |
| ASM-STRLEN | *(M5 only.)* `String::len` is the UTF-8 byte length, and `is_empty ⇔ len = 0`. | high | none |
| ASM-NU | The Rust (`kani/src/norm.rs`) and Lean (`lean/ApprovalLean/Ident.lean`) transcriptions of LINK's class, representative and transport functions agree (§18.6.1). | high | LINK checks the representative half exactly: the views `link.rs` writes must equal Lean's `allCls.map rep` as a set. The class and transport tables are short, line-by-line, and every K-LINK-T and LEAN-COVER proof uses them. |

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
| F-10 | **formalver tooling defects:** <br>(a) `run-prolog.sh` ends with `\|\| true` and runs `-g "run_tests, halt."`; a failing `run_tests` falls through to the toplevel, which exits 0 at EOF. Failures never fail the script. <br>(b) `run-verus.sh` and the README's direct `verus` command omit `--cfg 'feature="verus"'`, so ironclaw's `cfg(feature="verus")` spec and proof modules are never compiled [conf: high]. The README's `./tools/get-z3.sh` lives under `source/` in the Verus repo. <br>(c) ironclaw proofs take their conclusion as a `requires`. <br>(d) ironclaw's gitlink `d313f44` ≠ recorded pin `34550ad`. <br>(e) No CI. | M0 fixed (a) and (e). (b) is still open in `run-verus.sh`; it matters from M5 or for ironclaw. (d): `check-pin.sh` is per project and CI runs it for near-approval only (OQ-6). Rule for this project: no proof assumes its conclusion. |
| F-15 | PR #15 changes the shell: a `reject` method, `action_rejected`, `key_added` and `key_revoked` events, `agent_key_revoked_at` / `approver_key_revoked_at` on proof views, `get_revocation`, and a `v` storage prefix for revocations. SH-4..SH-8, SH-10, SH-11 (export count: 16 at `main`, the row said 13), C-4, ST-5, RES-1 and requirement D11 ("no rejection") described the `5736251` shell. | **Done at M3** (2026-10-15): those rows, their `traceability.pl` and `status.toml` descriptions, and C-6's check describe the PR #15 shell; D11 reads "no upgrade, ownership transfer, expiry or threshold" and D17 covers rejection. |
| F-17 | near-sdk-core 4.2.3 (in the lockfile) accepts **ML-DSA-65** public keys (1952 bytes; nearcore 2.13, protocol 85). With ML-DSA-65 keys on both sides, the worst-case `action_approved` line is 18256 B, over the 16384 B limit: the core accepts the request, and that approver key can never approve it (the call fails with `TotalLogLengthExceeded`). One ML-DSA-65 key on either side still fits (≤ 15775 B), so another approver with a shorter key can. Storage per request also grows (`B_req` 4160 B; 16 pending = 0.666 NEAR). The README's worst case assumes secp256k1. | **Fixed upstream** in trust-framework PR #19 (pin `081a3a6`, 2026-10-17): `add_agent`/`add_approver` refuse ML-DSA-65 keys after the owner check. Checked by SH-13 (`f17_mldsa65_keys_are_refused`). Supporting them later needs a shorter event or a lower action limit (README). |
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
| **VM** | Verus spec machine (M5 path B; superseded by **L**) | `model-proof` (+ ASM-MODEL) |
| **L** | Lean theorems about the TLA+ model at every size (§18) | `model-proof` |
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
| TR-3 | **Durable revocation:** if the registration of `R[i].ak` under which `i` was made is removed while `R[i]` is pending, then `R[i]` is never approved in any extension. This holds even if the key is re-registered to the same account and role. | K (HIST-8 + `AgentRevoked` in `h_step_*`; `h_bmc_from_init_witness`: revoke, re-add, approve fails) / VC, PM (MC-1 must find **no** revival) |
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
| ST-8 | **Store protocol at any store size (K-ORACLE).** For a store of any size, keep only the entries a step reads, at their own keys and positions: every read answers as on the full store, so the step makes the same calls and returns the same result (the core reaches state only through `Store`, `#![forbid(unsafe_code)]`). `h_oracle_approve`/`h_oracle_reject` check `expect`/`protocol` on such restrictions: a `Sparse` with up to 3 requests and log slots at any `u64` positions, every field and counter free. Add, revoke and request read no request, so `h_proto_*` already covers them at every size. Removes the state bound from the code side of ASM-MODEL. ST-8W: the oracle harnesses draw accounts from 8 values (`src::Wide`), enough for every account term of a footprint, so a real footprint maps injectively into the harness identities (ASM-IDENT parametricity). | K |
| ST-4 | **The real store refines `MemStore`:** `ApprovalContract` and `MemStore<AccountId,PublicKey>` run random op sequences (10k × 50) through the core and through the public methods. **Before each step the contract is persisted and reloaded** (`state_write`, drop, `state_read`), so every step reads Borsh from cold storage. After every step, results and `α` are equal. | D (`store_diff.rs`) |
| ST-5 | Storage layout: prefixes `p` (principals), `r` (requests), `a` (approval log) and `v` (revocations) are pairwise distinct, none is a prefix of another, and none overlaps `STATE`. After every step of the random runs, the storage keys are **exactly** `STATE` and `p\|r\|a\|v ‖ borsh(key)` for the entries `α` lists. | D / R |
| ST-6 | Layout stability: golden Borsh bytes (key and value) for `STATE` (fresh and after a run) and one entry of each map: principals with an ed25519 and a secp256k1 key; requests pending, approved and rejected; a log entry; a revocation. A diff must be flagged as storage-breaking in the pin-bump PR. | D |
| ST-7 | Identity equality: `==` on near-sdk `AccountId` and `PublicKey` equals Borsh-byte equality, is reflexive and symmetric, and survives `clone` and a Borsh round trip (edge identities of every curve and length, 200k random pairs). Both types derive `PartialEq` over one field whose Borsh form is `u32 len ‖ bytes`, so this pins the derive against a hand-written impl or a new field in a dependency bump. | D |

### 5.7 Resource limits (RES)

| ID | Statement | Check |
|---|---|---|
| RES-1 | **Storage growth per operation** (bytes, each record counted with its key and the 40-byte per-record overhead): <br>• `Req` adds one record of ≤ `B_req` and rewrites one principal at the same size (`pend` is fixed-width); <br>• `Appr` grows one request by ≤ `B_ap` and adds a log record of `B_log`; <br>• `Rej` grows one request by ≤ `B_rej`; <br>• `Add` adds ≤ `B_p`; <br>• `Revoke` removes one principal and adds a revocation record of `B_v`; <br>• failures add nothing. <br>With 64-character accounts, 2048-byte actions and ed25519/secp256k1 keys (secp256k1 is the larger): `B_p` = 199, `B_req` = 2272, `B_ap` = 169, `B_log` = 57, `B_rej` = 161, `B_v` = 65. The bounds come from the Borsh layout and equal VMLogic's metering of the worst case (D), and the deltas are measured on-chain (S). With INV-9, the worst case an agent key can lock without an approver is 16 × `B_req` = 0.364 NEAR. ML-DSA-65 keys (`B_req` would be 4160) cannot be registered (SH-13). | D / S |
| RES-2 | Every accepted request is approvable within log limits: for `1 ≤ len(a) ≤ N`, the worst-case `approval_requested`, `action_approved` and `action_rejected` lines are each ≤ 16384 B. The worst case: 64-character accounts, ed25519 or secp256k1 keys, 2048 control bytes (each escaped to `\u00XX`), `u64::MAX` times and 20-digit ids; the longest line is `action_approved` at 13197 B (F-4). ML-DSA-65 keys on both sides would reach 18256 B (F-17); the contract refuses them at registration (SH-13), so ed25519 and secp256k1 are every key type. | D (explicit-limit unit test) / S |
| RES-3 | `get_approvals(0,100)` over 100 maximum-size, fully escaped proofs stays under the view gas cap and the 4 MiB return limit (estimate about 1.3 MB). *Measured (M6):* about 1.30 MB (1,299,658-1,299,659 B; the count varies by a byte between runs); about 88.3-88.4 TGas when called as a transaction. | S |

### 5.8 Contract shell (SH)

| ID | Statement | Check |
|---|---|---|
| SH-1 | **Env mapping:** `caller() = ⟨predecessor, signer, signer_pk⟩` and `now() = ⟨block_height, block_timestamp⟩`, probed with pairwise-distinct context values. `add_agent` passes `Agent`, `add_approver` passes `Approver`. All three owner methods pass the **predecessor**: a DAO owner works, and an owner's signature relayed by another contract fails. | D (upstream tests cover part) / R |
| SH-2 | One core transition per change call, with no other writes (`α` compared around each public call). | D |
| SH-3 | **Exact errors:** a core `Err(e)` panics with exactly `e.as_str()`, compared exactly via `catch_unwind` after extracting `panic_msg` from the mocked runtime's payload (payload format recorded at M3), and nothing is logged. On-chain the failure message is `"Smart contract panicked: " ‖ as_str` [conf: high on the prefix]. | D, S |
| SH-4 | `approval_requested` is exactly one log line, `EVENT_JSON:{"standard":"trust_approval","version":"1.0.0","event":"approval_requested","data":RequestView(r)}`, with `status: "pending"`. The method returns `r.id`. The emit happens only after the core returned `Ok`. The only failures after it are gas exhaustion and `LackBalanceForState` (ASM-ATOMIC, VER-1). | D / R |
| SH-5 | `action_approved` is exactly one line. Its `data` = the return value = `get_approval(i)` right after the call, with `agent_key_revoked_at` and `approver_key_revoked_at` both `null`. Later `get_approval(i)` differs from it **only** in those two fields, which report `proof_revocations` (RD-8): the `{block, ns}` at which the agent's or approver's registration was revoked, even after the key is registered again (HIST-5 for every other field). | D |
| SH-6 | **Events per method:** each successful change method logs exactly one line, of exactly one event: `add_agent` and `add_approver` → `key_added` `{public_key, account_id, role, registration_id}`; `revoke_key` → `key_revoked` `{public_key, account_id, role, registration_id, revoked_at_block, revoked_at_ns, voided_pending}` (`voided_pending` = the removed registration's `pending`); `request_action` → `approval_requested` (SH-4); `approve` → `action_approved` (SH-5); `reject` → `action_rejected` with `data` = the returned `RejectionView` = `get_rejection(i)`. `new`, every `get_*` and every failed call log nothing. | D |
| SH-7 | **View mapping:** <br>• `get_approval(i)` is `approval(s,i)` with the revocation fields from `proof_revocations` (RD-8), and `get_approvals(f?,l?)` is `approvals(f.unwrap_or(0), l.unwrap_or(50))` mapped the same way; <br>• `get_request(i)` is `None` for `i ≥ #R`, otherwise a `RequestView` with every field equal to `R[i]` (including `agent_registration_id`) and `status = request_status`; <br>• `get_rejection(i)` is `None` unless `R[i].rj ≠ None`, otherwise every field of `R[i]` and its rejection; <br>• `get_revocation(g)` is `V(g)` as `{block, ns}`; <br>• `get_principal(k)` is `None` for `k ∉ dom P`, otherwise `account_id`, `role`, `registration_id` and `pending` equal `P(k)`; <br>• `get_owner` is `o`; <br>• the counts are the store counters. | D |
| SH-8 | **JSON shape:** <br>• field names as in the README for `RequestView`, `ApprovalProofView` (with `agent_key_revoked_at` / `approver_key_revoked_at`: `null` or `{block, ns}`), `RejectionView`, `PrincipalView` (with `registration_id`), `KeyView`, `KeyRevokedView` and `BlockTimeView`; <br>• `*_ns` and `ns` are strings (`U64`); ids, indices, heights and `block` are numbers, exact above 2⁵³; absent results are `null`; <br>• arguments `{}`, or `from_index`/`limit` set to `null`, give the defaults; whole-args `null` and empty input fail with near-sdk's deserialization panic (message recorded). The argument half exists only in the wasm wrappers: S (M6); <br>• `From` conversions, `request_view`, `proof_view` and `rejection_view` preserve every field. | D, S |
| SH-9 | **Init:** `new` succeeds once (`#[init]`) and only from `C` (`#[private]`). Every method fails before init (`PanicOnDefault`). Post-init state is `Init(owner_id)`. Wrapper-only, so unit tests can't see it [conf: high]. | S / R |
| SH-10 | **Deposits:** call all 16 exports at the pin (13 before PR #15, F-15) with 1 yocto attached, using **full-access** keys (function-call keys can't attach deposits), calling `new` on a fresh, uninitialized deployment. Every change method and `new` must fail with near-sdk's non-payable panic; record the outcome for each `get_*`. *Observed (M6, near-sandbox 2.13.4):* every change method and `new` fail with `Method <m> doesn't accept deposit`; every `get_*` (and `contract_source_metadata`) **accepts** the deposit when called as a transaction, so the wrapper checks only `&mut self` methods. | S |
| SH-11 | **Export surface:** function exports are exactly the 16 `#[near]` methods (`new`, `add_agent`, `add_approver`, `revoke_key`, `request_action`, `approve`, `reject`, `get_owner`, `get_principal`, `get_request`, `get_request_count`, `get_approval`, `get_rejection`, `get_revocation`, `get_approvals`, `get_approval_count`) plus `contract_source_metadata` and `__contract_abi` (cargo-near embeds the ABI; observed at M3). The only non-function export is `memory` (no `__data_end`/`__heap_base` after cargo-near's `wasm-opt`). `wasm-surface.expected` lists both sets. No `Store` method, upgrade or owner transfer is exported. | W / S |
| SH-12 | **No escape hatches:** wasm imports include no `promise_*` (which covers create, then, batch, yield, and, return), no deploy, no delete, no add-key, no global-contract and no transfer host function; `wasm-surface.expected` lists the exact import set (17 `env` functions at the pin). The only storage keys written are those of ST-5. | W / R |
| SH-13 | **Unsupported key type (F-17):** `add_agent` and `add_approver` panic with exactly `UNSUPPORTED_KEY_TYPE` ("ML-DSA-65 keys are not supported") for an ML-DSA-65 key, after the owner check (a non-owner still gets `NotOwner`) and before the core's guards (`LogFull` included), logging nothing. Every registered key is then ed25519 or secp256k1, the types RES-1 and RES-2 are computed for. | D |

### 5.9 Runtime assumption tests (RT): sandbox, reproducible wasm

| ID | Establishes | For |
|---|---|---|
| RT-KEY | A function-call key `k` of account `a` arrives as `signer = predecessor = a` with `signer_pk = k`. An unregistered key on the right account gets `UnknownKey`. A registered key added to another account gets `KeyAccountMismatch`. | ASM-SIGNER |
| RT-RELAY | `request_action`/`approve` through a third-party relay contract fails with `IndirectCall`. | ASM-PRED |
| RT-SELFACCT | A contract on the signer's own account calling `C` **succeeds** (documents F-9). | ASM-PRED |
| RT-METATX | NEP-366 delegate action: record the outcome (expected `IndirectCall`). *Observed:* `IndirectCall` on C, for an agent function-call key and for a full-access agent key; the relayer's transaction succeeds. | ASM-META |
| RT-FCKEY | An agent function-call key scoped to `request_action` can't call `approve` or `add_agent`. Assert `InvalidTxError::InvalidAccessKeyError(MethodNameMismatch)`, not a contract panic: the contract would also reject both calls, so only the error kind shows the runtime enforced the scope. | ASM-FCKEY |
| RT-REVERT | Force failures, including `LackBalanceForState` after draining `C`'s balance, and a call with just enough gas for the core step. State and views must be unchanged. Record whether the event survives in the failed outcome. *Observed:* state unchanged in every case; the event **survives** in the failed outcome for out of gas after the emit (attached gas from about 27/40 to 39/40 of the minimum) and for `LackBalanceForState` on `request_action` and `approve`. | ASM-ATOMIC |
| RT-BATCH | One tx `[request_action("a"), request_action("")]`, signed by a **full-access** key of the agent account that is also its registered agent key (a function-call key can sign only single-action txs). The outcome fails at action index 1 with "action is empty", and the counters are unchanged. Record whether the first event appears. *Observed:* it **appears** in the failed outcome. | ASM-ATOMIC |
| RT-RESET | Delete and recreate `C`: counters reset. VER-3 (a full-access key or a `DeleteAccount` since `b₀`) detects it. VER-6 is only a heuristic that catches it while counters are below cached values. | ASM-CODE |
| RT-SPOOF | A spoofer contract logs a forged `EVENT_JSON`. The VER-1 `executor_id` rule rejects it. | VER-1 |
| RT-TIME | 40 requests, 20 approvals and 20 rejections interleaved with 80 skipped blocks: each stored `requested_at`/`approved_at`/`rejected_at` equals the block its receipt ran in, heights strictly increase and timestamps never decrease in execution order. A sample on one node, not the chain rule. | ASM-TIME |
| RT-CODEHASH | The wasm under test is the `cargo near build reproducible-wasm` output. Record its sha256 (hex) **and** the NEAR `code_hash` (base58 of sha256). *Was blocked by F-12 (resolved upstream, R-8).* | ASM-DEPLOY, ASM-COMPILE |
| RT-TRACE | **Main flows on the deployed artifact.** Replay every `conformance/traces/*.txt`, plus 200 random sequences of ≤30 ops, on the reproducible wasm. For each step, these must equal `spec.rs`: the result or return value, the exact failure message, the receipt logs, and the `get_*` views (including `{}` args, nulls, `limit = 0`, and values > 2⁵³). *As built (M6):* `spec.rs` runs over the Kani `ArrStore` (at most 4 requests), so the per-step oracle is the real core on the host over `MemStore`, with the sandbox's block times and JSON rendered from the README; it is tied to `spec.rs` by Kani and plain mode, and to `tla.rs` and `step/4` because every step must also match the trace file (`prolog.txt` from `step/4`; `core-random.txt`, the 200 × 30 random sequences, from `kani/src/trace.rs`, each step checked against `tla.rs`). *Observed (M6):* 210 traces, 6,800 steps, every step equal, on the reproducible wasm (near-sandbox 2.13.4, about 10.5 min with 6 jobs). | ASM-COMPILE, ASM-SDK |

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
   `[approve]` or `[approve, reject]` for approvers (the README asks for both
   since PR #15 added `reject`), finite allowance. The contract can't list its
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
| C-4 | Each event comes from exactly one core operation: `key_added` from `add_principal` (driven by both `add_agent` and `add_approver`), `key_revoked` from `revoke_key`, `approval_requested`, `action_approved` and `action_rejected` from `request_action`, `approve` and `reject`. Every authority- or proof-changing method emits an event, or has an `accepted_risk` (`new`, which emits nothing). Only change methods emit. Since `3426c92` admin operations emit `key_added` / `key_revoked` (R-7), and `reject` emits `action_rejected`. | P |
| C-5 | Generated constants equal the requirement constants: `DPG ≤ PG`, `MAXP ≥ 1`, and `N` within the RES-2 bound. | P |
| C-6 | The generated API surface equals the requirements' API table: the wasm's `#[near]` function exports (`api_method/1`) are exactly the `method/3` names, the only other function exports are near-sdk's (`api_sdk_export/1`: `contract_source_metadata`, `__contract_abi`), and each ABI entry's kind and modifiers match the method's kind and authority (`view` ↔ view; `call` ↔ change; `call` with `[init, private]` ↔ `new`). | P |
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
| D11 no upgrade, ownership transfer, expiry or threshold (rejection is D17) | SH-11, SH-12, C-1, C-6 |
| D12 atomic, bounded execution | TX-0, ROB-1, ROB-2, ROB-4, ST-1, ST-2, ST-3, ST-4, ST-5, ST-6, ST-7, ST-8, SH-2, SH-3, RD-6, LEM-3 |
| D13 timestamps recorded and ordered | INV-10, TR-4, RT-TIME |
| D14 deployed artifact = verified source | RT-CODEHASH, RT-RESET, RT-TRACE, DEP-1, VER-2, VER-3, VER-6 |
| D15 verification hygiene (ASM-SPEC, ASM-TOOLS) | TR-5, MC-1, MC-2, C-2, C-3, C-5, C-6, C-7, C-8, C-9, C-10 |
| D16 verifier and executor discipline | VER-1, VER-4, VER-5, VER-7, VER-8 |
| D17 an approver of another account may reject a pending request | TX-7, HIST-9, INV-13, INV-5, INV-6, TR-2, RD-7, SH-6, TLA-LIVE-2 |

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

M1 implements this design against the pinned API (results and run times in
[`kani/RESULTS.md`](kani/RESULTS.md)). M2 adds the ghost stores in
`ghost.rs` (`Sparse`, `Window`, `Counting`, plus `Obs`, the abstraction
`α` read through the `Store` interface, and `expect`, the TX results with
both counter `LogFull` guards) and their harness bodies in
`ghost_checks.rs`. `Sparse` holds each `LookupMap` as a fixed-capacity
association list and the counters as plain `u64`, so the shell's `+= 1`
at `u64::MAX` panics as it does on-chain; the plain test
`sparse_header_hash` fails when `contract/src/lib.rs` no longer has the
sha256 in its header. Because M1 runs the core over `ArrStore` (RESULTS.md
deviation 1), `h_store_laws_arr` and the `ArrStore` leg of `h_refine_*`
discharge the ST-1/ST-3 obligations that deviation created.

### 6.2 Harnesses and covers

`run-kani.sh` fails the run on any `UNSATISFIABLE`/`UNREACHABLE` cover. Use
`--fail-uncoverable` if the pinned Kani has it [conf: low-med].

Each `h_step_{op}` row runs as five Kani harnesses, `_tx` (exact result,
TX-0), `_post` (exact post-state), `_hist` (HIST, `Φ`), `_inv` (INV-0..10,
LEM, TR-4) and `_reg` (INV-11..16): one CBMC run for all of them needed
more than 15 GB once PR #15's state was added. They form one cover family.

| Harness | Pre-state | Properties | Covers (must be SATISFIED) |
|---|---|---|---|
| `h_init` | `MemStore::new(OWNER)`, empty `H` | INV and GH at init | none |
| `h_step_add` | arbitrary `Inv ∧ GH` state, `#P,#R,#L ≤ 3` | TX-0, TX-1, TX-6, HIST-*, INV, GH and LEM-1..2 step, TR-6 `Φ` step | Ok, NotOwner, KeyAlreadyRegistered |
| `h_step_revoke` | same | TX-0, TX-2, TX-6, HIST-*, HIST-8, INV, GH and LEM-1..2 step, TR-3 step, TR-6 `Φ` step | Ok, NotOwner, KeyNotRegistered, a pending request becomes void |
| `h_step_request` | same; actions from the §6.3 alphabet | TX-0, TX-3, TX-4 (except the cap boundary), TX-6, HIST-*, INV, GH and LEM-1..2 step, TR-6 `Φ` step | Ok, the 4 TX-3 errors, EmptyAction |
| `h_step_approve` | same; time monotone | TX-0, TX-3, TX-5, TX-6, HIST-*, INV, GH and LEM-1..3 step, INV-10, TR-2, TR-3, TR-4 steps, TR-6 `Φ` step | Ok, the 4 TX-3 errors, RequestNotFound, AlreadyApproved, AlreadyRejected, AgentRevoked, ActionMismatch, SelfApproval |
| `h_step_reject` | same; time monotone | TX-0, TX-3, TX-7, TX-6, HIST-* (HIST-9), INV (INV-13), TR-2 step, TR-6 `Φ` step | Ok, the 4 TX-3 errors, RequestNotFound, AlreadyApproved, AlreadyRejected, AgentRevoked, SelfApproval |
| `h_raw_{op}` | arbitrary store, **no** `assume(inv)`; `pend` any `u32`, `from`, `G` and registration ids any `u64` | ROB-1, TX-0, TX-1..5 and TX-7 exact result via `expected`, HIST-7 (add, revoke, reject); for request: the INV-9 bound step (`Ok ⇒ pend < MAXP ∧ pend' = pend + 1`) and the TX-4 cap boundary | Ok per op; add: LogFull at `G = MAXU`; request: Ok at `pend = MAXP − 1` and TooManyPending at `pend = MAXP` |
| `h_bmc_from_init` | `Init` + ≤ 5 ops (any kind, ≤ 2 requests), ghost history | GH (TR-1, TR-7) and TR-2 over every such trace | approved; rejected |
| `h_bmc_from_init_witness` | `Init` + the 6 ops add, add, request, revoke, add, approve (any arguments) | the same, along that shape | revoke → re-add → approve old id fails with AgentRevoked |
| `h_read` | like `h_step`; `id`, `from`, `limit` any `u64` | RD-1, RD-2, RD-5, RD-7, RD-8, LEM-4 | non-empty page; void status; rejected status; a proof whose agent key was revoked |
| `h_page_arith`, `h_page_arith_empty` | `Window` over any `u64` `count`, offset and request-id shift; out-of-page reads, out-of-order reads and any write panic. `h_page_arith`: every request approved, `from` any `u64`, `limit ≤ 2` (`PAGE_SMALL`), page length and every entry checked. `h_page_arith_empty`: every request absent (fallback 6), any `limit`, `from` one of the 10 `PAGE_FROMS` (0, 1, 2^32, 2^63 and the distances to `u64::MAX` that change the page); the per-read assertions bound the slots read by `e − f`. Plain mode runs both over any `from` and `limit` and also checks the slot count of empty pages. `#[kani::unwind(5)]` / `(102)` | RD-3, RD-6, ROB-4 (`approvals` reads), and the page clamp | non-empty page at `count = MAXU`; non-empty page where `f + l` overflows; full page |
| `h_proto_{request,approve}` | `Sparse` **raw** state (no `assume(inv)`), counters any `u64` ≥ stored size; `h_proto_request_empty` is the `""` instance. ST-2 is also checked from states with counters equal to size, in `h_refine_*`. | ST-2, ROB-2, TR-5 (exact result via `ghost::expect`, which adds both counter `LogFull` guards to `spec::expected`) | Ok; LogFull (approve's only from non-`Inv` states, per LEM-3) |
| `h_proto_{add,revoke,reject}` | same | ST-2 | Ok, each error (add, revoke); Ok (reject) |
| `h_count_{op}` | `Counting` over `MemStore`, raw state | ROB-4 (per-operation read and write bounds; no write on failure except F-6) | none |
| `h_refine_{op}` (approve and reject as `_tx` and `_post`) | the same state in `ArrStore` and `Sparse` (and `MemStore` in plain mode; under Kani ST-1 ties `MemStore` to `ArrStore`): INV-0, INV-1, INV-8, distinct revocation ids and no live registration revoked (every `Inv` state, and more) | ST-3 (same results, same `α` read through `Store`), ST-2 with counters equal to size | none |
| `h_store_laws_{mem,sparse,arr}` (mem and sparse split by law: `_reg` insert and remove principal, the base harness the other five, each over a fixed shape; arr every shape) | small well-formed stores (distinct keys, dense ids, distinct revocation ids), one mutator within its law's precondition | ST-1, INV-0 (`MemStore`, `ArrStore`) | insert over an existing key; remove of an absent key |
| `h_action_len` | agent registered; `len ∈ {0, 1, 2048, 2049}` with the 1-byte case `" "`, plus the 2050-byte multi-byte case; result by kind and non-action fields (fallback 5); `#[kani::unwind(2051)]` so the chars-vs-bytes mutant fails on its assertion | ROB-3 | Ok, EmptyAction, ActionTooLong |
| `h_canary` | any | asserts a false property; must report FAILED | none |

### 6.3 Bounds and the small-scope argument

| Dimension | Bound | Justification |
|---|---|---|
| Accounts | 4 (owner = 0); 8 in `h_oracle_*` (ST-8W) | ASM-IDENT parametricity. Since §18.6.1 the claim below is not needed for ST-8, whose 8 values cover every footprint injectively. `approve` reads 5 account terms: predecessor, signer, `P(c.key).acct`, `R[i].aa`, `P(R[i].ak).acct`. The guard order forces predecessor = signer = `P(c.key).acct` before the last two comparisons, so at most 3 values plus the owner are ever distinguished, and 4 values realize every reachable pattern. |
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

The "≤ 3 each" row is made precise in [`kani/CUTOFF.md`](kani/CUTOFF.md):
**CUT-1** (harnesses `h_cut_*`) proves each call's footprint, and **CUT-2**
(the argument there) shows the harness bounds are then sufficient for REF-1..3
at every size, except E1 (pending at `MAXP`) and E2 (counters at `u64::MAX`),
which the raw and `Sparse` harnesses cover. **U-1**
(`tools/scripts/kani-loops.py`, CI job `loops`) derives a bound for every
loop in every harness's goto program from a constant and fails if any
reachable loop needs more than its harness `--default-unwind`; with
unwinding assertions on, a bound that is too low fails loudly.

### 6.4 Mutants

`kani/mutants/*.patch` are applied to a temporary copy of the core. Each must
be killed by its listed harness under Kani and by plain mode. 27 of these were
seeded against the upstream suite during planning (27/27 killed).

| Killed by (milestone) | Mutants |
|---|---|
| `h_step_*` (M1) | self-approval check; relay check; key-account binding; double log push; drop-empty; `trim`-empty; `active_from` dropped / strict / +1 / 0; no increment; no decrement; no principal write-back; action-mismatch dropped; already-approved dropped; three guard swaps; void reported as pending (`h_read`); revoke not owner-only; `approval_index` from request count; proof copies agent as approver; `push_approval` before the checks |
| `h_step_*`, `h_read` (M1, PR #15 API) | reject: self-approval check dropped, no decrement, rejection records the agent's registration; already-rejected dropped; revocation not recorded; registration count not incremented; request records registration 0; `proof_revocations` swapped (`h_read`); rejected reported as pending (`h_read`) |
| `h_raw_*` (M1) | cap off-by-one (`>=` changed to `>`) (`h_raw_request`); add's `LogFull` dropped (`h_raw_add`: the counter overflows) |
| `h_action_len` (M2) | length off-by-one (37); chars-vs-bytes (38, `h_action_len_multi`: the 2050-byte case alone; the mutant counts lead bytes in a plain loop, since std's `chars().count()` runs CBMC out of memory) |
| `h_page_arith` (M2) | page clamp (`.min(approval_count)`) removed (39); page addition wraps (40) |
| `h_proto_*` (M2) | `LogFull` request dropped (41, `h_proto_request`); `LogFull` approve dropped (42, `h_proto_approve`) |
| `h_store_laws_mem_law_insert` (M2) | `MemStore` insert pushes duplicates (43) |
| **Must survive** (equivalent, F-14) | role check dropped / account check dropped in `live_agent_registration`. If either is killed, INV-8 or LEM-4 is wrong. Checked with the harnesses that see raw states skipped (`h_raw_*`, `h_proto_*`, and the `facts` generator), since the equivalence holds only under INV-8. |

---

## 7. Verus (M5): real code first, model as fallback

**Status (2026-10-14): not started; the spike is a pending decision.**
`verus_min_verified = 0`. Path A is the only route to `evidence = proof` on
the real code.

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

**Path B (superseded by §18).** The Lean layer (§18) is a model proof of the
same machine, linked to TLA+, the core and Prolog mechanically (MC-4, REF-5L)
rather than by shared comments, so path B is not planned any more; if the
spike fails, M5 ends and §18 stands. The original plan, for reference: write a spec machine in
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

**Status (2026-10-11).** Implemented as above with Scryer Prolog 0.10.0
(`SCRYER` in `versions.env`), with these differences: traces live in
`verification/mc2.pl` (not `gen_traces.pl`); `code_facts.pl` is generated by
`kani/src/facts.rs`, which **observes** the guard precedence on 400k random
calls (`code_before/3` pairs, topological order) instead of copying a table;
`model/FROZEN` holds the hash of `approval_machine.pl` as written from the
requirements, before any cross-check ran. C-1..C-5 and C-7..C-10 pass; C-6
waits for M3's `api_facts.pl`. MC-1: 51,568 states, 0 violations
(`mc1_state_floor`); MC-1s: 2,151. MC-2 agrees both ways (60 × 80 calls);
the wasm leg (RT-TRACE) waits for M6. Scryer reclaims memory only on
backtracking: long searches must be failure-driven loops over dynamic
facts.

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
  - **`mutants/*.patch`, each must fail the suite** (`near-tests/run-mutants.sh`):
    - `add_agent` registers Approver;
    - `caller()` uses the signer as predecessor;
    - `now()` swaps height and timestamp;
    - emit before `ok()`;
    - status mapping inverted;
    - default `limit` set to 100;
    - `revoke_key` passes the signer;
    - `push_request` keyed by `count+1`;
    - two maps sharing a prefix;
    - `request_view` sets `requested_at_block` from `timestamp_ns`;
    - (PR #15) `proof_view` swaps the two revocation fields;
    - (PR #15) `key_revoked` reports `voided_pending = 0`.
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

**Status (2026-10-15): M3 built; statuses `in-progress`.**

- **`near-tests/`** depends on `approval-contract` and `approval-core` by
  path and on near-sdk 5.29.1 with `unit-testing` (the real `VMLogic` of
  near-vm-runner 0.37.4). Its `Cargo.lock` is the mirror's plus this crate's
  own entry; `tests/lockfile.rs` checks the 258 shared packages. The
  contract is driven as the runtime drives it: every call starts from
  `state_read`, a successful call ends with `state_write` and a drop, and a
  panicking call is discarded with its writes (ASM-ATOMIC). Expected values
  are built from the README's field names and the core's results on a
  `MemStore`, never from the contract's view types. α of the contract is
  read through its `Store` impl over the key universe (local to
  `near-tests/src/lib.rs`, not shared with `kani/spec.rs`, whose `abs` is
  over `ArrStore<Acct, Key>`); the exact storage key set closes the gap.
- **`store_diff.rs`** (ST-4, SH-2, and per step SH-3..SH-7 and ST-5):
  10,000 × 50 steps with reload every step pass in about 3.5 min (debug
  profile, dependencies at `opt-level = 2`, one core). After every step:
  equal results and exact panic messages, exactly one event with the
  expected data, equal α, the exact storage key set, and every view on every
  id equal to the core's reads. Over a full run every operation succeeds
  and all 16 errors reachable from `Init` occur. `STORE_DIFF_SEQS`,
  `STORE_DIFF_STEPS`, `STORE_DIFF_SEED` and `STORE_DIFF_VIEWS` size it.
- **`shell.rs`** (14 tests, under 5 s): SH-1, SH-3 (all 17 errors; the
  three `LogFull` guards on states with a counter at `u64::MAX`; payload
  `HostError(GuestPanic { panic_msg })`), SH-4..SH-8, ST-5, ST-6 (golden
  bytes in `tests/golden/layout.txt`, regenerated with `UPDATE_GOLDEN=1`),
  RES-1 (the Borsh bounds equal VMLogic's storage metering at the worst
  case), RES-2 (13197 B worst line) and F-17. The argument half of SH-8 and
  SH-9/SH-10 need the wasm wrappers: M6.
- **Mutants:** the ten listed above, adapted to PR #15 (`emit before ok()`
  is `key_added` emitted before `add_principal` runs; the status mapping
  swaps `pending` and `void`), plus two for PR #15. `run-mutants.sh` first
  checks the unpatched copy passes; all 12 are killed (about 13 min).
- **`wasm-surface.sh`** builds with `cargo near build non-reproducible-wasm
  --locked` (cargo-near 0.22.0, the version of the upstream reproducible
  image) in a temporary copy, or takes `--wasm`/`--abi`; parses imports and
  exports in Python; diffs against `wasm-surface.expected` (16 methods,
  `contract_source_metadata`, `__contract_abi`, `memory`; 17 `env` imports);
  and regenerates `prolog/extracted/api_facts.pl` from the exports and the
  ABI. C-6 passes on it.

**Status (2026-10-15, M6 and M7 built; statuses `in-progress` pending the spec
review).**
- **`sandbox/`** is a standalone workspace (`near-workspaces` 0.23.0, the
  default near-sandbox 2.13.4, protocol 86) with its lockfile seeded from the
  mirror (`scripts/check-lock.py`: 343 shared packages, no mismatch).
  `scripts/run-sandbox.sh` is the job: lockfile check, `scripts/build-res.sh`
  (the three helper contracts, via `cargo near`), `cargo test --locked`.
  `scripts/build-wasm.sh [non-reproducible|reproducible|reproducible-manual]`
  builds the wasm under test; tests take `APPROVAL_WASM`.
- **Tests:** `runtime.rs` (RT-CODEHASH, RT-KEY, RT-RELAY, RT-SELFACCT,
  RT-METATX, RT-FCKEY, RT-REVERT, RT-BATCH, RT-SPOOF), `shell.rs` (SH-9,
  SH-10, RES-1 measured deltas, RES-3), `deploy.rs` (DEP-1/VER-2/VER-3/VER-8
  demo, RT-RESET), `trace.rs` (RT-TRACE). Tests that record an outcome write
  `results/<ID>.json`; the observations are copied into the `observed` field
  of the matching `[assumptions]` entries.
- **Wasm under test:** the reproducible build of the pin, sha256
  `3f48c2f2b121d359507ebc696c8a402e2ae7cba1c57552a5e18c49a65761bde9`,
  `code_hash` `5G334oPHzjDvPLXKUSstbaf3BzUPaj1sWZnDhy5Baauv`, built with the
  pinned `sourcescan/cargo-near:0.22.0-rust-1.97.0` image and cargo-near's
  NEP-330 environment (`reproducible-manual`; the container needed a proxy).
  Every test also passes on the non-reproducible host build (`ffdbb5a7…`).
- **RT-TRACE inputs** are checked in under `conformance/traces/`
  (`sandbox/scripts/gen-traces.sh`): `prolog.txt` (10 × 80 calls from
  `step/4`) and `core-random.txt` (the 200 random sequences, 30 calls each,
  from `kani/src/trace.rs`). Each step is compared with the trace file and
  with the real core run on the host (see RT-TRACE in §5.9). The full run
  (210 traces, 6,800 steps) passed on the reproducible wasm in 632 s with
  `RT_TRACE_JOBS=6`.
- **Recorded outcomes:** see §5.9 (RT-METATX, RT-REVERT, RT-BATCH) and §5.8
  (SH-10). The event of a failed receipt **does** survive in its outcome
  (out of gas after the emit, `LackBalanceForState`, a failed batch), so
  VER-1's "successful receipt" clause is load-bearing.
- **`deploy-checks/check_deployment.sh <net>`** (Python 3.11 behind a shell
  wrapper) implements DEP-1.1–1.5, VER-2, VER-3 and VER-8 from
  `[deployment.<net>]`, with `CHECK_<KEY>` overrides. Its only indexer is
  `rpc-scan` (walk every block from `b0`), fit for a local chain; on a public
  net without an indexer DEP-1.4, VER-3's scan and VER-8 fail as unchecked.
  `[deployment.sandbox]` drives the demo; `[deployment.testnet]` is an empty
  template (no testnet deployment has been made).
- **`prolog/verification/verifier_rules.pl`** encodes VER-1..8;
  `tests/test_verifier_rules.pl` (run by `run-prolog.sh`) has accepting and
  rejecting cases for each. The sandbox feeds it real observations: RT-SPOOF
  (VER-1 on real, copied, forged and failed-receipt events), the VER-8 key
  views of sandbox proofs, and RT-RESET (VER-6).
- **Local only:** neard raises `RLIMIT_NOFILE` to 65535; where the hard
  limit is lower, `scripts/dev-nofile-shim.sh` (an `LD_PRELOAD` shim) is
  needed. CI's runners don't use it.

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
│   ├── versions.env    # KANI, TLA2TOOLS, APALACHE, LEAN, VERUS, SCRYER, CARGO_NEAR, NEAR_SANDBOX, RUST_TOOLCHAIN
│   └── scripts/        # run-prolog.sh (fixed), run-verus.sh (fixed), run-kani.sh, run-tla.sh,
│                       # check-pin.sh, check-status.sh, check-hygiene.sh, wasm-surface.sh
└── projects/near-approval/
    ├── strategy.md  status.toml  wasm-surface.expected
    ├── source-mirror/                 # submodule → trust-framework @ pinned_commit
    ├── prolog/{requirements,model,verification,extracted,tests}/
    ├── conformance/traces/            # generated, checked in
    ├── kani/{src,tests,mutants,kani-stub}/
    ├── tla/{*.tla,*.cfg,mutants}/     # §17; build/ is generated
    ├── lean/{ApprovalLean,canary,mutants}/  # §18; .lake/ is generated
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
| `layer` | primary technique: `kani | plain | verus | prolog | tla | lean | unit | difftest | sandbox | wasm-check | review | deploy-check` |
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
- `lean` → `model-proof` (theorems about the model) or `model-check` (MC-4)
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
| **M1.6** | Lean (§18) | • `run-lean.sh near-approval` passes: LEAN-IND, LEAN-STEP, LEAN-TR, LEAN-GUARD, LEAN-WIT with no `sorry`, axiom audit clean, canaries fail, REF-5L and MC-4 equal. <br>• Every Lean spec mutant killed. <br>• **Statuses:** LEAN-*, REF-5L, MC-4 updated; ASM-TLA-SCOPE narrowed to liveness. | 3–4 |
| **M2** | Ghost-store harnesses | • `h_page_arith`, `h_proto_*`, `h_count_*`, `h_refine_*`, `h_store_laws_*` and `h_action_len` pass, with their covers satisfied. <br>• Every §6.4 mutant except the must-survive pair is killed by Kani and by plain mode. <br>• RD-4 plain check passes (log ≤ 250; `l ∈ {1, 2, 99, 100, 101, 200}`). <br>• **Statuses:** INV-0, TR-5, RD-3, RD-4, RD-6, ROB-2..4 and ST-1..3 updated. | 1–2 |
| **M3** | near-sdk shell and store | • `store_diff.rs` (10k × 50, with reload) passes. <br>• `shell.rs` passes. <br>• All shell mutants are killed. <br>• Golden Borsh bytes are committed. <br>• `wasm-surface.sh` diff on the non-reproducible build is clean. <br>• `api_facts.pl` generated. <br>• **Statuses:** ST-4..6, SH-1..8, SH-11, SH-12, RES-1 and RES-2 updated. | 2–3 |
| **M4** | Prolog | • `run-prolog.sh near-approval` exits 0 (strict). <br>• C-1..10 pass, or each failure has a recorded decision (C-4/F-8). <br>• MC-1 and MC-1s meet the §5.11 criteria, each in < 5 min, and `mc1_state_floor` is recorded. <br>• Traces checked in; MC-2 replay passes on the core and `spec.rs`. <br>• `code_facts.pl` regeneration shows no diff. <br>• **Statuses:** C-1..10, MC-1 and MC-2 updated. | 3–4 |
| **M5** | Verus (2-day spike, then path A; path B superseded by §18) | • Spike decision recorded. <br>• `verus/canary/false_lemma.rs` fails. <br>• **Path A:** the twin verifies with refinement `ensures` for every public core fn and `MemStore`; the erasure check passes; every `REWRITES.toml` entry has a passing Kani equivalence harness. Core properties become `verified-with-assumptions` / `proof`, with trusted ASM-IDENT, ASM-STRLEN and listed std specs. <br>• **Path B:** all lemmas in §7 are proved under the hygiene gate; spec mutants each break a lemma. Status becomes `verified-with-assumptions` / `model-proof` + ASM-MODEL. | 9–15 |
| **M6** | Sandbox | Needed F-12, resolved upstream (R-8). <br>• RT-* (including RT-TRACE and RT-BATCH), SH-9 and SH-10 pass on a pinned neard with the reproducible wasm. <br>• `wasm-surface.sh` diff on the reproducible build is clean. <br>• RES measured, with thresholds and both hashes recorded. <br>• RT-METATX outcome documented. <br>• `[assumptions]` statuses filled from observations. <br>• `cargo expand` review of SH-9/RD-6 signed off. <br>• **Statuses:** RT-*, SH-9, SH-10 and RES-3 updated. | 3–5 |
| **M7** | Deployment and automation | • A testnet deployment with the DEP-1 lock batch and at least one agent key and one approver key registered; `check_deployment.sh` passes; `[deployment.testnet]` filled. <br>• `verifier_rules.pl` encodes VER-1..8; RT-SPOOF and a VER-8 check against the testnet proof demonstrate them. <br>• Every CI job live; pin-bump procedure documented; `docs/architecture.md` gains the Kani, shell and deployment layers. <br>• **Statuses:** DEP-1 and VER-1..8 updated. | 2 |

**Total: M0–M7 about 25–39 days.** Kani precedes Verus because it checks the
deployed code itself and buys the most assurance per day.

**Progress (2026-10-15).** M3 is built (§9): `store_diff.rs` 10k × 50 and
`shell.rs` pass, all 12 shell mutants are killed, golden bytes are committed,
the `wasm-surface.sh` diff is clean and `api_facts.pl` is generated, so C-6
runs and passes. Its statuses are `in-progress` until the spec sign-off and
the `near-unit` CI job; F-17 is new.

**Progress (2026-10-14).** M0, M1.5, M1.6 and M4 are done, except C-6 (waits
on M3). M1 is done except its "spec reviewer sign-off" line, so its statuses
stay `in-progress`. M2, M3, M5, M6 and M7 have not started.

**M6 and M7 (2026-10-15).** Built and passing locally on near-sandbox 2.13.4
with the reproducible wasm (§9): every RT-* test, SH-9, SH-10, RES-1
(measured), RES-3, RT-TRACE, the `check_deployment.sh sandbox` demo with its
negative cases, and `verifier_rules.pl`. Not done: the `wasm-surface.sh` diff
on the reproducible build (needs M3's script; RT-CODEHASH records the export
list), the `cargo expand` review of SH-9/RD-6, the testnet deployment and
`[deployment.testnet]`, the `sandbox` and `deploy-check` CI jobs, and
`docs/architecture.md`. Statuses stay `in-progress` (spec reviewer sign-off;
M7 also needs the testnet decision). Remaining effort
on the critical path (re-pin, review, M2, M3, M6) is about 6–10 days plus
the review; M7 adds 2 and needs a testnet decision.

## 14. CI (`.github/workflows/near-approval.yml`)

| Job | Trigger | Fails on |
|---|---|---|
| `pin` | PR, push | gitlink ≠ pin; hash drift; release profile without `overflow-checks = true` or borsh feature gating (ASM-COMPILE). Every other job depends on it. |
| `plain` | PR, push | any failure; drift in generated `code_facts.pl` |
| `kani` | PR, push, nightly, manual (one job per harness or step part, 38 jobs; about 110 runner-minutes on the self-hosted Macs; 120 min per harness) | any failure; any unsatisfied cover (the `covers` job, across jobs); `h_canary` passing |
| `loops` | PR, push | U-1: a reachable loop in a harness needs more than its `--default-unwind` |
| `mutants` | weekly | a core or shell mutant survives; an equivalent mutant is killed |
| `tla` | PR, push | any §17.3 check failing; a witness or the unfair liveness run passing; a spec mutant surviving |
| `prolog` | PR, push | any failure; drift in `conformance/traces`; MC-1/MC-1s state count below the floor |
| `lean` | PR, push | a `sorry` or forbidden construct; an axiom beyond `propext`, `Classical.choice`, `Quot.sound`; a canary compiling; guard order ≠ `tla_facts.pl`; a REF-5L, MC-4 or LINK difference; a Lean spec mutant surviving |
| `verus` | PR, push (from M5) | any error; count below the floor; canary verifies; a spec mutant verifies; hygiene |
| `near-unit` | PR, push | any failure; lockfile version mismatch; export or import diff (non-reproducible build) |
| `sandbox` | nightly; submodule bump; manual (from M6) | any failure; export or import diff (reproducible build); threshold exceeded |
| `status-lint` | PR | a non-`unverified` ID without its artifact or PROP tag; `verified*` without a passing harness in this run; `evidence` not allowed for its `layer` (§12); a K/V property past `unverified` without spec sign-off |
| `upstream-watch` | weekly (`.github/workflows/upstream-watch.yml`) | none; opens an issue when a path in `tools/upstream-watch.toml` changed (near-proof-arena specs and challenges; the Nomicon pages the assumptions cite) |
| `deploy-check` | manual; weekly | any DEP or VER violation |

trust-framework is private, so CI needs a deploy key or fine-grained token for
the submodule (OQ-7, resolved in M0: secret `CROSS_REPO_BUILD_KEY` via
`tools/scripts/ci-submodule.sh`).

**Live (2026-10-14):** `pin`, `plain`, `loops`, `kani`, `covers`, `tla`,
`lean`, `prolog`, `mutants` and `upstream-watch`, on self-hosted macOS
runners (`vars.CI_RUNNER`). On a PR, `pin` always runs and each other job
runs only when the diff touches its inputs (`tools/scripts/ci-areas.sh`;
Markdown changes run none). Push to `main`, nightly and manual runs run
every job.
Not yet built: `verus` (M5).

## 15. Risks

| Risk | Mitigation |
|---|---|
| Kani too slow at these bounds [conf: low on timing] | §6.3 ladder; per-op split; plain mode keeps CI useful |
| `assume(inv)` makes step proofs vacuous | Covers on every outcome; `h_raw_*` without the assumption; must-survive mutants |
| Spec bugs (ASM-SPEC) | Three independent semantics with replay; mutants; traceability; human spec sign-off |
| Runtime assumptions wrong (META, LIMITS, logs on failure) | Levelled assumptions; M6 tests; conditional statements |
| Upstream churn (the contract is new) | Provisional pin; per-file staleness; weekly watch |
| Point-in-time deployment checks miss a later key or code change | DEP-1 lock at deploy; VER-3 since `b₀`; VER-8 per proof; NEP-591 global-contract check |
| Verus can't handle the real core | §18 proves the model at every size; Tier 1 and Tier 2 keep full value without M5 |
| Tool pins conflict (Verus rustc vs cargo-near rustc) | Path A adoption gate; the twin is the steady state |
| Everything except plain mode needs network access | CI-only jobs; plain mode works offline |

## 16. Open questions

1. **OQ-1:** *Done (2026-10-14).* Re-pinned to trust-framework `main`
   (`8635ca7`); only `README.md`'s `[source_hashes]` entry changed.
2. **OQ-2 (F-12):** *Answered in `3426c92` (R-8).*
3. **OQ-3 (F-13):** *Answered in `3426c92`: upstream CI (R-9).*
4. **OQ-4 (F-4):** Keep `MAX_ACTION_LEN = 2048` behind the RES-2 test, or
   lower it?
5. **OQ-5 (F-6):** Reorder `revoke_key` to check before removing, or keep it
   documented?
6. **OQ-6 (F-10d):** *Scoped per project:* CI runs `check-pin.sh` for
   near-approval only. Ironclaw's drift is unfixed.
7. **OQ-7:** CI access to private trust-framework (*resolved in M0*);
   runners with Docker (for reproducible builds) and an archival RPC (for
   VER-2/3) are still open, needed at M6 and M7.
8. **OQ-8:** Is separation by account id enough, or should the owner account
   be barred from holding agent or approver keys? MC-1 can flag it.
9. **OQ-9:** Admin events (F-8): *answered in `3426c92` (R-7); C-4 and the
   SH rows followed at M3 (F-15, done).*
10. **OQ-10 (F-17):** Are ML-DSA-65 access keys enabled on mainnet, and
    should the contract bound `MAX_ACTION_LEN` for them, refuse them at
    registration, or should DEP-1 forbid them? *Answered 2026-10-17: refused
    at registration (trust-framework PR #19), checked by SH-13.*

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
| `MC_Safety.{tla,cfg}` | TLC: accounts `{o, a1, a2}`, keys `{k1, k2}`, one storable payload `x` plus `Empty` and `TooLong`, `MaxPending = 2` (scaled), at most 3 requests. Symmetry on accounts and keys; a `VIEW` replaces registration ids by their rank among the ids the state refers to. The core only copies ids and the properties compare them only for order and equality, so this is a bisimulation quotient and the unbounded add/revoke cycles stay finite. |
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
| TLA-SAFE | `Inv` and `StepProperty` (HIST-1/2/3/7/8, TR-2, TR-3 as `□(Void ⇒ □Void)`) in every reachable state and step | TLC, `MC_Safety` | ≤ 3 requests, 3 accounts, 2 keys, 1 storable payload, `MaxPending = 2`, any number of add/revoke |
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
removes the small-scope step for the code, not for the TLA+ constants. §18
(Lean) removes it for the TLA+ model's safety properties.

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

**Implemented (2026-10-11).** C-2t: `tools/scripts/tla-facts.py` writes
`prolog/extracted/tla_facts.pl` from `ApprovalCore.tla`. MC-3:
`tools/scripts/run-mc3.sh` runs `MC_Graph.cfg` (edges, `-dump`) and
`MC_GraphTable.cfg` (each store with its rejected calls, via a `PrintT`
invariant under `VIEW store`), `verification/graph_export.pl` exports the
same universe from `step/4`, and `mc3.py` compares stores, rejected calls
and edges, printing each disagreeing `(store, call)`. It runs nightly (TLC
alone is ~400 MB of output). First full run (2026-10-11, universe in `MC_Graph.cfg`): 21,670 stores, 41,706 successful edges and 6,298,932 rejected calls on each side, all equal; the Prolog export takes ~40 min under Scryer. MC-2 uses one text format for stores and calls
across `mc2.rs`, `mc2.pl` and `mc3.py`.

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

---

## 18. Lean: the TLA+ model's safety at every size (M1.6)

Every other layer is bounded somewhere. Kani steps from states of ≤ 3
principals, requests, log entries and revocations (CUTOFF.md argues that is
enough, on paper). TLC explores ≤ 3 requests, 2 keys, 3 accounts and one
payload; Apalache's inductive step starts from ≤ 3 requests. The Lean layer
proves the TLA+ model's safety properties for **states of every size**, with
no bound on keys, accounts, requests, registrations or `MaxPending`. It
replaces the optional TLAPS step CUT-3 of the bounds plan: TLAPS has no
CI-friendly install and Lean is what near-proof-arena uses, so later arena
work shares the toolchain.

```text
real core ⊑ tla.rs ≡ ApprovalCore.tla ≡ Lean machine ⊨ Inv, StepProps, TR-1/2/3   (every size)
  Kani REF-1..4    REF-5        MC-4, REF-5L, LEAN-GUARD     LEAN-IND, LEAN-STEP, LEAN-TR
```

### 18.1 The model (`lean/`)

| File | Contents |
|---|---|
| `ApprovalLean/Machine.lean` | `ApprovalCore.tla` transcribed: one Lean definition per TLA+ operator (named in its doc comment), `err` (the error operators, guards in the core's order), `effect` (the actions), `step` (a rejected call stutters), `Next`, `run`, `Reach`, statuses, `pend`. |
| `ApprovalLean/Props.lean` | `ApprovalProps.tla` transcribed: `TypeOK`, INV-3..16, INV-5r, LEM-1/2, `Provenance`, `RidLive`, `Approvable` as the structure `Inv`; HIST-1/2/3/7/8/10 as `StepProps`. |
| `ApprovalLean/Lemmas.lean` | the principal map, `countIdx` and per-action field lemmas |
| `ApprovalLean/Inv/*.lean`, `Inductive.lean` | LEAN-IND: `inv_init`, one preservation theorem per action, `inv_next`, `inv_step`, `reach_inv` |
| `ApprovalLean/StepProps.lean` | LEAN-STEP: `stepProps_next`, `stepProps_step` |
| `ApprovalLean/Trace.lean` | LEAN-TR: `reach_run`, `tr1_provenance`, `tr2_decision_final`, `tr3_void_terminal`, `hist1_run`, `hist3_run`, `hist10_run` |
| `ApprovalLean/Guard.lean` | LEAN-GUARD: `guardOrder` (TLA+'s `GuardOrder`), `err_eq_firstFail`, `guards_order`, `err_mem_guardOrder`, `err_ne_logFull` |
| `ApprovalLean/Witness.lean` | LEAN-WIT: reachable approved, rejected, void, revived-still-void and pending-cap states (TR-5), by evaluation |
| `ApprovalLean/Delta.lean` | LEAN-DELTA (§18.6): `cstep`, `expect`/`protocol` transcribed over `Store`'s getters; `delta_refines` |
| `ApprovalLean/Text.lean`, `DeltaText.lean`, `Main.lean` | the `approval-lean` executable: `replay` (REF-5L), `graph` (MC-4), `guards`, `link` (LINK) |
| `Audit.lean`, `canary/`, `mutants/` | the hygiene gate (18.4) |

**Representation**, each difference fixed by the abstraction the replay and
graph tools apply before comparing:
- `principals` is a finite map (an association list with distinct keys,
  holding only registered principals); TLA+'s total function over `Keys` is
  `prin s k`, which answers `NoPrincipal` for an absent key. With no `Keys`
  constant, every theorem holds for **every key type**, finite or not;
  accounts and payloads are type parameters too.
- `revoked` is a duplicate-free list read as a set; `INV-15` counts it and
  the map by length (`TypeOK` carries the two distinctness facts).
- Request and log indices are 0-based (TLA+ sequences are 1-based).
- Counters are `Nat` and `MaxPending` is a parameter, as in TLA+ (A6): the
  theorems hold for every `MaxPending`, including the core's 16, so there is
  no "scaled to 2" caveat.

### 18.2 The link to the other layers

| # | Link | Check |
|---|---|---|
| L1 | The Lean machine transcribes the TLA+ model (**ASM-LEAN-TLA**) | **MC-4**: `approval-lean graph` exports the labelled reachable graph of the MC_Graph universe in `graph_export.pl`'s format and `mc3.py` compares it with TLC's: stores, every rejected call with its error, every edge. With MC-3 (Prolog = TLC) this makes the three semantics one graph. **REF-5L**: the real core's MC-2 traces replayed on `step`. **LEAN-GUARD**: the guard list is `GuardOrder`, equal to `tla_facts.pl` (C-2t). |
| L2 | The Lean theorems are about `Inv` and `StepProps` as TLA+ states them | `Props.lean` names each TLA+ conjunct; paired review; the spec mutants (18.4) |
| L3 | The TLA+ model is the code's | unchanged: REF-1..5 (§17.2) |

ASM-LEAN-TLA is the analogue of REF-5 for `tla.rs`: a transcription checked
by equality on a finite graph and on traces, not proved. Its level is high:
MC-4 compares every call in every state of a universe where every guard and
every error fires, and REF-5L runs the real core's own traces.

### 18.3 What is proved

| ID | Theorem | TLA+ counterpart and its bound |
|---|---|---|
| LEAN-IND | `inv_init : Inv cfg init`; `inv_next : Inv cfg s → Next cfg s s' → Inv cfg s'`; hence `reach_inv : Reach cfg s → Inv cfg s` | TLA-IND (Apalache, arrays ≤ 3, `MaxPending = 2`), TLA-SAFE's state invariants (TLC, ≤ 3 requests) |
| LEAN-STEP | `stepProps_next`, `stepProps_step`: every call from an `Inv` state satisfies HIST-1/2/3/7/8/10 | TLA-SAFE's `StepProperty`, TLA-IND's `StepProps` |
| LEAN-TR | over `run cfg s ops` for any `ops` from a reachable `s`: TR-2 (`tr2_decision_final`), TR-3 (`tr3_void_terminal`), TR-1 (`tr1_provenance`), HIST-1/3/10 transitively | TLC's finite depth |
| LEAN-GUARD | `err cfg s op = (firstFail (guards cfg s op)).getD .ok` and `(guards cfg s op).map Prod.fst = guardOrder op.kind` | C-2t, REF-1 |
| LEAN-WIT | witnesses for approved, rejected, void, revival and the pending cap | TLA-WIT |
| LEAN-DELTA | `delta_refines`: on every concrete store of every size with ids at their positions and counters below `u64::MAX`, `cstep`'s error is `err` and its calls land on `step` (§18.6) | none (REF-1..3 within the Kani bound) |

Net effect on assumptions: **ASM-TLA-SCOPE is needed only for liveness
(TLA-LIVE-1)**; the safety half is retired, given ASM-LEAN-TLA. ASM-MODEL
(the Kani bound on the code) is discharged by §18.6 rather than by
mechanising CUTOFF.md, which stays as the explanation of why small identity
domains suffice.

### 18.4 Hygiene gate

- `run-lean.sh build` fails on any `sorry` warning, and a scan of the
  sources (comments stripped) fails on `sorry`, `admit`, `axiom`,
  `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`.
- `run-lean.sh audit`: every headline theorem in `Audit.lean` depends only
  on `propext`, `Classical.choice` and `Quot.sound`.
- `canary/False.lean` and `canary/NotInv.lean` must fail to compile.
- `lean/mutants/*.patch` are the 15 TLA+ spec mutants ported to
  `Machine.lean`; each must break a proof (build), REF-5L or the guard
  check. Four of them (05, 06, 13, 14) also restate the `rfl` field lemma
  in `Lemmas.lean` that spells out the mutated effect, so that the kill
  comes from an invariant or step-property proof, not from that lemma.
  All 15 are killed by `Inv/*.lean`, `StepProps.lean` or `Guard.lean`
  (`lean/RESULTS.md`).
- No `Inv` conjunct is a step property, and no theorem assumes its
  conclusion: hypotheses are `Inv cfg s`, `Reach cfg s` or an error
  operator returning `ok`.

### 18.5 Running and CI

`tools/scripts/run-lean.sh near-approval [build|audit|canary|guards|replay|graph|link|mutants]`,
default all. `tools/scripts/get-lean.sh` fetches the Lean
release zip pinned in `tools/versions.env` (sha256-checked, no elan) and
checks it against `lean/lean-toolchain`. Core library only, no Mathlib.
CI job `lean` runs all of it on every PR: a clean build takes about 15 s,
the mutants about 3 min and MC-4 about 4 min (TLC's two runs and
`mc3.py`; the Lean export itself takes under a second). LINK takes about
a few seconds (14,310 views, the representatives of `Ident.allCls`, written
by the kani crate's `link_cases`, then checked by `approval-lean link`).

### 18.6 L2: the code steps like the model at every size

Chosen over mechanising CUTOFF.md (l2-oracle-proposal.md, 2026-10-17). The
state bound of ASM-MODEL is closed by three links, none of which bounds the
store:

```text
core step  =  expect/protocol  =  Lean cstep  ⊑  model step    (every store size)
          ST-8              LINK             LEAN-DELTA
```

| ID | What | How |
|---|---|---|
| ST-8 | The core's result and `Store` calls are `ghost::expect` and `ghost::protocol` on any store | Kani (§ ST-8): a `Sparse` holding the step's footprint at any keys and positions, all fields and counters free. A real store of any size restricted to that footprint is such a `Sparse`. |
| LINK | `expect`/`protocol` equal the Lean transcription `cstep` | `kani/src/link.rs` writes one representative footprint view per class of views (`norm::all_cls` through `norm::rep`: 14,310 views), runs `expect`, `protocol` and the real core on a `Sparse` holding exactly that view, and writes the error and calls; `approval-lean link` requires the views to be exactly Lean's `Ident.allCls.map Ident.rep` and recomputes each with `cstep`, which must agree on the error and every call. That this finite domain covers every view is proved (§18.6.1). |
| LEAN-DELTA | `cstep` refines the model's `step` | `Delta.lean`, `delta_refines`: for every `CStore` of any size whose request ids equal their positions (INV-1) and whose counters are below `u64::MAX` (A6), `cstep`'s error equals `err` on `α s`, and applying its calls gives `step`'s state, up to map equality of principals and set equality of revocations. Axiom audit as 18.4. |

`cstep` reads the store only through `Rd`, the getters `Store` offers
(`principal`, `request`, the three counters, the owner), so LINK can feed
it the same view the Rust side gets. Block times are not modelled (A7); the
revocation time and the request and decision times are checked by RT-TIME.
With L1 (LEAN-IND, LEAN-STEP, LEAN-TR), the safety properties then hold for
the code at every state size, given ASM-IDENT, ASM-NU, ASM-LEAN-TLA and the
tool assumptions.

#### 18.6.1 LINK's domain, mechanised

LINK compares Rust and Lean on finitely many views; the chain needs them
equal on every view. Until 2026-10-19 that rested on an argument (the
domain realises every equality pattern and counter relation the code
observes). It is now proved on both sides against one shared normal form:

- `cls v op` maps a footprint view (any accounts, keys, payloads, counters)
  to its class: the equalities and comparisons the step's guards can see
  (caller = owner, predecessor = signer, the key's role and account, the
  request's state, `activeFrom ≤ id`, `pending` at the cap or at 0, the
  counters at `u64::MAX`, the action's kind and whether it is the request's).
- `rep c` is the class's representative view and call: accounts `o`, `a1`,
  `a2`, keys `k0`, `k1`, payloads `t1`, `t2`, and counters at distinct
  values (1000, 2000, ..., 10000) away from every constant the code uses.
- `sub v op` is a table from the representative's values to `v`'s:
  identities and payloads by value, each counter `d` also at `d ± 1`
  (saturating). `out` applies it to the representative's calls.

| ID | What | How |
|---|---|---|
| LEAN-COVER | `cstep v op = (sub v op).out (cstep (rep (cls v op)))` and `cls v op ∈ allCls`, for every view of any `A`, `K`, `P` whose request at `i` has id `i` and a payload action | `Ident.cover` (all five operations by case analysis on the guards), `Ident.cls_mem`; `wfv_of_store` derives the premise from `WF` and `TypeOK`, so it holds on every store LEAN-DELTA covers whose abstraction is reachable. |
| LEAN-FRAME | `cstep` reads only the owner, the call key's principal, the request at `i`, its key's principal and the counters it compares | `Ident.frame` |
| LEAN-REN | `cstep` commutes with injective renaming of accounts, keys and payloads | `Ident.rename` |
| K-LINK-T | The same equation for `expect`/`protocol`: errors equal, calls equal after `sub` (and the times, which only Rust has) | `h_link_t_{add,revoke,request,approve,reject}` and the `_empty`/`_long` action instances: a footprint `Sparse` with any `u8` accounts and keys, any counters, positions and times (`norm::link_t`) |
| ST-8W | ST-8 over enough accounts for every footprint | `h_oracle_approve`, `h_oracle_reject` with `src::Wide` (8 accounts; keys already 4) |

Chain for one step on a real store `s` (identities `AccountId`/`PublicKey`):
the core on `s` equals the core on its footprint (the core reaches state
only through `Store`); rename the footprint injectively into the harness
identities (ASM-IDENT parametricity, ST-8W makes the range large enough);
ST-8 gives `expect`/`protocol` there; K-LINK-T moves to the representative;
LINK equates Rust and Lean on it; LEAN-COVER moves back; LEAN-REN and
LEAN-FRAME return to `s`'s identities and full store; LEAN-DELTA reaches the
model. Every link is a Kani or Lean proof, or LINK's exhaustive check.

What stays trusted: ASM-IDENT (the core is generic in `A` and `K` and uses
them only through `Clone` and `PartialEq`, so it commutes with injective
renaming; ST-7 checks the `PartialEq` half), and ASM-NU (the Rust and Lean
transcriptions of `cls`, `rep` and `sub` agree; LINK's set check pins `rep`
exactly). Actions on the Rust side stay the harness alphabet plus `""` and a
2,049-byte string, as everywhere in the Kani layer (ASM-STRLEN for M5).

Mutation: a class that reads `activeFrom < id`, a representative counter
that collides with another's `± 1`, and a transport row with the wrong
account each break `cover`; a wrong counter row or class in `norm.rs` fails
`h_link_t` in plain mode.
