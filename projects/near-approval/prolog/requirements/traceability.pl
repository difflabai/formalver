%% traceability.pl -- Requirements -> properties (strategy 5.12) and the property list
%%
%%   property(Id, Layer, Text)   every property in status.toml (layer = its primary
%%                               technique), plus the strategy 17.5 IDs C-2t and MC-3
%%   verified_by(Req, Property)  strategy 5.12, plus the rows marked "M4 addition"
%%                               for properties added with trust-framework PR #15
%%                               (17.6) and M1.5 (17.3), and for D17
%%
%% property/3 rows were transcribed from status.toml (metadata, not code); C-9
%% re-reads status.toml at check time, so drift is caught.

:- module(traceability, [
    property/3,
    verified_by/2,
    status_pending_id/1
]).

:- use_module(library(lists)).

%%% ========================================================
%%% verified_by/2: strategy 5.12
%%% ========================================================

verified_by(Req, P) :- trace_row(Req, Ps), member(P, Ps).

trace_row('R1',  ['TX-3', 'TX-4', 'TR-1', 'SH-1', 'RT-KEY']).
trace_row('R2',  ['SH-4', 'SH-6', 'C-4', 'RT-TRACE']).
trace_row('R3',  ['TX-3', 'TX-5', 'INV-5', 'INV-6', 'TR-1', 'RT-KEY', 'RT-RELAY']).
trace_row('R4',  ['SH-5', 'SH-6', 'C-4', 'RT-TRACE']).
trace_row('R5',  ['RD-1', 'RD-5', 'HIST-5', 'SH-7', 'SH-8', 'VER-1']).
trace_row('R6',  ['RD-2', 'RD-3', 'RD-4', 'RD-5', 'SH-7', 'RES-3', 'VER-5']).
% "D1 key+account identity, D2 caller = signer" share one row in 5.12.
trace_row('D1',  ['TX-3', 'INV-8', 'RT-KEY', 'RT-RELAY', 'RT-SELFACCT', 'RT-METATX', 'RT-FCKEY', 'DEP-1', 'VER-8']).
trace_row('D2',  ['TX-3', 'INV-8', 'RT-KEY', 'RT-RELAY', 'RT-SELFACCT', 'RT-METATX', 'RT-FCKEY', 'DEP-1', 'VER-8']).
trace_row('D3',  ['TX-1', 'TX-2', 'TX-6', 'HIST-6', 'HIST-7', 'SH-1']).
trace_row('D4',  ['INV-0', 'INV-6', 'C-1']).
trace_row('D5',  ['INV-5']).
trace_row('D6',  ['TX-5', 'HIST-2', 'TR-2']).
trace_row('D7',  ['TR-3', 'HIST-8', 'INV-8', 'LEM-4', 'RD-7']).
trace_row('D8',  ['INV-1', 'INV-3', 'INV-4', 'INV-7', 'LEM-1', 'LEM-2', 'HIST-3', 'HIST-4', 'RD-2', 'RD-4']).
trace_row('D9',  ['INV-2', 'INV-9', 'ROB-3', 'TR-6', 'RES-1', 'RES-2', 'SH-13']).
trace_row('D10', ['TX-5', 'TR-1']).
% D11 amended (decision D17): "no upgrade, expiry or threshold".
trace_row('D11', ['SH-11', 'SH-12', 'C-1', 'C-6']).
trace_row('D12', ['TX-0', 'ROB-1', 'ROB-2', 'ROB-4', 'ST-1', 'ST-2', 'ST-3', 'ST-4', 'ST-5', 'ST-6', 'ST-7', 'ST-8', 'SH-2', 'SH-3', 'RD-6', 'LEM-3']).
trace_row('D13', ['INV-10', 'TR-4', 'RT-TIME']).
trace_row('D14', ['RT-CODEHASH', 'RT-RESET', 'RT-TRACE', 'DEP-1', 'VER-2', 'VER-3', 'VER-6']).
trace_row('D15', ['TR-5', 'MC-1', 'MC-2', 'C-2', 'C-3', 'C-5', 'C-6', 'C-7', 'C-8', 'C-9', 'C-10']).
trace_row('D16', ['VER-1', 'VER-4', 'VER-5', 'VER-7', 'VER-8']).

%%% M4 additions (not in the 5.12 table, which predates PR #15 and M1.5)
% D17 rejection: TX-7 (reject contract), HIST-9 (Rejected terminal), INV-13 (one
% decision), INV-5/INV-6 for rejections, TR-2 (decided at most once), RD-7 (status).
trace_row('D17', ['TX-7', 'HIST-9', 'INV-13', 'INV-5', 'INV-6', 'TR-2', 'RD-7', 'TLA-LIVE-2', 'SH-6']).
% D7 recorded revocation (registration ids and revocation times, PR #15).
trace_row('D7',  ['INV-11', 'INV-12', 'INV-14', 'INV-15', 'INV-16', 'HIST-10', 'TR-7', 'RD-8']).
% D6/D7/D8/D9 at every depth in the TLA+ model; D9 "stays approvable" (TLA-LIVE).
trace_row('D6',  ['TLA-SAFE', 'TLA-IND']).
trace_row('D7',  ['TLA-SAFE', 'TLA-IND']).
trace_row('D9',  ['TLA-LIVE-1', 'TLA-LIVE-2']).
% D15: the refinement link and the cross-model checks (strategy 17.2, 17.5).
trace_row('D15', ['TLA-WIT', 'REF-1', 'REF-2', 'REF-3', 'REF-4', 'REF-5', 'C-2t', 'MC-3']).

% D15: the cutoff argument that makes the bounded Kani proofs size-independent
% (kani/CUTOFF.md) and the loop-bound derivation (tools/scripts/kani-loops.py).
trace_row('D15', ['CUT-1', 'CUT-2', 'U-1']).

% Strategy 18 (Lean): D6/D7/D8/D9 and TR-1/2/3 at every size, and the Lean
% machine's links to the code and the other models (D15).
trace_row('D6',  ['LEAN-IND', 'LEAN-STEP', 'LEAN-TR']).
trace_row('D7',  ['LEAN-IND', 'LEAN-STEP', 'LEAN-TR']).
trace_row('D8',  ['LEAN-IND', 'LEAN-STEP']).
trace_row('D9',  ['LEAN-IND']).
trace_row('D15', ['LEAN-GUARD', 'LEAN-WIT', 'REF-5L', 'MC-4']).
% Strategy 18.6 (L2): the code steps like the model at every store size.
trace_row('D12', ['LEAN-DELTA', 'LINK']).

%%% IDs in this file that status.toml does not have yet (decision 'C-9-new-ids').
status_pending_id(_) :- fail.

%%% ========================================================
%%% property/3 (from status.toml)
%%% ========================================================

% [modules.requirements]
property('C-1', prolog, "Authority matrix: one authority per change method; owner/agent/approver method sets disjoint; no key can both request and approve").
property('C-2', prolog, "Guard table: every ApprovalError produced by >=1 guard; specified precedence equals generated code_precedence/2").
property('C-3', prolog, "Error messages pairwise distinct and substring-free").
property('C-4', prolog, "Each event from exactly one core operation (key_added from add_principal via add_agent and add_approver; key_revoked, approval_requested, action_approved, action_rejected); authority/proof-changing methods emit or carry accepted_risk (new); only change methods emit").
property('C-5', prolog, "Generated constants equal requirement constants; DEFAULT_PAGE_SIZE <= MAX_PAGE_SIZE; MAX_PENDING_PER_KEY >= 1; MAX_ACTION_LEN within RES-2 bound").
property('C-6', prolog, "Generated API surface equals the requirements API table: #[near] wasm exports = method/3 names, other exports only near-sdk's, ABI kind and modifiers match each method's kind and authority").
property('C-7', prolog, "Traceability both ways: every requirement has >=1 property; every property traces to a requirement or threat").
property('C-8', prolog, "Every threat has mitigated_by or accepted_risk").
property('C-9', prolog, "Property and assumption IDs in status.toml equal those in traceability.pl").
property('C-10', prolog, "Warn when a verified* property depends on an assumption with level below high whose check has not passed").
property('MC-1', prolog, "Bounded model check of reference step/4 at depth 6 with real constants: no INV, separation-of-duties, double-approval, pending-count or revival violation; reaches approved and void states and every error except both LogFull and TooManyPending; MC-1s (max_pending=2, max_u=2) also reaches TooManyPending and request LogFull; state counts >= mc1_state_floor").
property('MC-2', prolog, "Generated traces replayed on the real core, on spec.rs and (RT-TRACE) on the wasm; all agree").
% [modules.core_state_machine]
property('TX-0', verus, "Atomic failure: Err => state unchanged; no Store mutator on failure except remove_principal of an absent key (F-6, no-op)").
property('TX-1', verus, "add_principal: Ok(principal) <=> caller = owner, key unregistered and G != MAXU; errors NotOwner, KeyAlreadyRegistered, LogFull; P' = P[k -> (acct, role, G, #R, 0)], G' = G + 1").
property('TX-2', verus, "revoke_key: Ok(P(k)) <=> caller = owner and key registered; errors NotOwner, KeyNotRegistered; P' = P minus k, V' = V[P(k).reg -> t]").
property('TX-3', verus, "authenticate: Ok <=> predecessor = signer and key registered to signer with role; errors IndirectCall, UnknownKey, WrongRole, KeyAccountMismatch; read-only").
property('TX-4', verus, "request_action: exact result, error order (auth, EmptyAction, ActionTooLong, TooManyPending, LogFull), appended request recording the caller's registration id, caller key pend+1").
property('TX-5', verus, "approve: exact result, error order (auth, RequestNotFound, AlreadyApproved, AlreadyRejected, AgentRevoked, ActionMismatch, SelfApproval, LogFull), approval recorded with the approver's registration id, log appended, agent key pend-1, proof = approval(s', i)").
property('TX-7', verus, "reject: exact result, error order (auth, RequestNotFound, AlreadyApproved, AlreadyRejected, AgentRevoked, SelfApproval), rejection recorded with the approver's registration id, agent key pend-1, log unchanged; Ok(R'[i])").
property('TX-6', kani, "Owner never changes; owner checks compare the caller account passed by the shell (predecessor: SH-1)").
property('INV-0', verus, "Registry is a function: one registration and role per key (MemStore has no duplicate keys)").
property('INV-1', verus, "Dense request ids: R[i].id = i").
property('INV-2', verus, "Stored actions are 1..=2048 bytes").
property('INV-3', verus, "Log -> request: L[j] < #R and R[L[j]] approved with index j").
property('INV-4', verus, "Request -> log: approved R[i] has index < #L and L[index] = i").
property('INV-5', verus, "Separation of duties: approver account != agent account, on every approval and rejection").
property('INV-6', verus, "Approver key != agent key on every approval and rejection").
property('INV-7', verus, "Registration bound: P(k).active_from <= #R").
property('INV-8', verus, "Registration provenance: R[i].ak = k and i >= P(k).active_from => R[i].aa = P(k).account, role Agent and R[i].agent_registration_id = P(k).registration_id").
property('INV-9', verus, "Pending count: P(k).pending equals undecided (neither approved nor rejected) requests of k under its registration, <= 16 (0 for approvers); the cap bound is stepped in h_raw_request").
property('INV-10', verus, "Time order (non-decreasing time inputs): approved_at and rejected_at >= requested_at component-wise").
property('INV-11', verus, "Live registration ids are issued (< G), pairwise distinct and not revoked").
property('INV-12', verus, "Revoked registration ids are issued (< G) and each is revoked once (insert_revocation's write-once law holds)").
property('INV-13', verus, "At most one decision per request: never both approved and rejected").
property('INV-14', verus, "Recorded registration ids (request agent, approver, rejecter) are issued (< G)").
property('INV-15', verus, "Registration accounting: #P + #V = G, so with INV-11/12 every issued registration is exactly one of live or revoked").
property('INV-16', verus, "Registration binding: a live registration id recorded on a request or decision belongs to the key, account and role it was recorded with").
property('LEM-1', verus, "Approval log has no duplicates").
property('LEM-2', verus, "#L = number of approved requests <= #R").
property('LEM-3', verus, "An unapproved request exists => #L < #R <= MAXU, so approve's LogFull is unreachable (F-7)").
property('LEM-4', verus, "Under INV-8, liveness reduces to active_from <= id; role/account checks are redundant (F-14, the 2 equivalent mutants)").
property('HIST-1', verus, "Request content immutable and never removed").
property('HIST-2', verus, "Decisions immutable once recorded: approvals and rejections").
property('HIST-3', verus, "Approval log append-only").
property('HIST-4', verus, "#R grows by 1 exactly on a successful request, #L by 1 exactly on a successful approval; otherwise unchanged").
property('HIST-5', verus, "Proof stability: a published proof never changes").
property('HIST-6', verus, "Registry discipline: owner fixed; P changes only by owner Add/Revoke or the pending field on request/approve/reject").
property('HIST-7', kani, "Owner operations never change requests or the log, and reject never changes the log, from any state").
property('HIST-8', verus, "Void is terminal").
property('HIST-9', verus, "Rejected is terminal").
property('HIST-10', verus, "Registrations and revocations: G grows by 1 exactly on a successful Add, V gains one entry exactly on a successful Revoke, and a recorded revocation never changes").
property('TR-1', verus, "Provenance: every proof has a prior successful request by a registered agent key and a successful approval restating the action by a registered approver key of a different account, with the agent registration continuous in between; the proof's registration ids are the registrations in force at request and approval").
property('TR-2', verus, "Each request decided (approved or rejected) at most once in any trace").
property('TR-3', verus, "Durable revocation: a request whose agent registration is revoked while pending is never approved, even after re-registration").
property('TR-4', verus, "Approval times non-decreasing along the log").
property('TR-5', kani, "Non-vacuity: approved, rejected and void states reachable; every error reachable except approve LogFull; request LogFull only at #R = MAXU").
property('TR-6', verus, "Agent storage bound as a potential: Phi = sum over agent keys of (16 - pending) >= 0 drops by 1 per successful request and rises only on a successful approval or rejection or agent Add").
property('TR-7', verus, "Revocation record: V lists exactly the successful Revokes, in order, each with the registration id it removed (as issued, fresh, by Add) and its time").
property('RD-1', verus, "approval(s,i) = Some(proof(R[i])) iff approved; None for pending, void or unknown").
property('RD-2', verus, "Exact page: approvals(f,l) = proofs of L[f..min(f saturating_add min(l,100), #L)], no drops").
property('RD-3', kani, "Page arithmetic over any u64 (from, limit, count): no overflow; reads only approval_count, approved_request_id(j) in the page and request(id) for returned ids; no writes").
property('RD-4', verus, "Client loop (stop on empty page or from >= count) enumerates the log exactly once, in order").
property('RD-5', verus, "Per-request and paged views agree; proof findable by request_id or approval_index").
property('RD-6', kani, "Core reads are pure (Window store panics on writes); every get_* takes &self").
property('RD-7', verus, "request_status = Approved / Rejected / Pending (live) / Void; None for unknown ids").
property('RD-8', verus, "proof_revocations(proof) = (V(agent registration), V(approver registration)); under Inv each is None exactly when that registration is still the key's current one").
property('ROB-1', kani, "No panics, overflows or OOB indexing for any arguments and any MemStore within the bounds (beyond: ASM-MODEL), including non-Inv states").
property('ROB-2', kani, "LogFull guards: count = MAXU with all earlier guards passing => Err(LogFull), no writes, before the shell's += 1 (which would panic under overflow-checks); approve's case needs a non-Inv state").
property('ROB-3', kani, "Action length boundaries in bytes: 0, 1 (a space), 2048, 2049 and a multi-byte 2050").
property('ROB-4', kani, "Bounded work: <= 4 Store reads and <= 3 writes per mutator; approvals <= 2*min(l,100)+1 reads").
property('ST-1', kani, "Store laws for MemStore and Sparse (map/sequence semantics; removing an absent key is a no-op)").
property('ST-2', kani, "Store protocol: exact mutator call sequence per op; makes contract-store differences from MemStore unreachable").
property('ST-3', kani, "Sparse (transliteration of the contract Store impl) refines MemStore").
property('ST-8', kani, "Store protocol at any store size (K-ORACLE): approve and reject on a Sparse with the footprint at any keys and positions, every field and counter free, return exactly expect() and make exactly the protocol() calls").
% [modules.tla_model]
property('TLA-SAFE', tla, "TLC: Inv (INV-3..9, INV-11..16, LEM-1/2, TR-1 provenance, RidLive, Approvable) in every reachable state and StepProperty (HIST-1/2/3/7/8/9/10, TR-2, TR-3) on every step, any interleaving of all calls by all parties").
property('TLA-IND', tla, "Apalache: Init => Inv, and Inv /\\ Next => Inv' /\\ StepProps from any state with <= 3 requests, integers unbounded, MaxPending scaled to 2: Inv and the step properties hold at every depth").
property('TLA-LIVE-1', tla, "Under weak fairness of approvers, a request whose eligible approver eventually always exists never stays pending (ends approved, rejected or void); fails without fairness (non-vacuity)").
property('TLA-LIVE-2', tla, "Approvable: every Approver key of another account can approve or reject a pending request (no accepted request is stuck in the core)").
property('TLA-WIT', tla, "Non-vacuity: approved, rejected, void, revival-attempt and pending-cap states are reachable in TLC; IndInit holds full states with approved, rejected and void requests and a revocation").
property('REF-1', kani, "Guard exactness (A1): the core's error equals the TLA+ error operator on alpha(pre); Ok exactly when the TLA+ action is enabled").
property('REF-2', kani, "Effect exactness (A2): on Ok, alpha(post) is the TLA+ action's post-state").
property('REF-3', kani, "Rejected calls stutter (A3): on Err, alpha(post) = alpha(pre)").
property('REF-4', kani, "Time irrelevance (A7): tla.rs reads no BlockTime, so REF-1/2 hold for every block time; payload classes (A5) via h_ref_toolong").
property('CUT-1', kani, "Footprint (kani/CUTOFF.md): each call reads and writes at most the keys, request positions, log slots and revocation records of its row; tracking is transparent").
property('CUT-2', review, "Cutoff: given CUT-1, harness state bounds (CAP_P, CAP_R, CAP_V) are sufficient for REF-1..3 at every size, except E1 (pending at MAXP) and E2 (counters at u64::MAX), which raw and Sparse harnesses cover; request/approve LogFull pending M2 Sparse").
property('U-1', review, "Every loop in every harness's goto program has a bound derived from a constant, and no reachable loop needs more than its harness unwind").
property('LEAN-IND', lean, "Lean: Init => Inv and Inv /\\ Next => Inv' for states of every size, every MaxPending, any key, account and payload types; Inv holds in every reachable state").
property('LEAN-STEP', lean, "Lean: every call from an Inv state satisfies StepProps (HIST-1/2/3/7/8/9/10), at every size").
property('LEAN-TR', lean, "Lean: over every run from a reachable state, decisions are final (TR-2), Void is terminal (TR-3), request content, log prefix, registration counter and revocations only grow; TR-1 provenance").
property('LEAN-GUARD', lean, "Lean: each error operator returns the first failing guard of a list whose codes are TLA+'s GuardOrder; LogFull never returned").
property('LEAN-WIT', lean, "Non-vacuity: approved, rejected, void, revived-still-void and pending-cap states reachable in the Lean machine").
property('REF-5L', plain, "The real core's MC-2 traces replayed on the Lean machine: every result and post-store equal").
property('LEAN-DELTA', lean, "Lean: on every concrete store of every size with ids at their positions and counters below u64::MAX, the transcribed expect/protocol step refines the model's step").
property('LINK', lean, "Rust expect/protocol equal the Lean cstep on every footprint view of a bounded domain covering every observable identity pattern and counter boundary").
property('MC-4', lean, "Graph equivalence: the Lean machine and TLC export the full labelled reachable graph of the MC_Graph universe; stores, rejected calls and edges are equal").
property('REF-5', plain, "Trace validation: 60 x 80-call core traces equal tla.rs on every step, and TLC accepts each as a behaviour of ApprovalCore.tla (>= 5 revival attempts, >= 20 rejections and revocations)").
% [modules.contract_store]
property('ST-4', difftest, "Real ApprovalContract store refines MemStore over 10k x 50 random ops, persisted and reloaded every step").
property('ST-5', unit, "Storage prefixes p/r/a/v pairwise distinct, prefix-free and distinct from STATE; after every random step the keys are exactly STATE and prefix ++ borsh(key) for the entries alpha lists").
property('ST-6', unit, "Golden Borsh bytes for STATE and one entry of each map (ed25519 and secp256k1 principals; pending, approved, rejected requests; log; revocation); layout changes flagged storage-breaking").
property('ST-7', unit, "Identity equality: == on near-sdk AccountId and PublicKey equals Borsh-byte equality, is reflexive and symmetric, and survives clone and a Borsh round trip (edge identities and 200k random pairs); the checked half of ASM-IDENT").
% [modules.contract_shell]
property('SH-1', unit, "Env mapping (caller, now); add_agent/add_approver pass the right role; owner methods pass the predecessor").
property('SH-2', difftest, "Exactly one core transition per change call and no other writes").
property('SH-3', unit, "Core Err(e) panics with exactly e.as_str() (catch_unwind) and logs nothing").
property('SH-4', unit, "approval_requested: exactly one NEP-297 line with RequestView(r), status pending; emitted only after Ok").
property('SH-5', unit, "action_approved: exactly one line; data = return value = get_approval(i) at approval (revocation fields null); later get_approval differs only in agent_key_revoked_at / approver_key_revoked_at").
property('SH-6', unit, "Each change method logs exactly its one event (key_added, key_revoked, approval_requested, action_approved, action_rejected = returned RejectionView); new, views and failed calls log nothing").
property('SH-7', unit, "View mapping: get_approval(s) with proof_revocations, get_approvals defaults (0, 50); get_request None past #R else every field of R[i] plus request_status; get_rejection; get_revocation = V(g); get_principal None if unregistered else account, role, registration_id, pending; get_owner; counts").
property('SH-8', unit, "JSON shape: README field names of every view and event payload (incl. revocation fields, RejectionView, KeyView, KeyRevokedView, BlockTimeView), U64 strings for *_ns, numbers for ids and heights, {} or null fields give defaults, whole-args null fails (wasm wrappers: sandbox), lossless conversions").
property('SH-9', sandbox, "Init once, only from C; methods fail before init; post-init state is Init(owner)").
property('SH-10', sandbox, "All 16 #[near] methods (and contract_source_metadata) called with 1 yocto via full-access keys (new on a fresh deployment): change methods and new fail with the non-payable panic; view outcomes recorded").
property('SH-11', 'wasm-check', "Function exports exactly the 16 #[near] methods + contract_source_metadata + __contract_abi (embedded by cargo-near); the only non-function export is memory; no Store, upgrade or owner-transfer export (wasm-surface.expected)").
property('SH-13', unit, "add_agent/add_approver refuse ML-DSA-65 keys after the owner check and before the core's guards, with exactly UNSUPPORTED_KEY_TYPE and no log (F-17)").
property('SH-12', 'wasm-check', "No promise_*, deploy, delete, add-key, global-contract or transfer imports (exact import set in wasm-surface.expected); only ST-5 storage keys written").
property('RES-1', unit, "Storage growth per op (add, revoke, request, approve, reject) bounded from the Borsh layout and metered by VMLogic; measured on-chain; <= 16 x B_req lockable per agent key without an approver").
property('RES-2', unit, "Worst-case approval_requested, action_approved and action_rejected lines (2048 escaped control bytes, 64-char accounts, ed25519/secp256k1 keys, max u64s) fit 16384 B (F-4); ML-DSA-65 keys, which would not (F-17), are refused at registration (SH-13)").
property('RES-3', sandbox, "get_approvals(0,100) over max-size proofs stays under view gas and 4 MiB return").
% [modules.runtime_assumptions]
property('RT-KEY', sandbox, "FC key of account a arrives as signer = predecessor = a with signer_pk = key; unregistered and cross-account keys rejected").
property('RT-RELAY', sandbox, "Calls through a third-party relay contract fail IndirectCall").
property('RT-SELFACCT', sandbox, "A contract on the signer's own account calling C succeeds (documents F-9)").
property('RT-METATX', sandbox, "NEP-366 delegate action outcome recorded (expected IndirectCall)").
property('RT-FCKEY', sandbox, "Agent FC key scoped to request_action cannot call approve or add_agent: InvalidAccessKeyError(MethodNameMismatch), not a contract panic").
property('RT-REVERT', sandbox, "Forced failures (LackBalanceForState, gas-starved after emit) leave state and views unchanged; record whether logs survive").
property('RT-BATCH', sandbox, "Batched [request_action(a), request_action('')] signed by a full-access registered agent key fails at action 1 and leaves counters unchanged; record whether the first event appears").
property('RT-RESET', sandbox, "Delete + recreate C resets counters; VER-3 detects it (VER-6 only heuristically)").
property('RT-SPOOF', sandbox, "Forged EVENT_JSON from a spoofer contract rejected by the VER-1 executor_id rule").
property('RT-TIME', sandbox, "Stored request/approval/rejection times equal the block their receipt ran in; heights strictly increase and timestamps never decrease across receipts on C").
property('RT-CODEHASH', sandbox, "Wasm under test is the reproducible build; record sha256 (hex) and NEAR code_hash (base58)").
property('RT-TRACE', sandbox, "Prolog traces + 200 random sequences replayed on the reproducible wasm equal spec.rs: results, exact messages, logs, views").
% [modules.deployment]
property('DEP-1', 'deploy-check', "Code hash = reproducible build, not a global contract referenced by account id; locked at deploy (deploy + new + full-access key deletion in one tx); owner is multisig/DAO; registered keys (rebuilt from an indexer) are FC keys scoped to C; balance buffer").
property('VER-1', prolog, "Accept proofs only from get_approval at final, or action_approved logs of successful receipts with executor_id = C in final blocks").
property('VER-2', 'deploy-check', "code_hash(C) = expected at the proof's block (archival) and now").
property('VER-3', 'deploy-check', "No full-access key on C since b0, or an indexer scan finds no DeployContract/UseGlobalContract/AddKey/DeleteAccount").
property('VER-4', prolog, "Check action and both accounts against expectations; approver against the verifier's own allowlist").
property('VER-5', prolog, "Enumerate with the RD-4 loop at one block_id").
property('VER-6', prolog, "Counter decrease or code-hash change invalidates cached proofs").
property('VER-7', prolog, "Executors deduplicate on (C, request_id) and enforce a maximum approval age").
property('VER-8', 'deploy-check', "Per proof: archival view_access_key for the agent key at the request block and the approver key at the approval block both show a function-call permission with receiver C and the DEP-1 method names (closes F-9)").
% [strategy 17.5] -- not yet in status.toml
property('C-2t', prolog, "Guard table across models: TLA+ GuardOrder = guard/4 order = code_precedence/2").
property('MC-3', prolog, "Graph equivalence: Prolog step/4 and TLC export the full labelled reachable graph of one small universe; state and edge sets are equal").
