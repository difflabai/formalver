%% approval_req.pl -- Requirements of the NEAR approval contract (M4)
%%
%% Written ONLY from requirements text (ASM-SPEC independence rule):
%%   * projects/near-approval/strategy.md: Target, sections 1, 2, 3, 4, 5.0-5.12, 17.6
%%   * source-mirror/contracts/approval/README.md (upstream README at pin 3426c92)
%% No Rust, Kani or TLA+ source was read to write this file.
%%
%% Readings the text leaves open are marked `% AMBIGUOUS:`.
%% Decisions taken by the project owner are decision/2 facts.
%%
%% Exported facts:
%%   requirement(Id, Text)
%%   method(Name, Kind, Authority)          Kind: init | change | view
%%                                          Authority: contract | owner | agent | approver | anyone
%%   method_op(Method, CoreOp)              which core operation a change method drives
%%   changes(Method, What)                  authority | proof | none
%%   emits(Method, Event)
%%   approval_error(Name)                           the ApprovalError variants named in the text
%%   guard(Op, Order, Error, Condition)     Error is raised when Condition does NOT hold;
%%                                          the first failing guard (lowest Order) wins
%%   error_message(Error, Message)          only where the text states a message
%%   constant(Name, Value)
%%   decision(Id, Text)

:- module(approval_req, [
    requirement/2,
    method/3,
    method_op/2,
    changes/2,
    emits/2,
    approval_error/1,
    guard/4,
    guard_sequence/2,
    core_op/1,
    error_message/2,
    constant/2,
    decision/2
]).

:- use_module(library(lists)).
:- use_module(library(pairs)).

%%% ========================================================
%%% Requirements (strategy Target, section 1, section 5.12; README)
%%% ========================================================

requirement('R1', "An agent requests an action with its own registered agent key (request_action).").
requirement('R2', "A successful request emits the NEP-297 event approval_requested.").
requirement('R3', "An approver approves a request with its own registered approver key (approve).").
requirement('R4', "A successful approval emits the NEP-297 event action_approved.").
requirement('R5', "The approval proof for a specific request is publicly readable (get_approval(request_id)) and equals the recorded proof.").
requirement('R6', "All approvals are publicly readable as a paged log in approval order (get_approvals(from_index, limit)); the documented client loop yields every proof exactly once.").

requirement('D1', "Identity is the signing key: a call is accepted only if signer_account_pk is registered for the method's role and bound to signer_account_id.").
requirement('D2', "No relaying: predecessor_account_id must equal signer_account_id (the caller is the signer).").
requirement('D3', "The owner, fixed at init, manages keys: add_agent, add_approver and revoke_key are owner-only; owner checks use the predecessor.").
requirement('D4', "Each key is registered at most once at a time, with exactly one role (agent or approver), bound to exactly one account.").
requirement('D5', "Separation of duties: an approver cannot approve or reject a request made by an agent key bound to the same account.").
requirement('D6', "A request is decided (approved or rejected) at most once; decided requests are never modified.").
requirement('D7', "Durable revocation: revoke_key removes a key immediately and records when, against that registration; requests pending under the revoked registration become void and stay void even if the key is registered again; proofs report later revocations of either key.").
requirement('D8', "Append-only paged log: requests and proofs are never changed or removed; request ids are dense; the approval log is append-only in approval order; pages are clamped to 100 (default 50); clients page until an empty page.").
requirement('D9', "Bounded storage: an action is 1 to 2048 bytes; an agent key holds at most 16 pending requests; approving or rejecting frees a slot; every accepted request stays approvable within runtime log limits.").
requirement('D10', "An approval commits to content: approve(request_id, action) fails unless action equals the stored action.").
% D11 amended by decision D17 (Gabe): rejection is now a feature, so D11 no longer lists it.
% The README also lists "no ownership transfer" next to "no upgrade"; included here.
requirement('D11', "No upgrade, ownership transfer, expiry or M-of-N threshold.").
requirement('D12', "Atomic, bounded execution: a call the core rejects writes nothing and emits nothing; every guard runs before any write; the core never panics; each mutator does bounded work.").
requirement('D13', "Timestamps (block height and ns) are recorded on requests and decisions and are ordered along the log.").
requirement('D14', "The deployed artifact is the reproducible build of the verified source, locked at deploy.").
requirement('D15', "Verification hygiene: specs are independent of the code (ASM-SPEC) and tools are sound and checked by canaries and mutants (ASM-TOOLS).").
requirement('D16', "Verifier and executor discipline: proofs are read at finality from the expected contract, events are hints, executors deduplicate and bound age.").
% D17: new requirement approved by Gabe (M4 plan, decision 1), after trust-framework PR #15.
requirement('D17', "An Approver key of another account (not the agent's account) may reject a pending request; rejection is terminal, frees the agent key's pending slot, emits action_rejected, and a rejected request is never approvable.").

%%% ========================================================
%%% API (README "API" table; 16 methods at 3426c92)
%%% ========================================================

% AMBIGUOUS: the task's authority domain is owner|agent|approver|anyone and kind is
% change|view. `new` is neither: the README says "contract account (init)". It is
% recorded as kind `init`, authority `contract`.
method(new,                init,   contract).
method(add_agent,          change, owner).
method(add_approver,       change, owner).
method(revoke_key,         change, owner).
method(request_action,     change, agent).
method(approve,            change, approver).
method(reject,             change, approver).
method(get_approval,       view,   anyone).
method(get_rejection,      view,   anyone).
method(get_revocation,     view,   anyone).
method(get_approvals,      view,   anyone).
method(get_request,        view,   anyone).
method(get_request_count,  view,   anyone).
method(get_approval_count, view,   anyone).
method(get_principal,      view,   anyone).
method(get_owner,          view,   anyone).

% Core operations (strategy 5.0: Add, Revoke, Req, Appr, Rej).
core_op(add_principal).
core_op(revoke_key).
core_op(request_action).
core_op(approve).
core_op(reject).

method_op(new,            init).
method_op(add_agent,      add_principal).
method_op(add_approver,   add_principal).
method_op(revoke_key,     revoke_key).
method_op(request_action, request_action).
method_op(approve,        approve).
method_op(reject,         reject).

% What each non-view method changes (C-4: authority- or proof-changing ops must emit).
changes(new,            authority).   % sets the owner
changes(add_agent,      authority).
changes(add_approver,   authority).
changes(revoke_key,     authority).
changes(request_action, proof).
changes(approve,        proof).
changes(reject,         proof).

%%% ========================================================
%%% Events (README "Events (NEP-297)", strategy R-7, F-15)
%%% ========================================================

emits(add_agent,      key_added).
emits(add_approver,   key_added).
emits(revoke_key,     key_revoked).
emits(request_action, approval_requested).
emits(approve,        action_approved).
emits(reject,         action_rejected).
% `new` emits nothing (README lists no init event): see threat_model accepted_risk(method(new), _).

%%% ========================================================
%%% Errors and guard precedence (strategy 5.0 Decidable, 5.1 TX-1..TX-5, TX-7)
%%% ========================================================

approval_error('NotOwner').
approval_error('KeyAlreadyRegistered').
approval_error('KeyNotRegistered').
approval_error('LogFull').
approval_error('IndirectCall').
approval_error('UnknownKey').
approval_error('WrongRole').
approval_error('KeyAccountMismatch').
approval_error('EmptyAction').
approval_error('ActionTooLong').
approval_error('TooManyPending').
approval_error('RequestNotFound').
approval_error('AlreadyApproved').
approval_error('AlreadyRejected').
approval_error('AgentRevoked').
approval_error('ActionMismatch').
approval_error('SelfApproval').
% CONTRADICTION: strategy section 2 says "ApprovalError: all 16 variants"; the
% errors named in sections 5.0/5.1 for 3426c92 are 17 (AlreadyRejected came with
% PR #15). The count in section 2 predated #15 (as did "13 #[near] methods"; both fixed at M3).

% guard(Op, Order, Error, Condition): Condition must hold, else Error.
% TX-1 add_principal
guard(add_principal, 1, 'NotOwner',             "caller account = owner").
guard(add_principal, 2, 'KeyAlreadyRegistered', "key not in dom P").
guard(add_principal, 3, 'LogFull',              "registration counter G /= MAXU").
% TX-2 revoke_key
guard(revoke_key,    1, 'NotOwner',             "caller account = owner").
guard(revoke_key,    2, 'KeyNotRegistered',     "key in dom P").
% TX-3 authenticate (role agent), then TX-4
guard(request_action, 1, 'IndirectCall',        "predecessor = signer").
guard(request_action, 2, 'UnknownKey',          "signer key in dom P").
guard(request_action, 3, 'WrongRole',           "P(key).role = agent").
guard(request_action, 4, 'KeyAccountMismatch',  "P(key).account = signer").
guard(request_action, 5, 'EmptyAction',         "len(action) >= 1").
guard(request_action, 6, 'ActionTooLong',       "len(action) =< MAX_ACTION_LEN").
guard(request_action, 7, 'TooManyPending',      "P(key).pending < MAX_PENDING_PER_KEY").
guard(request_action, 8, 'LogFull',             "request counter #R /= MAXU").
% TX-3 authenticate (role approver), then Decidable, then TX-5
guard(approve, 1,  'IndirectCall',              "predecessor = signer").
guard(approve, 2,  'UnknownKey',                "signer key in dom P").
guard(approve, 3,  'WrongRole',                 "P(key).role = approver").
guard(approve, 4,  'KeyAccountMismatch',        "P(key).account = signer").
guard(approve, 5,  'RequestNotFound',           "request_id < #R").
guard(approve, 6,  'AlreadyApproved',           "R[i] not approved").
guard(approve, 7,  'AlreadyRejected',           "R[i] not rejected").
guard(approve, 8,  'AgentRevoked',              "Live(s,i): agent registration of R[i] unbroken").
guard(approve, 9,  'ActionMismatch',            "action = R[i].action").
guard(approve, 10, 'SelfApproval',              "signer /= R[i].agent_account").
guard(approve, 11, 'LogFull',                   "approval counter #L /= MAXU").
% TX-3 authenticate (role approver), then Decidable, then TX-7 (D17)
guard(reject, 1, 'IndirectCall',                "predecessor = signer").
guard(reject, 2, 'UnknownKey',                  "signer key in dom P").
guard(reject, 3, 'WrongRole',                   "P(key).role = approver").
guard(reject, 4, 'KeyAccountMismatch',          "P(key).account = signer").
guard(reject, 5, 'RequestNotFound',             "request_id < #R").
guard(reject, 6, 'AlreadyApproved',             "R[i] not approved").
guard(reject, 7, 'AlreadyRejected',             "R[i] not rejected").
guard(reject, 8, 'AgentRevoked',                "Live(s,i): agent registration of R[i] unbroken").
guard(reject, 9, 'SelfApproval',                "signer /= R[i].agent_account").
% AMBIGUOUS: reject reuses the error name SelfApproval for "approver account = agent
% account" (strategy TX-7 lists it so); the README only says an approver "can't
% approve or reject a request made by an agent key bound to the same account".

%% guard_sequence(+Op, -Errors): the specified precedence of Op as a list.
guard_sequence(Op, Errors) :-
    core_op(Op),
    findall(N-E, guard(Op, N, E, _), Pairs),
    keysort(Pairs, Sorted),
    pairs_values(Sorted, Errors).

%%% ========================================================
%%% Error messages
%%% ========================================================
%% The text states only one panic string: RT-BATCH expects the batch to fail
%% with "action is empty". Every other message is unstated (strategy section 2:
%% "all 16 variants and their messages" are in scope, but are not listed).
error_message('EmptyAction', "action is empty").

%%% ========================================================
%%% Constants (strategy 5.0, 3.3 ASM-LIMITS, F-4; README)
%%% ========================================================

constant(max_action_len,        2048).   % N, bytes (README: 1 to 2048 bytes)
constant(min_action_len,        1).
constant(max_pending_per_key,   16).     % MAXP
constant(default_page_size,     50).     % DPG (README: limit defaults to 50)
constant(max_page_size,         100).    % PG  (README: clamped to 100)
constant(max_u,                 18446744073709551615).  % MAXU = 2^64 - 1
constant(max_total_log_length,  16384).  % ASM-LIMITS, bytes per receipt
constant(max_logs_per_receipt,  100).    % ASM-LIMITS
constant(max_return_bytes,      4194304).% ASM-LIMITS, 4 MiB
constant(max_call_tgas,         300).    % ASM-LIMITS
% F-4: "The limit breaks above about 2.6 KB" of action. Used as the RES-2 bound for N.
constant(action_len_log_bound,  2600).
% AMBIGUOUS: worst-case action_approved line. strategy F-4/RES-2 say about 13.0 KB,
% the README says about 13.1 KB. The larger value is recorded.
constant(worst_case_event_bytes, 13100).
constant(storage_byte_cost_yocto, 10000000000000000000). % ASM-STAKE: 10^19 yocto per byte

%%% ========================================================
%%% Decisions
%%% ========================================================

decision('D17', "Gabe (M4 plan, decision 1): add D17 (Approver key of another account may reject a pending request; terminal; frees the slot; never approvable). D11 drops 'rejection'.").
decision(decision_extraction, "Strategy section 8: code-facing parts of C-2, C-2t, C-3 and C-5 compare against generated facts (extracted/code_facts.pl from a plain-mode test in kani/, extracted/tla_facts.pl from GuardOrder). Until generated, those parts report pending extraction; the requirement-side parts run now.").
decision('C-6', "Gabe (M4 plan, decision 3): C-6 (API surface vs wasm exports/ABI) lands as 'pending M3' until extracted/api_facts.pl is generated by the near-unit job; no fake pass. M3: api_facts.pl is generated by tools/scripts/wasm-surface.sh from the cargo-near build and its ABI, so C-6 now runs.").
decision(error_messages, "The requirements text states only the EmptyAction message (\"action is empty\", RT-BATCH). C-3 checks the stated messages and, once extracted/code_facts.pl exists, the code's messages; until then the code part is pending extraction.").
decision('C-4-key_added', "key_added is emitted by both add_agent and add_approver (README). Both drive one core operation, add_principal, so C-4's 'each event from exactly one method' is checked per core operation (method_op/2).").
decision('C-9-new-ids', "C-2t and MC-3 (strategy 17.5) are in traceability.pl but not yet in status.toml; the M4 commit that lands this directory must add them. C-9 reports them as pending, not as a failure.").
