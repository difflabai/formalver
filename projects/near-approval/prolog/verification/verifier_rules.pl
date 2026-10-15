%% verifier_rules.pl -- VER-1..VER-8 (strategy 5.10): what an off-chain verifier
%% or executor must check before acting on an approval proof.
%%
%% Specified here, demonstrated in the sandbox (sandbox/tests/runtime.rs RT-SPOOF
%% feeds observed receipts to ver1_accept/2; sandbox/tests/deploy.rs feeds
%% observed access keys to ver8_ok/4) and tested in tests/test_verifier_rules.pl.
%% The rules are written from the catalogue, not from any verifier
%% implementation; deploy-checks/check_deployment.py implements VER-2, VER-3
%% and VER-8 against an RPC endpoint.
%%
%% Terms
%%   Accounts, keys, method names: atoms.  Heights, ids, ns: integers.
%%   Proof:  proof(C, RequestId, Action, AgentAcct, AgentKey, ApproverAcct,
%%                 ApproverKey, ApprovedNs)
%%   Source of a proof (VER-1):
%%     view(Contract, Method, Finality)          an RPC view call
%%     log(receipt(Executor, Status, Finality),  an EVENT_JSON log line
%%         event(Standard, Version, Event, RequestId))
%%   Access key permission (DEP-1.4, VER-8):
%%     full_access | missing
%%     function_call(Receiver, Methods, Allowance)  Allowance = unlimited | N
%%
%% Each ver<N>_* predicate succeeds iff the rule accepts; accept_proof/2 is the
%% conjunction a verifier applies to one proof.

:- module(verifier_rules, [
    ver1_accept/2,
    ver2_ok/3,
    ver3_ok/3,
    forbidden_action/1,
    ver4_ok/3,
    ver5_enumerate/3,
    ver5_ok/2,
    rd4_client/4,
    ver6_invalidates/2,
    ver7_execute/6,
    ver8_ok/4,
    dep14_permission_ok/3,
    accept_proof/2
]).

:- use_module(library(lists)).
:- use_module(library(between)).

%%% VER-1 -----------------------------------------------------------------
%% Accept a proof for (C, i) only from get_approval(i) at finality final, or
%% from an action_approved log in a successful receipt executed by C in a
%% final block. Anything else (another executor, a failed receipt, an
%% optimistic block, another standard or event) is at most a hint.

ver1_accept(C, view(C1, get_approval, final)) :- C1 == C.
ver1_accept(C, log(receipt(Exec, success, final), event(trust_approval, Version, action_approved, _))) :-
    Exec == C,
    Version == '1.0.0'.

%%% VER-2 -----------------------------------------------------------------
%% code_hash(C) equals the expected hash at the proof's block (archival) and
%% now. A missing account or missing code is a code hash that is not Expected.

ver2_ok(Expected, AtProofBlock, Now) :-
    atom(Expected),
    AtProofBlock == Expected,
    Now == Expected.

%%% VER-3 -----------------------------------------------------------------
%% ver3_ok(+Mode, +FullAccessKeysSinceB0, +ActionsToCSinceB0)
%%   Mode = locked:     no full-access key on C at any block since b0 (the
%%                      archival key lists, or b0+1 plus SH-12 and ASM-FCKEY);
%%   Mode = governance: full-access keys allowed, but an indexer scan of every
%%                      receipt to C since b0 finds no DeployContract,
%%                      UseGlobalContract, AddKey or DeleteAccount.
%% Actions are atoms (deploy_contract, function_call, ...).

forbidden_action(deploy_contract).
forbidden_action(use_global_contract).
forbidden_action(add_key).
forbidden_action(delete_account).

ver3_ok(locked, Keys, Actions) :-
    Keys == [],
    no_forbidden(Actions).
ver3_ok(governance, _, Actions) :-
    no_forbidden(Actions).

no_forbidden(Actions) :- \+ ( member(A, Actions), forbidden_action(A) ).

%%% VER-4 -----------------------------------------------------------------
%% ver4_ok(+Proof, +expect(Action, AgentAcct), +Allowlist)
%% The proof's action and agent account are what the verifier expected, and
%% the approver account is on the verifier's own allowlist (any = the owner's
%% registry is trusted, ASM-OWNER).

ver4_ok(proof(_, _, Action, Agent, _, Approver, _, _), expect(Action1, Agent1), Allow) :-
    Action == Action1,
    Agent == Agent1,
    Agent \== Approver,
    (   Allow == any -> true
    ;   memberchk(Approver, Allow)
    ).

%%% VER-5 -----------------------------------------------------------------
%% Enumerate with the RD-4 loop: from_index starts at 0 and advances by the
%% page length, stopping only on an empty page, and every page is read at one
%% block_id.  A read is page(BlockId, FromIndex, Limit, Items).

ver5_ok(Reads, Items) :-
    Reads = [page(B, 0, _, _) | _],
    ver5_ok_(Reads, B, 0, Items).

ver5_ok_([page(B1, F, _, [])], B, F, []) :- B1 == B.
ver5_ok_([page(B1, F, _, Page) | Rest], B, F, Items) :-
    B1 == B,
    Page \== [],
    length(Page, N),
    F1 is F + N,
    append(Page, Items1, Items),
    ver5_ok_(Rest, B, F1, Items1).

%% ver5_enumerate(+Log, +Limit, -Items): the RD-4 client loop run against the
%% get_approvals semantics (limit clamped to 100, default 50 when Limit = none)
%% over the approval log Log at one block. Yields Log exactly once, in order.
ver5_enumerate(Log, Limit, Items) :-
    rd4_client(Log, Limit, Reads, Items),
    ver5_ok(Reads, Items).

rd4_client(Log, Limit, Reads, Items) :- rd4_(Log, Limit, 0, Reads, Items).

rd4_(Log, Limit, F, [page(b, F, Limit, Page) | Reads], Items) :-
    get_approvals(Log, F, Limit, Page),
    (   Page == []
    ->  Reads = [], Items = []
    ;   length(Page, N), F1 is F + N,
        append(Page, Items1, Items),
        rd4_(Log, Limit, F1, Reads, Items1)
    ).

%% The view's paging (RD-2): limit none -> 50, clamped to 100; past the end -> [].
get_approvals(Log, F, Limit0, Page) :-
    (   Limit0 == none -> Limit = 50 ; Limit is min(Limit0, 100) ),
    length(Log, Len),
    (   F >= Len -> Page = []
    ;   End is min(Len, F + Limit),
        findall(X, ( between(F, End, I), I < End, nth0(I, Log, X) ), Page)
    ).

%%% VER-6 -----------------------------------------------------------------
%% ver6_invalidates(+Cached, +Observed): with state(RequestCount,
%% ApprovalCount, CodeHash) terms, a counter decrease or a code hash change
%% invalidates every cached (C, i). Only a heuristic for RT-RESET: a recreated
%% contract that has caught up with the cached counters is not detected
%% (VER-3 is the real check).

ver6_invalidates(state(R0, A0, H0), state(R1, A1, H1)) :-
    (   R1 < R0 -> true
    ;   A1 < A0 -> true
    ;   H1 \== H0
    ).

%%% VER-7 -----------------------------------------------------------------
%% ver7_execute(+Seen, +C, +RequestId, +ApprovedNs, +NowNs, +MaxAgeNs): an
%% executor acts on (C, RequestId) at most once (Seen lists C-Id pairs already
%% executed) and only while the approval is at most MaxAgeNs old. The
%% contract never expires or consumes approvals, so both are the executor's
%% job.

ver7_execute(Seen, C, Id, ApprovedNs, NowNs, MaxAgeNs) :-
    \+ memberchk(C-Id, Seen),
    ApprovedNs =< NowNs,
    NowNs - ApprovedNs =< MaxAgeNs.

%%% VER-8 -----------------------------------------------------------------
%% ver8_ok(+C, +Proof, +AgentKeyAtRequest, +ApproverKeyAtApproval): the
%% archival view_access_key of the agent key on the agent account at the block
%% that included the request tx, and of the approver key on the approver account
%% at the block that included the approval tx, are both function-call keys with
%% receiver C, the DEP-1.4 method names and a finite allowance.  Each view is
%% key(Account, Key, Permission). This closes F-9 per proof: code on the
%% signer's own account can't be called with such a key.

ver8_ok(C, proof(C1, _, _, Agent, AKey, Approver, PKey, _),
        key(Agent1, AKey1, APerm), key(Approver1, PKey1, PPerm)) :-
    C1 == C,
    Agent1 == Agent, AKey1 == AKey,
    Approver1 == Approver, PKey1 == PKey,
    dep14_permission_ok(C, agent, APerm),
    dep14_permission_ok(C, approver, PPerm).

%% dep14_permission_ok(+C, +Role, +Permission): DEP-1.4's key shape.
%% Approvers: [approve], or [approve, reject] in either order (the README asks
%% for both since PR #15 added reject).
dep14_permission_ok(C, Role, function_call(R, Methods, Allowance)) :-
    R == C,
    integer(Allowance), Allowance >= 0,
    sort(Methods, Sorted),
    length(Methods, N), length(Sorted, N),      % no duplicates
    role_methods(Role, Sorted).

role_methods(agent, [request_action]).
role_methods(approver, [approve]).
role_methods(approver, [approve, reject]).

%%% All of them ------------------------------------------------------------
%% accept_proof(+Proof, +Evidence) with
%%   Evidence = evidence(Source, CodeHashes, Lock, Expect, Allow, Keys)
%%     Source     VER-1 source term
%%     CodeHashes hashes(Expected, AtProofBlock, Now)            VER-2
%%     Lock       lock(Mode, FullAccessKeysSinceB0, Actions)     VER-3
%%     Expect     expect(Action, AgentAcct)                      VER-4
%%     Allow      approver allowlist or any                      VER-4
%%     Keys       keys(AgentKeyView, ApproverKeyView)            VER-8
%% VER-5 (enumeration), VER-6 (cache) and VER-7 (execution) are about how
%% proofs are found, cached and used, not about one proof; apply them
%% separately.

accept_proof(Proof, evidence(Source, hashes(E, P, N), lock(M, Ks, As), Expect, Allow, keys(AK, PK))) :-
    Proof = proof(C, _, _, _, _, _, _, _),
    ver1_accept(C, Source),
    ver2_ok(E, P, N),
    ver3_ok(M, Ks, As),
    ver4_ok(Proof, Expect, Allow),
    ver8_ok(C, Proof, AK, PK).
