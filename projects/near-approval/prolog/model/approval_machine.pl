%% approval_machine.pl -- Reference semantics step/4 of the approval contract (M4)
%%
%% INDEPENDENCE (ASM-SPEC): written only from requirements text -- strategy.md
%% (Target, sections 1, 3, 4, 5.0-5.5, 17.6) and the upstream README
%% (contracts/approval/README.md). No Rust, Kani or TLA+ source was read.
%% Disagreements with the code are meant to surface in MC-3 / MC-2, not here.
%% model/FROZEN records the sha256 of this file before any comparison.
%%
%% State (strategy 5.0, s = <o, P, R, L, G, V>):
%%   st(Params, Owner, P, R, L, G, V)
%%     Params = params(N, MaxPending, MaxU, PageMax, PageDefault)
%%     P = sorted list Key-p(Account, Role, RegId, ActiveFrom, Pending)
%%     R = list of req(Id, AgentAcct, AgentKey, AgentReg, Action, Ap, Rj), in id order
%%           Ap = none | ap(LogIndex, ApproverAcct, ApproverKey, ApproverReg)
%%           Rj = none | rj(RejecterAcct, RejecterKey, RejecterReg)
%%     L = list of request ids, in approval order
%%     G = registration counter
%%     V = sorted list of revoked registration ids
%%
%% Abstractions:
%%   * Actions are empty | ok(Tag) | too_long. action_of_length/3 maps a byte
%%     length to its class, so length boundaries (ROB-3) are still testable.
%%   * Block times are dropped (strategy 17.1 does the same; the core stores
%%     them and never branches on them). So V records which registrations were
%%     revoked, not when; INV-10 and TR-4 are out of this model's scope.
%%   * Counters are unbounded integers compared with MaxU, a parameter, so
%%     MC-1s can scale it.
%%
%% Operations (strategy 5.0 Add, Revoke, Req, Appr, Rej):
%%   add(CallerAcct, Key, Account, Role)       add_agent / add_approver (Role = agent | approver)
%%   revoke(CallerAcct, Key)                   revoke_key
%%   request(c(Pred, Signer, Key), Action)     request_action
%%   approve(c(Pred, Signer, Key), Id, Action) approve
%%   reject(c(Pred, Signer, Key), Id)          reject (D17)
%%   view(Query)                               any get_* view: never changes state
%% Result = ok(Value) | err(Error). A rejected call stutters: S1 = S0 (TX-0, D12).
%% The error is the first failing guard in the order of guard/4 (approval_req.pl).

:- module(approval_machine, [
    real_params/1,
    scaled_params/3,
    params_get/3,
    init_state/3,
    step/4,
    op_kind/2,
    action_of_length/3,
    principal/3,
    request_at/3,
    request_count/2,
    approval_count/2,
    live/2,
    status/3,
    pend_count/3,
    view/3,
    approval/3,
    approvals/5,
    client_enumerate/4,
    guard_holds/4
]).

:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(between)).
:- use_module('../requirements/approval_req').

%%% ========================================================
%%% Parameters and initial state
%%% ========================================================

%% real_params(-Params): the requirement constants.
real_params(params(N, MaxP, MaxU, PG, DPG)) :-
    constant(max_action_len, N),
    constant(max_pending_per_key, MaxP),
    constant(max_u, MaxU),
    constant(max_page_size, PG),
    constant(default_page_size, DPG).

%% scaled_params(+MaxPending, +MaxU, -Params): MC-1s (strategy 5.11).
scaled_params(MaxP, MaxU, params(N, MaxP, MaxU, PG, DPG)) :-
    constant(max_action_len, N),
    constant(max_page_size, PG),
    constant(default_page_size, DPG).

params_get(max_action_len,      params(N, _, _, _, _), N).
params_get(max_pending_per_key, params(_, P, _, _, _), P).
params_get(max_u,               params(_, _, U, _, _), U).
params_get(max_page_size,       params(_, _, _, PG, _), PG).
params_get(default_page_size,   params(_, _, _, _, D), D).

%% init_state(+Params, +Owner, -S): Init(o) = <o, {}, [], [], 0, {}> (strategy 5.0, SH-9).
init_state(Params, Owner, st(Params, Owner, [], [], [], 0, [])).

%% action_of_length(+Bytes, +Params, -Class): UTF-8 byte length -> abstract action.
action_of_length(0, _, empty) :- !.
action_of_length(Len, Params, Class) :-
    params_get(max_action_len, Params, N),
    (   Len =< N -> Class = ok(len(Len))
    ;   Class = too_long
    ).

%%% ========================================================
%%% State accessors
%%% ========================================================

principal(st(_, _, P, _, _, _, _), K, Pr) :- memberchk(K-Pr, P).

request_at(st(_, _, _, R, _, _, _), I, Req) :-
    integer(I), I >= 0, nth0(I, R, Req).

request_count(st(_, _, _, R, _, _, _), N) :- length(R, N).
approval_count(st(_, _, _, _, L, _, _), N) :- length(L, N).

%% live(S, I): Live(s,i) = P(R[i].ak) = <R[i].aa, Agent, f, _> and f =< i (strategy 5.0).
%% README: "only requests made after [active_from] can be decided".
live(S, I) :-
    request_at(S, I, req(_, AA, AK, _, _, _, _)),
    principal(S, AK, p(Acct, Role, _, From, _)),
    Acct == AA, Role == agent, From =< I.

%% status(S, I, Status): approved | rejected | pending | void (strategy 5.0 Status, README).
status(S, I, Status) :-
    request_at(S, I, req(_, _, _, _, _, Ap, Rj)),
    (   Ap \== none -> Status = approved
    ;   Rj \== none -> Status = rejected
    ;   live(S, I)  -> Status = pending
    ;   Status = void
    ).

%% pend_count(S, K, N): Pend(s,k) = #{i >= P(k).from : R[i].ak = k, undecided} (5.0).
pend_count(S, K, N) :-
    principal(S, K, p(_, _, _, From, _)),
    S = st(_, _, _, R, _, _, _),
    pend_count_(R, K, From, 0, N).

pend_count_([], _, _, N, N).
pend_count_([req(Id, _, AK, _, _, Ap, Rj) | Rs], K, From, N0, N) :-
    (   Id >= From, AK == K, Ap == none, Rj == none -> N1 is N0 + 1 ; N1 = N0 ),
    pend_count_(Rs, K, From, N1, N).

%%% ========================================================
%%% step/4
%%% ========================================================

op_kind(add(_, _, _, _),  add_principal).
op_kind(revoke(_, _),     revoke_key).
op_kind(request(_, _),    request_action).
op_kind(approve(_, _, _), approve).
op_kind(reject(_, _),     reject).

step(S0, view(Q), ok(A), S0) :- !, view(S0, Q, A).
step(S0, Op, Result, S1) :-
    op_kind(Op, Kind),
    guard_sequence(Kind, Guards),
    (   first_failing(Guards, Kind, S0, Op, E)
    ->  Result = err(E), S1 = S0
    ;   effect(Op, S0, Result, S1)
    ).

first_failing([G | Gs], Kind, S, Op, E) :-
    (   guard_holds(Kind, G, S, Op) -> first_failing(Gs, Kind, S, Op, E)
    ;   E = G
    ).

%% guard_holds(+Kind, +Error, +S, +Op): the condition of guard(Kind, _, Error, _).
%% Each condition may assume that the guards before it in the order hold.

% --- add_principal (TX-1, D3, D4)
guard_holds(add_principal, 'NotOwner', st(_, O, _, _, _, _, _), add(C, _, _, _)) :- C == O.
guard_holds(add_principal, 'KeyAlreadyRegistered', S, add(_, K, _, _)) :- \+ principal(S, K, _).
guard_holds(add_principal, 'LogFull', st(Pm, _, _, _, _, G, _), _) :-
    params_get(max_u, Pm, U), G =\= U.
% --- revoke_key (TX-2, D3, D7)
guard_holds(revoke_key, 'NotOwner', st(_, O, _, _, _, _, _), revoke(C, _)) :- C == O.
guard_holds(revoke_key, 'KeyNotRegistered', S, revoke(_, K)) :- principal(S, K, _).
% --- authenticate (TX-3, D1, D2), shared by request_action, approve, reject
guard_holds(Kind, 'IndirectCall', _, Op) :-
    auth_op(Kind), op_caller(Op, c(Pred, Sig, _)), Pred == Sig.
guard_holds(Kind, 'UnknownKey', S, Op) :-
    auth_op(Kind), op_caller(Op, c(_, _, K)), principal(S, K, _).
guard_holds(Kind, 'WrongRole', S, Op) :-
    auth_op(Kind), op_caller(Op, c(_, _, K)), principal(S, K, p(_, Role, _, _, _)),
    kind_role(Kind, Role0), Role == Role0.
guard_holds(Kind, 'KeyAccountMismatch', S, Op) :-
    auth_op(Kind), op_caller(Op, c(_, Sig, K)), principal(S, K, p(Acct, _, _, _, _)),
    Acct == Sig.
% --- request_action (TX-4, D9)
guard_holds(request_action, 'EmptyAction', _, request(_, A)) :- A \== empty.
guard_holds(request_action, 'ActionTooLong', _, request(_, A)) :- A \== too_long.
guard_holds(request_action, 'TooManyPending', S, request(c(_, _, K), _)) :-
    S = st(Pm, _, _, _, _, _, _),
    principal(S, K, p(_, _, _, _, Pend)),
    params_get(max_pending_per_key, Pm, MaxP),
    Pend < MaxP.
guard_holds(request_action, 'LogFull', S, _) :-
    S = st(Pm, _, _, _, _, _, _),
    request_count(S, NR), params_get(max_u, Pm, U), NR =\= U.
% --- Decidable(s,i), shared by approve and reject (strategy 5.0, D6, D7, D17)
guard_holds(Kind, 'RequestNotFound', S, Op) :-
    decide_op(Kind), op_id(Op, I), request_count(S, NR),
    integer(I), I >= 0, I < NR.
guard_holds(Kind, 'AlreadyApproved', S, Op) :-
    decide_op(Kind), op_id(Op, I), request_at(S, I, req(_, _, _, _, _, Ap, _)), Ap == none.
guard_holds(Kind, 'AlreadyRejected', S, Op) :-
    decide_op(Kind), op_id(Op, I), request_at(S, I, req(_, _, _, _, _, _, Rj)), Rj == none.
guard_holds(Kind, 'AgentRevoked', S, Op) :-
    decide_op(Kind), op_id(Op, I), live(S, I).
% --- approve (TX-5, D10, D5)
guard_holds(approve, 'ActionMismatch', S, approve(_, I, A)) :-
    request_at(S, I, req(_, _, _, _, Act, _, _)), Act == A.
guard_holds(Kind, 'SelfApproval', S, Op) :-
    decide_op(Kind), op_id(Op, I), op_caller(Op, c(_, Sig, _)),
    request_at(S, I, req(_, AA, _, _, _, _, _)), Sig \== AA.
guard_holds(approve, 'LogFull', S, _) :-
    S = st(Pm, _, _, _, _, _, _),
    approval_count(S, NL), params_get(max_u, Pm, U), NL =\= U.

auth_op(request_action).
auth_op(approve).
auth_op(reject).

decide_op(approve).
decide_op(reject).

kind_role(request_action, agent).
kind_role(approve, approver).
kind_role(reject, approver).

op_caller(request(C, _), C).
op_caller(approve(C, _, _), C).
op_caller(reject(C, _), C).

op_id(approve(_, I, _), I).
op_id(reject(_, I), I).

%%% Effects of successful calls

% TX-1: p = <acct, role, G, #R, 0>; P' = P[k -> p]; G' = G + 1.
effect(add(_, K, Acct, Role), st(Pm, O, P0, R, L, G0, V), ok(principal(Acct, Role, G0, NR, 0)),
       st(Pm, O, P1, R, L, G1, V)) :-
    length(R, NR),
    put_assoc_list(P0, K, p(Acct, Role, G0, NR, 0), P1),
    G1 is G0 + 1.
% TX-2: P' = P \ {k}; V' = V[P(k).reg -> t]. Returns the removed principal.
effect(revoke(_, K), S0, ok(principal(Acct, Role, Reg, From, Pend)), S1) :-
    S0 = st(Pm, O, P0, R, L, G, V0),
    principal(S0, K, p(Acct, Role, Reg, From, Pend)),
    del_assoc_list(P0, K, P1),
    ord_insert(V0, Reg, V1),
    S1 = st(Pm, O, P1, R, L, G, V1).
% TX-4: r = <#R, sig, key, P(key).reg, action, None, None>; R' = R.r; pend + 1.
effect(request(c(_, Sig, K), A), S0, ok(Id), S1) :-
    S0 = st(Pm, O, P0, R0, L, G, V),
    principal(S0, K, p(Acct, Role, Reg, From, Pend)),
    length(R0, Id),
    append(R0, [req(Id, Sig, K, Reg, A, none, none)], R1),
    Pend1 is Pend + 1,
    put_assoc_list(P0, K, p(Acct, Role, Reg, From, Pend1), P1),
    S1 = st(Pm, O, P1, R1, L, G, V).
% TX-5: R[i].ap = <#L, sig, key, P(key).reg>; L' = L.i; P(R[i].ak).pend - 1.
effect(approve(c(_, Sig, K), I, _), S0, ok(Proof), S1) :-
    S0 = st(Pm, O, P0, R0, L0, G, V),
    principal(S0, K, p(_, _, BReg, _, _)),
    request_at(S0, I, req(Id, AA, AK, AG, Act, none, Rj)),
    length(L0, Ix),
    replace_nth0(R0, I, req(Id, AA, AK, AG, Act, ap(Ix, Sig, K, BReg), Rj), R1),
    append(L0, [I], L1),
    dec_pending(P0, AK, P1),
    S1 = st(Pm, O, P1, R1, L1, G, V),
    approval(S1, I, some(Proof)).
% TX-7 / D17: R[i].rj = <sig, key, P(key).reg>; P(R[i].ak).pend - 1; L unchanged.
effect(reject(c(_, Sig, K), I), S0, ok(rejection(Req1)), S1) :-
    S0 = st(Pm, O, P0, R0, L, G, V),
    principal(S0, K, p(_, _, BReg, _, _)),
    request_at(S0, I, req(Id, AA, AK, AG, Act, Ap, none)),
    Req1 = req(Id, AA, AK, AG, Act, Ap, rj(Sig, K, BReg)),
    replace_nth0(R0, I, Req1, R1),
    dec_pending(P0, AK, P1),
    S1 = st(Pm, O, P1, R1, L, G, V).

dec_pending(P0, K, P1) :-
    memberchk(K-p(Acct, Role, Reg, From, Pend), P0),
    Pend1 is Pend - 1,
    put_assoc_list(P0, K, p(Acct, Role, Reg, From, Pend1), P1).

%%% ========================================================
%%% Views (README API; strategy 5.5 RD-1..RD-8, SH-7)
%%% ========================================================

%% approval(S, I, Opt): the core proof, some(proof(...)) iff R[i] approved (RD-1).
%% proof(ApprovalIndex, RequestId, Action, AgentAcct, AgentKey, AgentReg,
%%       ApproverAcct, ApproverKey, ApproverReg)
approval(S, I, Opt) :-
    (   request_at(S, I, req(Id, AA, AK, AG, Act, ap(Ix, BA, BK, BG), _))
    ->  Opt = some(proof(Ix, Id, Act, AA, AK, AG, BA, BK, BG))
    ;   Opt = none
    ).

%% approvals(S, From, Limit, End, Page): RD-2. End = min(f (+) min(l, PG), #L) with (+)
%% saturating at MaxU; Page = proofs of L[From .. End-1], so len(Page) = End -. From.
approvals(S, From, Limit, End, Page) :-
    S = st(Pm, _, _, _, L, _, _),
    params_get(max_page_size, Pm, PG),
    params_get(max_u, Pm, U),
    length(L, NL),
    Lim is min(Limit, PG),
    End is min(min(From + Lim, U), NL),
    (   From >= End -> Page = []
    ;   Last is End - 1,
        findall(P, ( between(From, Last, J), nth0(J, L, I), approval(S, I, some(P)) ), Page)
    ).

%% client_enumerate(S, Limit, Proofs, Pages): RD-4 documented loop -- from += len(page)
%% until a page comes back empty (README "Don't stop on a page shorter than limit").
client_enumerate(S, Limit, Proofs, Pages) :-
    client_loop(S, 0, Limit, Proofs, 0, Pages).

client_loop(S, From, Limit, Proofs, N0, N) :-
    approvals(S, From, Limit, _, Page),
    (   Page == [] -> Proofs = [], N = N0
    ;   length(Page, Len), From1 is From + Len, N1 is N0 + 1,
        append(Page, Rest, Proofs),
        client_loop(S, From1, Limit, Rest, N1, N)
    ).

%% view(S, Query, Answer)
% get_approval(id): the proof plus the revocation status of both registrations
% (README: agent_key_revoked_at / approver_key_revoked_at; RD-8). Times are abstracted
% to revoked | none.
view(S, get_approval(I), A) :-
    approval(S, I, Opt),
    (   Opt = some(P) -> proof_view(S, P, PV), A = some(PV) ; A = none ).
% get_approvals(from_index?, limit?): defaults 0 and DPG (README, SH-7).
view(S, get_approvals(F0, L0), Page) :-
    S = st(Pm, _, _, _, _, _, _),
    params_get(default_page_size, Pm, DPG),
    ( F0 == none -> F = 0 ; F = F0 ),
    ( L0 == none -> Lim = DPG ; Lim = L0 ),
    approvals(S, F, Lim, _, Proofs),
    maplist(proof_view(S), Proofs, Page).
view(S, get_request(I), A) :-
    (   request_at(S, I, Req) -> status(S, I, St), A = some(request_view(Req, St))
    ;   A = none ).
view(S, get_rejection(I), A) :-
    (   request_at(S, I, req(Id, AA, AK, AG, Act, _, rj(BA, BK, BG)))
    ->  A = some(rejection(Id, Act, AA, AK, AG, BA, BK, BG))
    ;   A = none ).
% get_revocation(registration_id): revoked iff that registration was revoked; none if
% live or never issued (README).
view(st(_, _, _, _, _, _, V), get_revocation(G), A) :-
    ( memberchk(G, V) -> A = some(revoked) ; A = none ).
% AMBIGUOUS: get_principal's fields. SH-7 lists account_id, role and pending; the README
% only says "state inspection". The model answers those three.
view(S, get_principal(K), A) :-
    (   principal(S, K, p(Acct, Role, _, _, Pend)) -> A = some(principal(Acct, Role, Pend))
    ;   A = none ).
view(st(_, O, _, _, _, _, _), get_owner, O).
view(S, get_request_count, N) :- request_count(S, N).
view(S, get_approval_count, N) :- approval_count(S, N).
view(S, request_status(I), A) :-
    ( status(S, I, St) -> A = some(St) ; A = none ).

proof_view(st(_, _, _, _, _, _, V), P, proof_view(P, AgentRev, ApproverRev)) :-
    P = proof(_, _, _, _, _, AG, _, _, BG),
    ( memberchk(AG, V) -> AgentRev = revoked ; AgentRev = none ),
    ( memberchk(BG, V) -> ApproverRev = revoked ; ApproverRev = none ).

%%% ========================================================
%%% Small list helpers
%%% ========================================================

put_assoc_list([], K, V, [K-V]).
put_assoc_list([K0-V0 | T], K, V, Out) :-
    compare(Ord, K, K0),
    (   Ord = (=) -> Out = [K-V | T]
    ;   Ord = (<) -> Out = [K-V, K0-V0 | T]
    ;   Out = [K0-V0 | Out1], put_assoc_list(T, K, V, Out1)
    ).

del_assoc_list([K0-V0 | T], K, Out) :-
    (   K0 == K -> Out = T
    ;   Out = [K0-V0 | Out1], del_assoc_list(T, K, Out1)
    ).

ord_insert([], X, [X]).
ord_insert([Y | Ys], X, Out) :-
    compare(Ord, X, Y),
    (   Ord = (=) -> Out = [Y | Ys]
    ;   Ord = (<) -> Out = [X, Y | Ys]
    ;   Out = [Y | Out1], ord_insert(Ys, X, Out1)
    ).

replace_nth0([_ | T], 0, X, [X | T]) :- !.
replace_nth0([H | T], N, X, [H | T1]) :-
    N > 0, N1 is N - 1, replace_nth0(T, N1, X, T1).
