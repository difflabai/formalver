%% model_check.pl -- MC-1 and MC-1s: bounded model check of the reference step/4
%%
%% strategy 5.11: owner o, accounts {a,b}, keys {k1,k2,k3}, depth 6, with state
%% deduplication (layered BFS over sorted state sets). Every reached state is
%% checked against the state invariants, and every successful edge against the
%% step properties, both written here from strategy 5.2-5.4.
%%
%% Operation universe per state (why it is enough):
%%   * every owner add (3 keys x 2 accounts x 2 roles) and revoke (3 keys);
%%   * every direct call c(X,X,K) for X in {a,b}, K in {k1,k2,k3}: request with
%%     empty | ok(x) | too_long; approve of ids 0..#R (#R itself: RequestNotFound)
%%     with ok(x) | empty; reject of ids 0..#R;
%%   * one non-owner add and revoke (caller a), and one relayed call per
%%     authenticated method (predecessor o, signer a).
%% Non-owner and relayed calls fail at their first guard whatever the state
%% (NotOwner, IndirectCall are first in guard/4), so they stutter and one
%% representative each covers them. One storable payload suffices: the model
%% compares actions only by equality, and approve with `empty` exercises
%% ActionMismatch.
%%
%% Results: mc(Name, Depth, States, Edges, Errors, Coverage, Violations, Millis)

:- module(model_check, [
    mc_run/4,
    mc_check/3,
    mc_profile/3,
    state_violation/2,
    edge_violation/5,
    expected_unreached/2,
    format_mc/1
]).

:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(time)).
:- use_module(library(pairs)).
:- use_module(library(format)).
:- use_module(library(ordsets)).
:- use_module(library(between)).
:- use_module('../requirements/approval_req').
:- use_module('../model/approval_machine').

%%% ========================================================
%%% Profiles
%%% ========================================================

%% mc_profile(Name, Params, Depth)
mc_profile('MC-1', Params, 6) :- real_params(Params).
% MC-1s: max_pending = 2, max_u = 2 (strategy 5.11).
mc_profile('MC-1s', Params, 6) :- scaled_params(2, 2, Params).

%% expected_unreached(Profile, Kind-Error): errors 5.11 says the profile need not reach.
% AMBIGUOUS: strategy 5.11 predates registration ids (PR #15) and lists only
% approve's LogFull, request_action's LogFull and TooManyPending as unreachable in
% MC-1. add_principal's LogFull needs G = MAXU, so with the real constants it is
% equally unreachable at depth 6; it is added here. With max_u = 2 (MC-1s) it is
% reachable and required.
expected_unreached('MC-1', approve-'LogFull').
expected_unreached('MC-1', request_action-'LogFull').
expected_unreached('MC-1', request_action-'TooManyPending').
expected_unreached('MC-1', add_principal-'LogFull').
expected_unreached('MC-1s', approve-'LogFull').

%% Coverage MC-1 must reach (5.11: an approved state and a void state; TR-5 and
%% D17 add rejected; TR-3 "revival attempt": revoke, re-add, decide fails).
required_coverage('MC-1', [approved, rejected, void, revival_attempt]).
required_coverage('MC-1s', [approved, rejected, void, pending_cap]).

%% Never reachable (LEM-3, F-7).
must_not_reach(_, approve-'LogFull').

owner(o).
accounts([a, b]).
keys([k1, k2, k3]).

%%% ========================================================
%%% Operation universe
%%% ========================================================

mc_op(_, add(o, K, A, Role)) :-
    keys(Ks), member(K, Ks), accounts(As), member(A, As), member(Role, [agent, approver]).
mc_op(_, add(a, k1, a, agent)).
mc_op(_, revoke(o, K)) :- keys(Ks), member(K, Ks).
mc_op(_, revoke(a, k1)).
mc_op(_, request(c(X, X, K), Act)) :-
    accounts(As), member(X, As), keys(Ks), member(K, Ks),
    member(Act, [empty, ok(x), too_long]).
mc_op(_, request(c(o, a, k1), ok(x))).
mc_op(S, approve(c(X, X, K), I, Act)) :-
    accounts(As), member(X, As), keys(Ks), member(K, Ks),
    request_count(S, NR), between(0, NR, I),
    member(Act, [ok(x), empty]).
mc_op(_, approve(c(o, a, k1), 0, ok(x))).
mc_op(S, reject(c(X, X, K), I)) :-
    accounts(As), member(X, As), keys(Ks), member(K, Ks),
    request_count(S, NR), between(0, NR, I).
mc_op(_, reject(c(o, a, k1), 0)).

%%% ========================================================
%%% BFS
%%% ========================================================

%% mc_run(+Name, +Params, +Depth, -Result)
mc_run(Name, Params, Depth, mc(Name, Depth, NStates, NEdges, Errors, Coverage, Violations, Ms)) :-
    now_ms(T0),
    owner(O),
    init_state(Params, O, S0),
    findall(V, state_violation(S0, V), V0),
    state_coverage(S0, [], C0),
    bfs(0, Depth, [S0], [S0], acc([], C0, V0, 0), acc(Errors, Coverage, Violations0, NEdges), Visited),
    length(Visited, NStates),
    sort(Violations0, Violations),
    now_ms(T1),
    Ms is T1 - T0.

bfs(D, Depth, Frontier, Visited, Acc0, Acc, VisitedOut) :-
    (   D >= Depth ; Frontier == [] ), !,
    Acc = Acc0, VisitedOut = Visited.
bfs(D, Depth, Frontier, Visited, Acc0, Acc, VisitedOut) :-
    expand_all(Frontier, Acc0, Acc1, Succs, []),
    sort(Succs, Sorted),
    ord_subtract(Sorted, Visited, New),
    ord_union(Visited, New, Visited1),
    check_states(New, Acc1, Acc2),
    D1 is D + 1,
    bfs(D1, Depth, New, Visited1, Acc2, Acc, VisitedOut).

expand_all([], Acc, Acc, Tail, Tail).
expand_all([S | Ss], Acc0, Acc, Succs, Tail) :-
    findall(Op-Res-S1, ( mc_op(S, Op), step(S, Op, Res, S1) ), Ts),
    expand_edges(Ts, S, Acc0, Acc1, ErrList, [], Succs, Mid),
    sort(ErrList, Errs),
    Acc1 = acc(E1, C1, V1, N1),
    ord_union(E1, Errs, E2),
    expand_all(Ss, acc(E2, C1, V1, N1), Acc, Mid, Tail).

expand_edges([], _, Acc, Acc, Es, Es, Ss, Ss).
expand_edges([Op-Res-S1 | Ts], S, acc(E, C0, V0, N0), Acc, Es, EsT, Ss, SsT) :-
    N1 is N0 + 1,
    op_kind(Op, Kind),
    (   Res = err(Err)
    ->  Es = [Kind-Err | Es1],
        error_coverage(S, Op, Err, C0, C1),
        V1 = V0, Ss = Ss1
    ;   Es = Es1, C1 = C0,
        findall(Viol, edge_violation(S, Op, Res, S1, Viol), Vs),
        append(Vs, V0, V1),
        Ss = [S1 | Ss1]
    ),
    expand_edges(Ts, S, acc(E, C1, V1, N1), Acc, Es1, EsT, Ss1, SsT).

check_states([], Acc, Acc).
check_states([S | Ss], acc(E, C0, V0, N), Acc) :-
    findall(V, state_violation(S, V), Vs),
    append(Vs, V0, V1),
    state_coverage(S, C0, C1),
    check_states(Ss, acc(E, C1, V1, N), Acc).

%%% Coverage

state_coverage(S, C0, C) :-
    findall(Tag, state_tag(S, Tag), Tags0),
    sort(Tags0, Tags),
    ord_union(C0, Tags, C).

state_tag(S, St) :-
    request_count(S, NR), NR > 0, Last is NR - 1,
    between(0, Last, I), status(S, I, St).
state_tag(S, pending_cap) :-
    S = st(Pm, _, P, _, _, _, _),
    params_get(max_pending_per_key, Pm, MaxP),
    member(_-p(_, agent, _, _, MaxP), P).

% Revival attempt (TR-3 witness): a decision on a request whose agent key is
% registered again, refused with AgentRevoked.
error_coverage(S, Op, 'AgentRevoked', C0, C) :-
    ( Op = approve(_, I, _) ; Op = reject(_, I) ),
    request_at(S, I, req(_, _, AK, _, _, _, _)),
    principal(S, AK, _), !,
    ord_union(C0, [revival_attempt], C).
error_coverage(_, _, _, C, C).

%%% ========================================================
%%% State invariants (strategy 5.2), viol(Id, State)
%%% ========================================================

state_violation(S, viol(Id, S)) :- inv(Id, S, Ok), \+ call(Ok).

inv('INV-0', st(_, _, P, _, _, _, _), approval_machine_keys_strict(P)).
inv('INV-1', st(_, _, _, R, _, _, _), dense_ids(R, 0)).
inv('INV-2', st(_, _, _, R, _, _, _), forall(member(Rq, R), arg(5, Rq, ok(_)))).
inv('INV-3', S, inv3(S)).
inv('INV-4', S, inv4(S)).
inv('INV-5', st(_, _, _, R, _, _, _), forall(member(Rq, R), sep_duties(Rq))).
inv('INV-6', st(_, _, _, R, _, _, _), forall(member(Rq, R), distinct_keys(Rq))).
inv('INV-7', S, inv7(S)).
inv('INV-8', S, inv8(S)).
inv('INV-9', S, inv9(S)).
inv('INV-11', S, inv11(S)).
inv('INV-12', st(_, _, _, _, _, G, V), forall(member(X, V), X < G)).
inv('INV-13', st(_, _, _, R, _, _, _), forall(member(req(_, _, _, _, _, Ap, Rj), R), (Ap == none ; Rj == none))).
inv('INV-14', S, inv14(S)).
inv('INV-15', st(_, _, P, _, _, G, V), (length(P, NP), length(V, NV), NP + NV =:= G)).
inv('INV-16', S, inv16(S)).
inv('LEM-1', st(_, _, _, _, L, _, _), (sort(L, SL), length(SL, N), length(L, N))).
inv('LEM-2', S, lem2(S)).
inv('LEM-3', S, lem3(S)).
inv('TLA-LIVE-2', S, approvable(S)).   % D9: every pending request approvable and rejectable

approval_machine_keys_strict([]).
approval_machine_keys_strict([_]).
approval_machine_keys_strict([K1-_, K2-V | T]) :- K1 @< K2, approval_machine_keys_strict([K2-V | T]).

dense_ids([], _).
dense_ids([req(Id, _, _, _, _, _, _) | T], I) :- Id == I, I1 is I + 1, dense_ids(T, I1).

inv3(S) :-
    S = st(_, _, _, _, L, _, _), request_count(S, NR),
    forall(nth0(J, L, I), ( I < NR, request_at(S, I, req(_, _, _, _, _, ap(J0, _, _, _), _)), J0 == J )).
inv4(S) :-
    S = st(_, _, _, R, L, _, _), length(L, NL),
    forall(( nth0(I, R, Rq), arg(6, Rq, ap(X, _, _, _)) ), ( X < NL, nth0(X, L, I0), I0 == I )).

sep_duties(req(_, AA, _, _, _, Ap, Rj)) :-
    ( Ap = ap(_, BA, _, _) -> BA \== AA ; true ),
    ( Rj = rj(BA2, _, _) -> BA2 \== AA ; true ).
distinct_keys(req(_, _, AK, _, _, Ap, Rj)) :-
    ( Ap = ap(_, _, BK, _) -> BK \== AK ; true ),
    ( Rj = rj(_, BK2, _) -> BK2 \== AK ; true ).

inv7(S) :-
    S = st(_, _, P, _, _, _, _), request_count(S, NR),
    forall(member(_-p(_, _, _, F, _), P), F =< NR).
inv8(S) :-
    S = st(_, _, P, R, _, _, _),
    forall(( member(K-p(Acct, Role, Reg, From, _), P), member(req(I, AA, AK, AG, _, _, _), R), AK == K, I >= From ),
           ( AA == Acct, Role == agent, AG == Reg )).
inv9(S) :-
    S = st(Pm, _, P, _, _, _, _), params_get(max_pending_per_key, Pm, MaxP),
    forall(member(K-p(_, _, _, _, Pend), P), ( pend_count(S, K, N), N =:= Pend, Pend =< MaxP )).
inv11(S) :-
    S = st(_, _, P, _, _, G, V),
    findall(Reg, member(_-p(_, _, Reg, _, _), P), Regs),
    forall(member(Reg, Regs), ( Reg < G, \+ memberchk(Reg, V) )),
    sort(Regs, SR), length(SR, N), length(Regs, N).
inv14(S) :-
    S = st(_, _, _, R, _, G, _),
    forall(member(req(_, _, _, AG, _, Ap, Rj), R),
           ( AG < G,
             ( Ap = ap(_, _, _, BG) -> BG < G ; true ),
             ( Rj = rj(_, _, BG2) -> BG2 < G ; true ) )).
inv16(S) :-
    S = st(_, _, P, R, _, _, _),
    forall(( member(K-p(Acct, Role, Reg, _, _), P), member(Rq, R) ),
           reg_binding(K, Acct, Role, Reg, Rq)).
reg_binding(K, Acct, Role, Reg, req(_, AA, AK, AG, _, Ap, Rj)) :-
    ( AG == Reg -> ( K == AK, Acct == AA, Role == agent ) ; true ),
    ( Ap = ap(_, BA, BK, BG), BG == Reg -> ( K == BK, Acct == BA, Role == approver ) ; true ),
    ( Rj = rj(BA2, BK2, BG2), BG2 == Reg -> ( K == BK2, Acct == BA2, Role == approver ) ; true ).
lem2(S) :-
    S = st(_, _, _, R, L, _, _), length(L, NL), length(R, NR),
    findall(x, ( member(Rq, R), arg(6, Rq, ap(_, _, _, _)) ), As), length(As, NA),
    NL =:= NA, NA =< NR.
lem3(S) :-
    S = st(Pm, _, _, R, L, _, _), params_get(max_u, Pm, U),
    (   member(Rq, R), arg(6, Rq, none)
    ->  length(L, NL), length(R, NR), NL < NR, NR =< U
    ;   true
    ).

% Approvable (TLA-LIVE-2, README "Approving or rejecting frees a slot", D9 "every
% accepted request stays approvable"): each pending request is approvable and
% rejectable by every approver key bound to another account.
approvable(S) :-
    S = st(_, _, P, R, _, _, _),
    forall(( member(req(I, AA, _, _, Act, _, _), R), status(S, I, pending),
             member(K-p(B, approver, _, _, _), P), B \== AA ),
           ( step(S, approve(c(B, B, K), I, Act), ok(_), _),
             step(S, reject(c(B, B, K), I), ok(_), _) )).

%%% ========================================================
%%% Step properties (strategy 5.3, 5.4) on successful edges
%%% ========================================================

edge_violation(S0, Op, Res, S1, viol(Id, S0, Op)) :-
    edge_prop(Id, S0, Op, Res, S1, Ok), \+ call(Ok).

edge_prop('HIST-1', S0, _, _, S1, hist1(S0, S1)).
edge_prop('HIST-2', S0, _, _, S1, hist2(S0, S1)).
edge_prop('HIST-3', st(_, _, _, _, L0, _, _), _, _, st(_, _, _, _, L1, _, _), append(L0, _, L1)).
edge_prop('HIST-4', S0, Op, _, S1, hist4(S0, Op, S1)).
edge_prop('HIST-5', S0, _, _, S1, hist5(S0, S1)).
edge_prop('HIST-6', S0, Op, _, S1, hist6(S0, Op, S1)).
edge_prop('HIST-7', S0, Op, _, S1, hist7(S0, Op, S1)).
edge_prop('HIST-8', S0, _, _, S1, terminal(void, S0, S1)).
edge_prop('HIST-9', S0, _, _, S1, terminal(rejected, S0, S1)).
edge_prop('HIST-10', S0, Op, _, S1, hist10(S0, Op, S1)).
edge_prop('TR-2', S0, Op, _, _, decided_once(S0, Op)).
edge_prop('TR-3', S0, Op, _, _, no_revival(S0, Op)).
edge_prop('TR-6', S0, Op, _, S1, phi_step(S0, Op, S1)).
edge_prop('TX-0', S0, _, Res, S1, ( Res = ok(_) ; S1 == S0 )).

hist1(st(_, _, _, R0, _, _, _), st(_, _, _, R1, _, _, _)) :-
    length(R0, N), length(Pre, N), append(Pre, _, R1),
    maplist(same_content, R0, Pre).
same_content(req(I, AA, AK, AG, A, _, _), req(I2, AA2, AK2, AG2, A2, _, _)) :-
    I == I2, AA == AA2, AK == AK2, AG == AG2, A == A2.

hist2(st(_, _, _, R0, _, _, _), st(_, _, _, R1, _, _, _)) :-
    forall(( nth0(I, R0, req(_, _, _, _, _, Ap, Rj)), nth0(I, R1, req(_, _, _, _, _, Ap1, Rj1)) ),
           ( ( Ap == none ; Ap1 == Ap ), ( Rj == none ; Rj1 == Rj ) )).

hist4(S0, Op, S1) :-
    request_count(S0, R0), request_count(S1, R1), approval_count(S0, L0), approval_count(S1, L1),
    DR is R1 - R0, DL is L1 - L0,
    op_kind(Op, Kind),
    ( Kind == request_action -> DR =:= 1 ; DR =:= 0 ),
    ( Kind == approve -> DL =:= 1 ; DL =:= 0 ).

hist5(S0, S1) :-
    request_count(S0, NR),
    forall(( between(1, NR, I1), I is I1 - 1, approval(S0, I, some(P)) ), approval(S1, I, some(P))).

hist6(st(_, O0, P0, _, _, _, _), Op, st(_, O1, P1, _, _, _, _)) :-
    O0 == O1,
    op_kind(Op, Kind),
    (   ( Kind == add_principal ; Kind == revoke_key ) -> true
    ;   pend_only_change(P0, P1)
    ).
pend_only_change(P0, P1) :-
    length(P0, N), length(P1, N),
    maplist(same_but_pend, P0, P1, Ds),
    findall(c, member(changed, Ds), Changed), length(Changed, NC), NC =< 1.
same_but_pend(K-p(A, Ro, Rg, F, Pd), K1-p(A1, Ro1, Rg1, F1, Pd1), D) :-
    K == K1, A == A1, Ro == Ro1, Rg == Rg1, F == F1,
    ( Pd == Pd1 -> D = same ; D = changed ).

hist7(st(_, _, _, R0, L0, _, _), Op, st(_, _, _, R1, L1, _, _)) :-
    op_kind(Op, Kind),
    (   ( Kind == add_principal ; Kind == revoke_key ) -> R0 == R1, L0 == L1
    ;   Kind == reject -> L0 == L1
    ;   true
    ).

terminal(St, S0, S1) :-
    request_count(S0, NR),
    forall(( between(1, NR, I1), I is I1 - 1, status(S0, I, St) ), status(S1, I, St)).

hist10(st(_, _, _, _, _, G0, V0), Op, st(_, _, _, _, _, G1, V1)) :-
    op_kind(Op, Kind),
    ( Kind == add_principal -> G1 =:= G0 + 1 ; G1 =:= G0 ),
    length(V0, N0), length(V1, N1),
    ( Kind == revoke_key -> N1 =:= N0 + 1 ; N1 =:= N0 ),
    ord_subset(V0, V1).

decided_once(S0, Op) :-
    (   ( Op = approve(_, I, _) ; Op = reject(_, I) )
    ->  request_at(S0, I, req(_, _, _, _, _, none, none))
    ;   true
    ).

no_revival(S0, Op) :-
    (   ( Op = approve(_, I, _) ; Op = reject(_, I) ) -> status(S0, I, pending) ; true ).

% TR-6: Phi = sum over agent keys of (MAXP - pend).
phi(st(Pm, _, P, _, _, _, _), Phi) :-
    params_get(max_pending_per_key, Pm, MaxP),
    findall(D, ( member(_-p(_, agent, _, _, Pd), P), D is MaxP - Pd ), Ds),
    sum_list(Ds, Phi).
phi_step(S0, Op, S1) :-
    phi(S0, F0), phi(S1, F1), D is F1 - F0,
    S0 = st(Pm, _, _, _, _, _, _), params_get(max_pending_per_key, Pm, MaxP),
    (   Op = request(_, _)       -> D =:= -1
    ;   Op = approve(_, _, _)    -> D =:= 1
    ;   Op = reject(_, _)        -> D =:= 1
    ;   Op = add(_, _, _, agent) -> D =:= MaxP
    ;   Op = add(_, _, _, approver) -> D =:= 0
    ;   D =< 0
    ).

%%% ========================================================
%%% Acceptance
%%% ========================================================

%% mc_check(+Result, -Failures, -Notes): Failures = [] means the profile passes.
mc_check(mc(Name, _, _, _, Errors, Coverage, Violations, _), Failures, Notes) :-
    findall(K-E, ( guard(K, _, E, _), \+ expected_unreached(Name, K-E) ), Need0),
    sort(Need0, Need),
    ord_subtract(Need, Errors, Missing),
    findall(K-E, ( must_not_reach(Name, K-E), memberchk(K-E, Errors) ), Forbidden),
    required_coverage(Name, Cov0), sort(Cov0, Cov),
    ord_subtract(Cov, Coverage, MissingCov),
    findall(Id, member(viol(Id, _), Violations), VI1),
    findall(Id, member(viol(Id, _, _), Violations), VI2),
    append(VI1, VI2, VIds0), sort(VIds0, VIds),
    findall(F, ( ( Missing \== [], F = missing_errors(Missing) )
               ; ( Forbidden \== [], F = forbidden_errors(Forbidden) )
               ; ( MissingCov \== [], F = missing_coverage(MissingCov) )
               ; ( VIds \== [], F = violations(VIds) ) ), Failures),
    findall(K-E, ( expected_unreached(Name, K-E), memberchk(K-E, Errors) ), Extra),
    Notes = [reached_beyond_requirement(Extra)].

format_mc(mc(Name, Depth, NS, NE, Errors, Coverage, Violations, Ms)) :-
    length(Errors, NErr), length(Violations, NV),
    format("  ~a: depth ~d, ~d states, ~d edges, ~d ms~n", [Name, Depth, NS, NE, Ms]),
    format("  ~a: ~d (op, error) pairs reached: ~w~n", [Name, NErr, Errors]),
    format("  ~a: coverage ~w; ~d violations~n", [Name, Coverage, NV]),
    (   Violations = [V | _] -> format("  ~a: first violation ~w~n", [Name, V]) ; true ).

%%% Wall-clock helper
now_ms(Ms) :-
    catch(( statistics(runtime, [T | _]), Ms is truncate(T) ), _, Ms = 0).
