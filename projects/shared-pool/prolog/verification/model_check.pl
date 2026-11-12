%% model_check.pl -- MC-1: bounded exploration of small universes through step/4
%%
%% PROP: MC-1 LIVE-2 LIVE-1 INV-WF INV-LEDGER INV-HARD INV-HEALTHY INV-DEP INV-VER
%% PROP: TX-0 TX-NOOP TX-VER AUTH-1 STALE-1 ADM-1 ADM-2 HARD-STEP DEP-1 LIFE-1
%% PROP: ASYNC-1 TERM-1 OBS-1 PAUSE-1
%%
%% A universe fixes a config, a finite set of times, observation vectors, a
%% record cap and the callers (the recipe's actors and executors, the owner,
%% and a stranger z). From init, every generated call is applied with step/4
%% (breadth first). Every edge is checked with props:edge_violation/5 and every
%% new state with props:state_violation/3 and props:live1_violation/3.
%%
%% Exploration state n(Pool, Clock, Ghost). Time is monotone (ASM-TIME): a call
%% uses a time >= Clock from the universe's list. The visited key drops the
%% version and the ghost's effect counter: guards read the version only through
%% equality with the request (submits are generated with the current version and
%% with a stale one) and u32::MAX (unreachable here), so states that differ only
%% in version are bisimilar. INV-VER is therefore checked per edge (TX-VER: +1
%% on every effective call, 0 otherwise), which is the induction step for it.
%%
%% Truncation: at the record cap no submit is generated; a state where some
%% submit would have been Ok is marked truncated.
%%
%% Dead records (LIVE-2): record J is dead in state S if J is open in S and no
%% state reachable from S has J terminal. A state that can reach a truncated
%% state is never certified dead (the cut-off part might help).
%%
%% Release blocked (F-2): a state whose ghost base is in bounds (B = 0, no
%% disturbing observe) in which the executor's settle(false) on an in-flight
%% record fails. Such a record still has settle(true), so it is not dead by
%% reachability; under ASM-EXEC (settle(false) only on definitive
%% nonexecution) it is the record the executor can never resolve honestly.
%%
%% Exploration stops at the first property violation (a violation fails the
%% run anyway; without the stop a mutated model can explode to max_states).
%%
%%   universe(Name, u(Config, Options))
%%   mc1_run(+Name, -Result)
%%   Result = mc1(Name, states(N), edges(E), truncated(T), violations(Vs),
%%                dead_inflight(D), dead_reserved(R), witness(Path), hits(H), complete(B),
%%                release_blocked(count(K), witness(Path2)))

:- module(model_check, [universe/2, mc1_run/2]).

:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(assoc)).
:- use_module(library(between)).
:- use_module(library(pairs)).
:- use_module('../requirements/pool_req').
:- use_module('../model/pool_machine').
:- use_module(props).
:- use_module(util).

%%% ========================================================
%%% Universes
%%% ========================================================

% F-1 (brief; conformance trace 0): one recipe whose completion pushes metric 0
% up by 2 and whose reservation pulls it down by 2. Observations: a disturbing
% one (metric 0 at 12 > max 10) and an in-bounds one.
universe(wedge, u(config(o, 0, [m(0, 10, 5), m(-100, 100, 5)], [t(1, 0, 1, target)],
                         [r(a1, x1, [-2, 0], [2, -5], 1, [])]),
                  [times([100, 200]), observations([[12, 5], [5, 5]]),
                   max_records(3), expiry(100), max_states(60000)])).
% Healthy: two recipes (the second requires a completed unit of the first),
% two actors and executors, freshness configured, only in-bounds observations.
universe(healthy, u(config(o, 100, [m(0, 10, 4), m(0, 6, 2)],
                          [t(0, 5, 1, target), t(1, 3, 2, deficit)],
                          [r(a1, x1, [1, 1], [1, -1], 2, []),
                           r(a2, x2, [2, 0], [-1, 1], 1, [p(0, 1)])]),
                    [times([100, 150, 250]), observations([[4, 2], [8, 5]]),
                     max_records(2), expiry(120), max_states(60000)])).

% F-2 scaled down (brief; risk fixture, docs/spec.md:46, 66): r0 is a credit
% position (reserves +20 selloff loss, -5 collateral, no completion effect),
% r1 a hedge whose completion takes 70 off the selloff loss. The hedge is only
% admissible while the position's reservation is counted (60 - 70 < 0); once
% it completes, releasing the position (cancel, or settle(false) after
% dispatch) would put the loss at -10: Bounds. Only in-bounds observations,
% so B = 0 throughout. Times 250 > expiry 200: an undispatched position dies.
universe(reliance, u(config(o, 0, [m(0, 100, 60), m(0, 40, 40)], [t(0, 80, 1, excess)],
                           [r(a1, x1, [20, -5], [0, 0], 1, []),
                            r(a2, x1, [0, -2], [-70, 0], 1, [])]),
                     [times([100, 250]), observations([[60, 40]]),
                      max_records(2), expiry(100), max_states(60000)])).

opt(Opts, Key) :- memberchk(Key, Opts).

%%% ========================================================
%%% Calls generated in a state
%%% ========================================================

ops(u(Cfg, Opts), n(S, Clock, _), Ops, AtCap) :-
    opt(Opts, times(Ts)), opt(Opts, observations(Obs)), opt(Opts, expiry(Ex)),
    opt(Opts, max_records(MaxR)),
    findall(T, ( member(T, Ts), T >= Clock ), Nows),
    pool_version(S, Ver), pool_records(S, Recs), length(Recs, NRec),
    Cfg = config(Owner, _, _, _, Rs), length(Rs, NR), NR1 is NR - 1,
    NRec1 is NRec - 1,
    findall(Op,
            ( member(RI, [0]), Op = submit(z, RI, 1, Ver, E, Clock), E is Clock + Ex
            ; Op = submit(A, 0, 1, V1, E, Clock), actor_of(Cfg, 0, A), V1 is Ver + 1, E is Clock + Ex
            ; between(0, NR1, RI), actor_of(Cfg, RI, A), recipe_of(Cfg, RI, r(_, _, _, _, MU, _)),
              between(1, MU, U), member(Now, Nows), E is Now + Ex,
              Op = submit(A, RI, U, Ver, E, Now)
            ), Subs),
    (   NRec >= MaxR -> AtCap = Subs, SubOps = [] ; AtCap = [], SubOps = Subs ),
    findall(Op,
            ( between(0, NRec1, Id), nth0(Id, Recs, c(RI, _, _, _)),
              actor_of(Cfg, RI, A), executor_of(Cfg, RI, X),
              (   member(Now, Nows), Op = dispatch(A, Id, Now)
              ;   member(B, [true, false]), Op = ack(Id, B)
              ;   member(Now, Nows), Op = cancel(A, Id, Now)
              ;   Op = cancel(Owner, Id, Clock)
              ;   member(B, [true, false]), Op = settle(X, Id, B)
              ;   Id =:= 0, ( Op = dispatch(z, Id, Clock) ; Op = cancel(z, Id, Clock) ; Op = settle(z, Id, true) )
              )
            ), RecOps),
    findall(Op,
            ( member(B, [true, false]), Op = pause(Owner, B)
            ; Op = pause(z, true)
            ; member(Vs, Obs), member(Now, Nows), Op = observe(Owner, Vs, Now)
            ; Obs = [Vs | _], Op = observe(z, Vs, Clock)
            ), AdmOps),
    append([SubOps, RecOps, AdmOps], Ops).

op_now(submit(_, _, _, _, _, N), N).
op_now(dispatch(_, _, N), N).
op_now(cancel(_, _, N), N).
op_now(observe(_, _, N), N).

key(n(pool(C, V, _, O, P, R), Clock, g(B, K, _)), k(C, V, O, P, R, Clock, B, K)).

%%% ========================================================
%%% Exploration
%%% ========================================================

mc1_run(Name, mc1(Name, states(NS), edges(NE), truncated(NT), violations(Vs),
                  dead_inflight(DI), dead_reserved(DR), witness(W), hits(Hits), complete(Done),
                  release_blocked(count(NB), witness(WB)))) :-
    universe(Name, U),
    U = u(Cfg, Opts),
    opt(Opts, times([T0 | _])),
    init_state(Cfg, T0, S0),
    ghost_init(S0, G0),
    N0 = n(S0, T0, G0),
    key(N0, K0),
    list_to_assoc([K0-0], Vis0),
    list_to_assoc([0-N0], Nodes0),
    findall(V, ( state_violation(S0, G0, V) ; live1_violation(S0, G0, V) ), IV0),
    findall(viol(0, init, V), member(V, IV0), IV),
    opt(Opts, max_states(Max)),
    explore(0, U, Max, x(1, Vis0, Nodes0, [], IV, [], [], []), x(NS, _, Nodes, Edges, Vs0, Par, Trunc, H0)),
    (   NS >= Max -> Done = false
    ;   Vs0 \== [] -> Done = stopped_at_violation
    ;   Done = true
    ),
    length(Edges, NE), length(Trunc, NT),
    sort(Vs0, Vs),
    msort_dup(H0, H1), tally(H1, Hits),
    list_to_assoc(Par, ParA),
    dead_records(NS, Nodes, Edges, Trunc, Dead),
    findall(Id-J, ( member(Id-J-St, Dead), memberchk(St, [dispatched, active, unknown]) ), DI0),
    findall(Id-J, member(Id-J-reserved, Dead), DR0),
    summarize(DI0, DI), summarize(DR0, DR),
    (   DI0 = [Id1-J1 | _] -> path_to(Id1, ParA, P1), W = dead(record(J1), Id1, P1)
    ;   DR0 = [Id2-J2 | _] -> path_to(Id2, ParA, P2), W = dead(record(J2), Id2, P2)
    ;   W = none
    ),
    findall(Id-J, ( between(0, NS, Id), Id < NS, get_assoc(Id, Nodes, n(S, _, G)),
                    release_blocked(S, G, J) ), RB),
    length(RB, NB),
    (   RB = [IdB-JB | _] -> path_to(IdB, ParA, PB), WB = blocked(record(JB), IdB, PB) ; WB = none ).

%% release_blocked(+S, +Ghost, -J): B = 0 and the executor's settle(J, false)
%% on the in-flight record J is rejected.
release_blocked(S, G, J) :-
    base_violation(S-G, B), forall(member(X, B), X =:= 0),
    pool_config(S, C), pool_records(S, Rs),
    nth0(J, Rs, c(RI, _, _, St)), memberchk(St, [dispatched, active, unknown]),
    executor_of(C, RI, Ex),
    step(S, settle(Ex, J, false), R, _), R \== ok.

summarize(L, count(N, records(Js))) :-
    length(L, N), findall(J, member(_-J, L), Js0), sort(Js0, Js).

explore(P, U, Max, X0, X) :-
    X0 = x(N, _, _, _, Vs, _, _, _),
    (   ( P >= N ; N >= Max ; Vs \== [] ) -> X = X0
    ;   X0 = x(_, _, Nodes, _, _, _, _, _),
        get_assoc(P, Nodes, Node),
        ops(U, Node, Ops, AtCap),
        expand_ops(Ops, P, Node, X0, X1),
        mark_truncated(AtCap, P, Node, X1, X2),
        P1 is P + 1,
        explore(P1, U, Max, X2, X)
    ).

mark_truncated([], _, _, X, X).
mark_truncated([Op | Ops], P, n(S, _, _), X0, X) :-
    (   catch(step(S, Op, R, _), _, fail), R = ok(_)
    ->  X0 = x(N, Vi, No, E, V, Pa, T, H), X = x(N, Vi, No, E, V, Pa, [P | T], H)
    ;   mark_truncated(Ops, P, n(S, _, _), X0, X)
    ).

expand_ops([], _, _, X, X).
expand_ops([Op | Ops], P, Node, X0, X) :-
    Node = n(S0, Clock, G0),
    X0 = x(N, Vis, Nodes, Es, Vs, Par, Tr, Hs),
    (   catch(step(S0, Op, R, S1), E, ( R = exception(E), S1 = S0 ))
    ->  true
    ;   R = no_result, S1 = S0
    ),
    findall(viol(P, Op, V),
            (   R = exception(Ex), V = exception(Ex)
            ;   R == no_result, V = no_result
            ;   edge_violation(S0, Op, R, S1, V)
            ), EVs),
    ghost_step(G0, S0, Op, R, S1, G1),
    ( op_now(Op, Now) -> Clock1 is max(Clock, Now) ; Clock1 = Clock ),
    N1 = n(S1, Clock1, G1),
    key(N1, K1),
    functor(Op, F, _), ( R = err(Er) -> Rk = Er ; R = ok(_) -> Rk = ok ; Rk = R ),
    (   get_assoc(K1, Vis, Id)
    ->  Vis1 = Vis, Nodes1 = Nodes, Par1 = Par, NN = N, SVs = []
    ;   Id = N, NN is N + 1,
        put_assoc(K1, Vis, Id, Vis1), put_assoc(Id, Nodes, N1, Nodes1),
        Par1 = [Id-(P-Op) | Par],
        findall(viol(Id, Op, V), ( state_violation(S1, G1, V) ; live1_violation(S1, G1, V) ), SVs)
    ),
    append([EVs, SVs, Vs], Vs1),
    X1 = x(NN, Vis1, Nodes1, [P-Id | Es], Vs1, Par1, Tr, [F-Rk | Hs]),
    expand_ops(Ops, P, Node, X1, X).

%%% ========================================================
%%% Dead records
%%% ========================================================

dead_records(NS, Nodes, Edges, Trunc, Dead) :-
    reverse_adjacency(Edges, Rev),
    findall(J, ( between(0, NS, I), I < NS, get_assoc(I, Nodes, n(S, _, _)),
                 pool_records(S, Rs), nth0(J, Rs, _) ), Js0),
    sort(Js0, Js),
    findall(Id-J-St,
            ( member(J, Js),
              findall(I, ( between(0, NS, I), I < NS, get_assoc(I, Nodes, n(S, _, _)),
                           pool_records(S, Rs), nth0(J, Rs, c(_, _, _, St0)), terminal(St0) ), Tg0),
              append(Tg0, Trunc, Tg),
              backward(Tg, Rev, Can),
              between(0, NS, Id), Id < NS, get_assoc(Id, Nodes, n(S, _, _)),
              pool_records(S, Rs), nth0(J, Rs, c(_, _, _, St)), open_status(St),
              \+ get_assoc(Id, Can, _)
            ), Dead0),
    sort(Dead0, Dead).

reverse_adjacency(Edges, Rev) :-
    empty_assoc(E0),
    foldl_rev(Edges, E0, Rev).
foldl_rev([], A, A).
foldl_rev([F-T | Es], A0, A) :-
    (   get_assoc(T, A0, L) -> put_assoc(T, A0, [F | L], A1) ; put_assoc(T, A0, [F], A1) ),
    foldl_rev(Es, A1, A).

backward(Targets, Rev, Can) :-
    empty_assoc(C0),
    bw(Targets, Rev, C0, Can).
bw([], _, C, C).
bw([I | Is], Rev, C0, C) :-
    (   get_assoc(I, C0, _) -> bw(Is, Rev, C0, C)
    ;   put_assoc(I, C0, t, C1),
        ( get_assoc(I, Rev, Ps) -> append(Ps, Is, Is1) ; Is1 = Is ),
        bw(Is1, Rev, C1, C)
    ).

path_to(0, _, []) :- !.
path_to(Id, Par, Path) :-
    get_assoc(Id, Par, P-Op),
    path_to(P, Par, Path0),
    append(Path0, [Op], Path).

