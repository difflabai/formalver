%% props.pl -- State invariants and step properties, shared by MC-1 and MC-2
%%
%% PROP: MC-1 MC-2 INV-WF INV-LEDGER INV-HARD INV-HEALTHY INV-DEP INV-VER LIVE-1
%% PROP: TX-0 TX-NOOP TX-VER AUTH-1 STALE-1 ADM-1 ADM-2 HARD-STEP DEP-1 LIFE-1
%% PROP: ASYNC-1 TERM-1 OBS-1 PAUSE-1
%%
%% Written from the property catalogue (brief) and the docs it cites. MC-1
%% applies them to every edge and state of the model's reachable graph; MC-2
%% applies them to the REAL core's conformance traces (the post-states are the
%% code's), so a violation there is a finding in the code.
%%
%% Ghost state g(Base, K0, Eff): Base = values at the last observe (or init),
%% K0 = number of records then, Eff = number of effective transitions.
%%
%%   ghost_init(+S, -G)
%%   ghost_step(+G0, +S0, +Op, +Result, +S1, -G1)
%%   state_violation(+S, +G, -V)               enumerates violated invariants
%%   edge_violation(+S0, +Op, +R, +S1, -V)     enumerates violated step properties
%%   live1_violation(+S, +G, -V)               LIVE-1 on a state (uses step/4)
%%   allowed_status_change(?From, ?To)          LIFE-1's status graph

:- module(props, [
    ghost_init/2,
    ghost_step/6,
    state_violation/3,
    edge_violation/5,
    live1_violation/3,
    allowed_status_change/2,
    base_violation/2
]).

:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(between)).
:- use_module('../requirements/pool_req').
:- use_module('../model/pool_machine').
:- use_module(util).

ghost_init(S, g(V, K, 0)) :- pool_values(S, V), pool_records(S, R), length(R, K).

ghost_step(g(B, K, E), S0, Op, R, S1, G1) :-
    (   R \= err(_), S1 \== S0
    ->  E1 is E + 1,
        (   Op = observe(_, _, _)
        ->  pool_values(S1, B1), pool_records(S1, Rs), length(Rs, K1), G1 = g(B1, K1, E1)
        ;   G1 = g(B, K, E1)
        )
    ;   G1 = g(B, K, E)
    ).

%% base_violation(+S-G, -B): B_i = PV_i(Base).
base_violation(S-g(Base, _, _), B) :-
    pool_config(S, config(_, _, Ms, _, _)), point_violation(Ms, Base, B).

%%% ========================================================
%%% State invariants
%%% ========================================================

state_violation(S, G, V) :-
    (   inv_wf(S, V)
    ;   inv_ledger(S, G, V)
    ;   inv_hard(S, G, V)
    ;   inv_dep(S, V)
    ;   inv_ver(S, G, V)
    ).

% INV-WF: values length n and bounded; record fields in range; #records <= 256.
inv_wf(S, 'INV-WF'(values)) :-
    pool_config(S, config(_, _, Ms, _, _)), pool_values(S, Vs),
    \+ ( length(Ms, N), length(Vs, N), constant(max_value, M, _),
         forall(member(X, Vs), ( X >= -M, X =< M )) ).
inv_wf(S, 'INV-WF'(record(J))) :-
    pool_config(S, C), pool_records(S, Rs),
    nth0(J, Rs, c(RI, U, _, St)),
    \+ ( recipe_of(C, RI, r(_, _, _, _, MU, _)), U >= 1, U =< MU, status(St) ).
inv_wf(S, 'INV-WF'(too_many_records)) :-
    pool_records(S, Rs), length(Rs, N), constant(max_records, M, _), N > M.

% INV-LEDGER: values = Base + sum_{j >= K0, not Cancelled} reserve_j u_j
%                          + sum_{j >= K0, Completed} complete_j u_j
% and every record before K0 is terminal (observe needs all terminal).
inv_ledger(S, g(Base, K0, _), 'INV-LEDGER'(Diff)) :-
    pool_config(S, config(_, _, _, _, Rcp)), pool_records(S, Rs), pool_values(S, Vs),
    ledger(Rs, 0, K0, Rcp, Base, Expect),
    Vs \== Expect,
    Diff = expected(Expect, got(Vs)).
inv_ledger(S, g(_, K0, _), 'INV-LEDGER'(open_before_base(J))) :-
    pool_records(S, Rs), nth0(J, Rs, c(_, _, _, St)), J < K0, open_status(St).

ledger([], _, _, _, V, V).
ledger([c(RI, U, _, St) | Cs], J, K0, Rcp, V0, V) :-
    (   J >= K0
    ->  nth0(RI, Rcp, r(_, _, Res, Com, _, _)),
        ( St \== cancelled -> vadd(V0, Res, U, V1) ; V1 = V0 ),
        ( St == completed  -> vadd(V1, Com, U, V2) ; V2 = V1 )
    ;   V2 = V0
    ),
    J1 is J + 1,
    ledger(Cs, J1, K0, Rcp, V2, V).

vadd([], [], _, []).
vadd([A | As], [D | Ds], U, [B | Bs]) :- B is A + D * U, vadd(As, Ds, U, Bs).

% INV-HARD: the envelope over open records is computable and EV_i <= B_i.
% INV-HEALTHY (corollary): B = 0 => EV = 0 (every subset of open completions lands in bounds).
inv_hard(S, G, V) :-
    pool_config(S, C), pool_records(S, Rs), pool_values(S, Vs),
    C = config(_, _, Ms, _, _),
    base_violation(S-G, B),
    (   envelope(C, Rs, Vs, none, none, Low, High)
    ->  interval_violation(Ms, Low, High, EV),
        nth0(I, EV, E), nth0(I, B, Bi), E > Bi,
        (   forall(member(X, B), X =:= 0) -> V = 'INV-HEALTHY'(metric(I), ev(E))
        ;   V = 'INV-HARD'(metric(I), ev(E), base(Bi))
        )
    ;   V = 'INV-HARD'(envelope_overflow)
    ).

% INV-DEP: every record's prerequisites are met by Completed records of lower index.
inv_dep(S, 'INV-DEP'(record(J))) :-
    pool_config(S, C), pool_records(S, Rs),
    nth0(J, Rs, c(RI, _, _, _)),
    recipe_of(C, RI, r(_, _, _, _, _, Req)),
    length(Pre, J), append(Pre, _, Rs),
    member(p(P, U), Req),
    completed_units(Pre, P, N), N < U.

% INV-VER: version = number of effective transitions.
inv_ver(S, g(_, _, E), 'INV-VER'(version(N), effective(E))) :- pool_version(S, N), N =\= E.

%%% ========================================================
%%% LIVE-1: B = 0 and version < u32::MAX => settle(executor, id, true) is Ok
%%% for every Dispatched/Active/Unknown record.
%%% ========================================================

live1_violation(S, G, 'LIVE-1'(record(J), Result)) :-
    base_violation(S-G, B), forall(member(X, B), X =:= 0),
    pool_version(S, N), u32_max(M), N < M,
    pool_records(S, Rs), pool_config(S, C),
    nth0(J, Rs, c(RI, _, _, St)), memberchk(St, [dispatched, active, unknown]),
    executor_of(C, RI, X),
    step(S, settle(X, J, true), Result, _),
    Result \== ok.

%%% ========================================================
%%% Step properties
%%% ========================================================

edge_violation(S0, Op, R, S1, V) :-
    (   R = err(_), S1 \== S0, V = 'TX-0'(state_changed)
    ;   R == ok, classify(S0, Op, stop(noop)), S1 \== S0, V = 'TX-NOOP'(state_changed)
    ;   is_ok(R), \+ classify(S0, Op, stop(noop)),
        pool_version(S0, N0), pool_version(S1, N1), N1 =\= N0 + 1,
        V = 'TX-VER'(N0, N1)
    ;   is_ok(R), S1 \== S0, \+ authorized(S0, Op), V = 'AUTH-1'(caller)
    ;   is_ok(R), Op = submit(_, _, _, Ver, _, _), pool_version(S0, N0), Ver =\= N0,
        V = 'STALE-1'(request(Ver), version(N0))
    ;   is_ok(R), Op = submit(_, _, _, _, _, _), adm_violation(S0, Op, S1, V)
    ;   is_ok(R), Op \= observe(_, _, _), hard_step_violation(S0, S1, V)
    ;   is_ok(R), Op = submit(_, RI, _, _, _, _), dep_violation(S0, RI, V)
    ;   life_violation(S0, Op, R, S1, V)
    ;   Op = ack(_, _), pool_values(S0, V0), pool_values(S1, V1), V0 \== V1, V = 'ASYNC-1'(values_changed)
    ;   term_violation(S0, Op, R, S1, V)
    ;   is_ok(R), Op = observe(_, _, _), S1 \== S0, pool_records(S0, Rs),
        member(c(_, _, _, St), Rs), open_status(St), V = 'OBS-1'(open_record)
    ;   is_ok(R), S1 \== S0, pool_config(S0, C0), pool_config(S1, C1), C0 \== C1, V = 'OBS-1'(config_changed)
    ;   pool_paused(S0, true), is_ok(R), S1 \== S0,
        ( Op = submit(_, _, _, _, _, _) ; Op = dispatch(_, _, _) ), V = 'PAUSE-1'(effect_while_paused)
    ).

is_ok(ok).
is_ok(ok(_)).

% AUTH-1: effective submit/dispatch => actor; cancel => actor or owner; settle =>
% executor; pause/observe => owner. Acknowledge has no caller (private callback).
authorized(S, submit(Ca, RI, _, _, _, _)) :- pool_config(S, C), actor_of(C, RI, A), Ca == A.
authorized(S, dispatch(Ca, Id, _)) :-
    pool_config(S, C), record_of(S, Id, c(RI, _, _, _)), actor_of(C, RI, A), Ca == A.
authorized(S, cancel(Ca, Id, _)) :-
    pool_config(S, C), record_of(S, Id, c(RI, _, _, _)), actor_of(C, RI, A), owner_of(C, O),
    ( Ca == A ; Ca == O ), !.
authorized(S, settle(Ca, Id, _)) :-
    pool_config(S, C), record_of(S, Id, c(RI, _, _, _)), executor_of(C, RI, X), Ca == X.
authorized(S, pause(Ca, _)) :- pool_config(S, C), owner_of(C, O), Ca == O.
authorized(S, observe(Ca, _, _)) :- pool_config(S, C), owner_of(C, O), Ca == O.
authorized(_, ack(_, _)).

% ADM-1: energy(post) <= energy(pre); ADM-2: in a violating state,
% energy(post + completion) < energy(pre).
adm_violation(S0, submit(_, RI, U, _, _, _), S1, V) :-
    pool_config(S0, C), pool_values(S0, V0), pool_values(S1, V1),
    energy(C, V0, E0), energy(C, V1, E1),
    (   E1 > E0, V = 'ADM-1'(E0, E1)
    ;   violating(C, V0), recipe_of(C, RI, r(_, _, _, Com, _, _)),
        vadd(V1, Com, U, VA), energy(C, VA, EA), EA >= E0, V = 'ADM-2'(E0, EA)
    ).

% HARD-STEP: every Ok except observe: PV_i(post) <= PV_i(pre).
hard_step_violation(S0, S1, 'HARD-STEP'(metric(I), P0, P1)) :-
    pool_config(S0, config(_, _, Ms, _, _)),
    pool_values(S0, V0), pool_values(S1, V1),
    point_violation(Ms, V0, PV0), point_violation(Ms, V1, PV1),
    nth0(I, PV1, P1), nth0(I, PV0, P0), P1 > P0.

% DEP-1: submit Ok => prerequisites met by Completed units in the pre-state.
dep_violation(S0, RI, 'DEP-1'(p(P, U), completed(N))) :-
    pool_config(S0, C), recipe_of(C, RI, r(_, _, _, _, _, Req)), pool_records(S0, Rs),
    member(p(P, U), Req), completed_units(Rs, P, N), N < U.

% LIFE-1: records append-only (one Reserved record per Ok submit), immutable
% id/recipe/units/expires_at, status changes only along the graph, at most one
% record changes per call, terminal absorbing.
allowed_status_change(reserved, dispatched).
allowed_status_change(reserved, cancelled).
allowed_status_change(dispatched, active).
allowed_status_change(dispatched, unknown).
allowed_status_change(unknown, active).
allowed_status_change(S, completed) :- memberchk(S, [dispatched, active, unknown]).
allowed_status_change(S, cancelled) :- memberchk(S, [dispatched, active, unknown]).

life_violation(S0, Op, R, S1, V) :-
    pool_records(S0, R0), pool_records(S1, R1),
    length(R0, N0), length(R1, N1),
    (   Op = submit(_, _, _, _, _, _), R = ok(_)
    ->  (   N1 =\= N0 + 1 -> V = 'LIFE-1'(not_appended)
        ;   last_of(R1, c(_, _, _, St)), St \== reserved -> V = 'LIFE-1'(new_not_reserved)
        ;   append(R0p, [_], R1), changed(R0, R0p, V)
        )
    ;   (   N1 =\= N0 -> V = 'LIFE-1'(record_count_changed)
        ;   changed(R0, R1, V)
        )
    ).

changed(R0, R1, V) :-
    (   nth0(J, R0, c(A, B, C, _)), nth0(J, R1, c(A1, B1, C1, _)),
        ( A \== A1 ; B \== B1 ; C \== C1 ), V = 'LIFE-1'(immutable_field(J))
    ;   nth0(J, R0, c(_, _, _, S0)), nth0(J, R1, c(_, _, _, S1)),
        S0 \== S1, \+ allowed_status_change(S0, S1), V = 'LIFE-1'(transition(J, S0, S1))
    ;   findall(J, ( nth0(J, R0, c(_, _, _, X)), nth0(J, R1, c(_, _, _, Y)), X \== Y ), Js),
        length(Js, K), K > 1, V = 'LIFE-1'(several_changed(Js))
    ).

% TERM-1: by the executor, the same terminal again is an Ok no-op; the opposite
% terminal is InvalidState.
term_violation(S0, settle(Ca, Id, Done), R, S1, V) :-
    pool_config(S0, C), record_of(S0, Id, c(RI, _, _, St)), executor_of(C, RI, X), Ca == X,
    (   ( Done == true, St == completed ; Done == false, St == cancelled )
    ->  \+ ( R == ok, S1 == S0 ), V = 'TERM-1'(repeat_not_noop(St), R)
    ;   ( Done == true, St == cancelled ; Done == false, St == completed )
    ->  R \== err(invalid_state), V = 'TERM-1'(conflict_not_rejected(St), R)
    ).
