%% test_mc2.pl -- MC-2: every conformance trace of the real core through step/4
%%
%% PROP: MC-2 TX-0 TX-NOOP TX-VER AUTH-1 STALE-1 ADM-1 ADM-2 HARD-STEP DEP-1 LIFE-1
%% PROP: ASYNC-1 TERM-1 OBS-1 PAUSE-1 INV-WF INV-LEDGER INV-HARD INV-HEALTHY INV-DEP INV-VER LIVE-1
%% PROP: TX-SUBMIT TX-DISPATCH TX-ACK TX-CANCEL TX-SETTLE TX-PAUSE TX-OBSERVE
%%
%% 1. Replay: exact agreement on every result and post-state (divergences are
%%    reported with trace id and call index), and the step properties and
%%    invariants hold on the real core's own traces.
%% 2. Vacuity guards: a corrupted trace is detected as a divergence; each step
%%    property checker fires on a real call with one planted fault and is silent
%%    on the unmodified call.
%%
%% Run: scryer-prolog test_mc2.pl -g "(catch(run_tests,E,(write(E),nl,halt(2))) -> halt(0) ; halt(1))" </dev/null

:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module('support/harness').

:- discontiguous(test/2).
:- use_module('../requirements/pool_req').
:- use_module('../model/pool_machine').
:- use_module('../verification/traces').
:- use_module('../verification/props').
:- use_module('../verification/mc2').

run_tests :- run_suite("shared-pool Prolog: MC-2 trace replay", x).

%% load_trace(+N, -Trace): trace N of the checked-in file.
load_trace(N, T) :-
    trace_file(F),
    catch(fold_traces(F, find_trace(N), none, _), found(T), true),
    nonvar(T).
find_trace(N, T, A, A) :- T = trace(M, _, _, _, _), ( M =:= N -> throw(found(T)) ; true ).

%% call_at(+N, +I, -S0, -Op, -R, -S1): the I-th call of trace N (1-based).
call_at(N, I, S0, Op, R, S1) :-
    load_trace(N, trace(_, Cfg, _, Init, Calls)),
    nth1(I, Calls, call(Op, R, Post)),
    (   I =:= 1 -> Pre = Init ; I0 is I - 1, nth1(I0, Calls, call(_, _, Pre)) ),
    trace_to_pool(Cfg, Pre, S0), trace_to_pool(Cfg, Post, S1).

viols(S0, Op, R, S1, Vs) :- findall(V, edge_violation(S0, Op, R, S1, V), Vs).

%% planted(+Label, +RealTuple, +Planted, +Expected): the real call is clean; the
%% planted one is reported under Expected (a property name).
planted(Label, t(S0, Op, R, S1), t(P0, POp, PR, P1), Exp) :-
    viols(S0, Op, R, S1, V0), check(real_clean(Label, V0), V0 == []),
    viols(P0, POp, PR, P1, Vs),
    note("~w: ~q", [Label, Vs]),
    check(fires(Label, Exp), ( member(V, Vs), functor(V, Exp, _) )).

set_version(pool(C, V, _, O, P, R), N, pool(C, V, N, O, P, R)).
set_values(pool(C, _, N, O, P, R), V, pool(C, V, N, O, P, R)).
set_records(pool(C, V, N, O, P, _), R, pool(C, V, N, O, P, R)).

%%% ========================================================
%%% Replay
%%% ========================================================

test('MC-2: all traces replay with exact agreement and no property violation', (
    trace_file(F),
    mc2_run(F, mc2(NT, NC, Divs, Viols, Hits)),
    length(Divs, ND), length(Viols, NV),
    note("traces ~d, calls ~d, divergences ~d, violations ~d", [NT, NC, ND, NV]),
    note("results seen: ~q", [Hits]),
    (   ND > 0 -> forall(( nth1(K, Divs, D), K =< 10 ), note("DIVERGENCE ~q", [D])) ; true ),
    (   NV > 0 -> forall(( nth1(K, Viols, V), K =< 10 ), note("VIOLATION ~q", [V])) ; true ),
    check(traces(NT), NT >= 208), check(calls(NC), NC >= 8000),
    check(divergences(ND), ND =:= 0), check(violations(NV), NV =:= 0) )).

% Non-vacuity of the replay: every op kind succeeds somewhere and the traces
% reach every error the code can return from an INV state. Full and
% Arithmetic come from the generator's appended traces 206 (arith: add and
% envelope at the 1e6 value bound) and 207 (full: 256 records).
test('MC-2 coverage: every op kind Ok and every reachable error', (
    trace_file(F),
    mc2_run(F, mc2(_, _, _, _, Hits)),
    findall(K, member(K-ok-_, Hits), Ks0), sort(Ks0, Ks),
    findall(E, ( member(_-E-_, Hits), E \== ok ), Es0), sort(Es0, Es),
    note("ok kinds ~q", [Ks]), note("errors ~q", [Es]),
    check(kinds, Ks == [ack, cancel, dispatch, observe, pause, settle, submit]),
    forall(member(E, [unauthorized, paused, stale, expired, snapshot_expired, invalid_recipe,
                      invalid_units, prerequisite, bounds, energy, invalid_state, not_found, pending,
                      full, arithmetic]),
           check(error_seen(E), memberchk(E, Es))) )).

test('MC-2 F-1: trace 0 is the brief\'s wedge, replayed exactly', (
    load_trace(0, T), mc2_replay_trace(T, r(NC, Divs, Viols, _), Final),
    note("trace 0: ~d calls, final ~q", [NC, Final]),
    Divs == [], Viols == [],
    T = trace(_, _, _, _, Calls),
    findall(Op-R, member(call(Op, R, _), Calls), ORs),
    memberchk(settle(x1, 0, true)-err(bounds), ORs),
    memberchk(settle(x1, 0, false)-err(bounds), ORs),
    memberchk(observe(o, [5, 5], 103)-err(pending), ORs) )).

test('MC-2 detects a corrupted trace (result and post-state), with trace id and index', (
    load_trace(0, trace(N, Cfg, Now, Init, Calls)),
    nth1(5, Calls, call(Op, _, Post), Rest),
    nth1(5, Calls1, call(Op, ok, Post), Rest),
    mc2_replay_trace(trace(N, Cfg, Now, Init, Calls1), r(_, D1, _, _), _),
    note("result corrupted: ~q", [D1]),
    check(result_div, D1 = [div(0, 5, settle(x1, 0, true), code(ok, _), model(err(bounds), _))]),
    Post = s(V, Ver, O, P, R), Ver1 is Ver + 1,
    nth1(3, Calls, call(Op3, R3, _), Rest3),
    nth1(3, Calls2, call(Op3, R3, s(V, Ver1, O, P, R)), Rest3),
    mc2_replay_trace(trace(N, Cfg, Now, Init, Calls2), r(_, D2, _, _), _),
    check(state_div, member(div(0, 3, _, _, _), D2)) )).

%%% ========================================================
%%% Planted faults: each property checker fires (vacuity guard)
%%% ========================================================
%% Trace 4 (hiring): 1 submit err(energy); 2 submit ok(0); 3 submit ok(1);
%% 4 submit err(prerequisite); 5 dispatch ok; 11 settle(x1,0,true) ok;
%% 12 pause(o,true) ok; 14 ack(1,true) ok (a Reserved record: ignored).

test('TX-0 fires when an error changes state', (
    call_at(4, 1, S0, Op, R, S1), pool_version(S1, N), N1 is N + 1, set_version(S1, N1, P1),
    planted('TX-0', t(S0, Op, R, S1), t(S0, Op, R, P1), 'TX-0') )).

test('TX-NOOP fires when an ignored acknowledgment bumps version', (
    call_at(4, 14, S0, Op, R, S1), check(is_noop, S1 == S0),
    pool_version(S1, N), N1 is N + 1, set_version(S1, N1, P1),
    planted('TX-NOOP', t(S0, Op, R, S1), t(S0, Op, R, P1), 'TX-NOOP') )).

test('TX-VER fires on a double version bump', (
    call_at(4, 2, S0, Op, R, S1), pool_version(S1, N), N1 is N + 1, set_version(S1, N1, P1),
    planted('TX-VER', t(S0, Op, R, S1), t(S0, Op, R, P1), 'TX-VER') )).

test('AUTH-1 fires on an effective submit by a non-actor', (
    call_at(4, 2, S0, Op, R, S1), Op = submit(_, RI, U, V, E, Now),
    planted('AUTH-1', t(S0, Op, R, S1), t(S0, submit(z, RI, U, V, E, Now), R, S1), 'AUTH-1') )).

test('STALE-1 fires on an accepted request at another version', (
    call_at(4, 2, S0, Op, R, S1), Op = submit(A, RI, U, _, E, Now),
    planted('STALE-1', t(S0, Op, R, S1), t(S0, submit(A, RI, U, 7, E, Now), R, S1), 'STALE-1') )).

test('ADM-1 fires when an admitted reservation raises energy', (
    call_at(4, 2, S0, Op, R, S1), pool_values(S1, [_ | Vt]), set_values(S1, [9 | Vt], P1),
    planted('ADM-1', t(S0, Op, R, S1), t(S0, Op, R, P1), 'ADM-1') )).

test('HARD-STEP fires when an Ok call moves a metric out of bounds', (
    call_at(4, 2, S0, Op, R, S1), pool_values(S1, [A, B, C, _ | Vt]), set_values(S1, [A, B, C, -1 | Vt], P1),
    planted('HARD-STEP', t(S0, Op, R, S1), t(S0, Op, R, P1), 'HARD-STEP') )).

test('DEP-1 fires when a submit without prerequisites is admitted', (
    call_at(4, 4, S0, Op, R, S1), Op = submit(_, RI, U, _, E, _),
    pool_records(S0, Rs), append(Rs, [c(RI, U, E, reserved)], Rs1), set_records(S0, Rs1, Q),
    pool_version(S0, N), N1 is N + 1, set_version(Q, N1, P1), length(Rs, Id),
    planted('DEP-1', t(S0, Op, R, S1), t(S0, Op, ok(Id), P1), 'DEP-1') )).

test('LIFE-1 fires on a Reserved -> Completed jump', (
    call_at(4, 5, S0, Op, R, S1), pool_records(S1, [c(A, B, C, _) | Rt]), set_records(S1, [c(A, B, C, completed) | Rt], P1),
    planted('LIFE-1', t(S0, Op, R, S1), t(S0, Op, R, P1), 'LIFE-1') )).

test('ASYNC-1 fires when an acknowledgment changes values', (
    call_at(4, 5, _, _, _, D), step(D, ack(0, true), ok, D1),
    pool_values(D1, [X | Vt]), X1 is X + 1, set_values(D1, [X1 | Vt], P1),
    planted('ASYNC-1', t(D, ack(0, true), ok, D1), t(D, ack(0, true), ok, P1), 'ASYNC-1') )).

test('TERM-1 fires when a repeated completion is rejected', (
    call_at(4, 11, _, _, _, C), step(C, settle(x1, 0, true), R, C1), check(noop, ( R == ok, C1 == C )),
    planted('TERM-1', t(C, settle(x1, 0, true), ok, C), t(C, settle(x1, 0, true), err(invalid_state), C), 'TERM-1') )).

test('OBS-1 fires on an observe accepted with open records', (
    call_at(4, 3, _, _, _, S), step(S, observe(o, [1, 1, 1, 1, 1, 1, 1, 3], 150), R, S1), check(pending, R == err(pending)),
    S = pool(Cf, _, N, _, P, Rs), N1 is N + 1, P1 = pool(Cf, [1, 1, 1, 1, 1, 1, 1, 3], N1, 150, P, Rs),
    planted('OBS-1', t(S, observe(o, [1, 1, 1, 1, 1, 1, 1, 3], 150), R, S1),
                     t(S, observe(o, [1, 1, 1, 1, 1, 1, 1, 3], 150), ok, P1), 'OBS-1') )).

test('PAUSE-1 fires on a dispatch effective while paused', (
    call_at(4, 12, _, _, _, S), check(paused, pool_paused(S, true)),
    step(S, dispatch(a2, 1, 120), R, S1), check(rejected, R == err(paused)),
    pool_records(S, [C0, c(A, B, E, reserved)]), pool_version(S, N), N1 is N + 1,
    set_records(S, [C0, c(A, B, E, dispatched)], Q), set_version(Q, N1, P1),
    planted('PAUSE-1', t(S, dispatch(a2, 1, 120), R, S1), t(S, dispatch(a2, 1, 120), ok, P1), 'PAUSE-1') )).

test('ADM-2 fires when a recovery reservation does not recover', (
    load_trace(5, trace(_, Cfg, _, _, _)),
    init_state(Cfg, 100, R0), step(R0, observe(o, [110, 40, 30, 40], 100), ok, R1),
    Op = submit(a2, 3, 1, 1, 200, 100), step(R1, Op, ok(0), R2),
    set_values(R2, [130, 40, 30, 38], P2),
    planted('ADM-2', t(R1, Op, ok(0), R2), t(R1, Op, ok(0), P2), 'ADM-2') )).
