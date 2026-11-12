%% test_model.pl -- unit tests of step/4 (the reference semantics)
%%
%% PROP: TX-SUBMIT TX-DISPATCH TX-ACK TX-CANCEL TX-SETTLE TX-PAUSE TX-OBSERVE
%% PROP: TERM-1 PAUSE-1 DEP-1 ADM-2 RD-PREVIEW RD-BEST LIVE-1 MC-1
%%
%% Each test cites the doc line it exercises. The F-1 test replays the brief's
%% witness (conformance trace 0) call by call; F-2..F-6 have step/4 witnesses
%% on the fixture configs (the model agrees with the real core on all 8,771
%% trace calls, MC-2; the core reproducers are in the brief's find phase).
%%
%% Run: scryer-prolog test_model.pl -g "(catch(run_tests,E,(write(E),nl,halt(2))) -> halt(0) ; halt(1))" </dev/null

:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(between)).
:- use_module('support/harness').

:- discontiguous(test/2).
:- use_module('../requirements/pool_req').
:- use_module('../model/pool_machine').
:- use_module('../verification/props').

run_tests :- run_suite("shared-pool Prolog: step/4 unit tests", x).

%%% Configs (trace configs 0, 3, 4, 5 of conformance/traces/core.txt)
cfg(wedge, config(o, 0, [m(0, 10, 5), m(-100, 100, 5)], [t(1, 0, 1, target)],
                  [r(a1, x1, [-2, 0], [2, -5], 1, [])])).
cfg(inventory, config(o, 0, [m(4,20,6),m(0,20,6),m(0,20,0),m(4,20,6),m(0,20,6),m(0,20,0),m(0,20,0)],
                      [t(0,4,1,target),t(1,4,1,target),t(2,4,1,target)],
                      [r(a1,x1,[-1,1,0,-1,0,0,1],[0,0,0,0,1,0,-1],20,[]),
                       r(a2,x1,[-1,0,1,-1,0,0,1],[0,0,0,0,0,1,-1],20,[]),
                       r(a1,x1,[0,-1,1,0,-1,0,1],[0,0,0,0,0,1,-1],20,[])])).
cfg(hiring, config(o, 0, [m(0,10,0),m(0,10,0),m(0,10,0),m(0,10,5),m(0,2,2),m(0,7,0),m(0,7,0),m(3,3,3)],
                   [t(0,2,1,target),t(1,3,1,target),t(2,2,1,target)],
                   [r(a1,x1,[1,0,0,-1,0,1,0,0],[0,0,0,0,0,-1,1,0],20,[]),
                    r(a2,x1,[0,1,0,-1,0,1,0,0],[0,0,0,0,0,-1,1,0],20,[]),
                    r(a2,x1,[0,0,1,0,-1,1,0,0],[0,0,0,0,0,-1,1,0],20,[p(0,2),p(1,3)])])).
cfg(risk, config(o, 300, [m(0,100,60),m(0,80,40),m(0,60,30),m(0,40,40)],
                 [t(0,80,1,excess),t(1,60,1,excess),t(2,40,1,excess)],
                 [r(a1,x1,[20,5,0,-5],[0,0,0,0],20,[]),r(a2,x1,[10,0,5,-5],[0,0,0,0],20,[]),
                  r(a2,x1,[0,10,5,-5],[0,0,0,0],20,[]),r(a2,x1,[0,0,0,-2],[-10,0,0,0],20,[])])).

init(Name, S) :- cfg(Name, C), init_state(C, 100, S).

%% run(+S0, +[Op-Expected..], -S): every call gives Expected; an error leaves S unchanged.
run(S, [], S).
run(S0, [Op-Exp | Ps], S) :-
    step(S0, Op, R, S1),
    (   R = Exp -> true
    ;   note("~q: expected ~q, got ~q", [Op, Exp, R]), fail
    ),
    (   R = err(_) -> check(unchanged(Op), S1 == S0) ; true ),
    run(S1, Ps, S).

status_of(S, Id, St) :- record_of(S, Id, c(_, _, _, St)).
version(S, N) :- pool_version(S, N).

%%% ========================================================
%%% F-1 (brief; spec:23 recovery rule vs spec:46)
%%% ========================================================

test('F-1 witness: trace 0 call by call (settle both ways Bounds, cancel/observe Pending)', (
    init(wedge, S0),
    run(S0, [observe(o, [12, 5], 100) - ok,
             submit(a1, 0, 1, 1, 200, 100) - ok(0),
             dispatch(a1, 0, 101) - ok,
             ack(0, true) - ok,
             settle(x1, 0, true) - err(bounds),
             settle(x1, 0, false) - err(bounds),
             cancel(o, 0, 102) - err(pending),
             observe(o, [5, 5], 103) - err(pending)], S),
    pool_values(S, V), note("wedged values ~q, record 0 ~q", [V, active]),
    V == [10, 5], status_of(S, 0, active) )).

test('F-1: no single call by anyone makes the wedged record terminal', (
    init(wedge, S0),
    run(S0, [observe(o, [12, 5], 100) - ok, submit(a1, 0, 1, 1, 200, 100) - ok(0),
             dispatch(a1, 0, 101) - ok], S),
    forall(( member(C, [o, a1, x1, z]), member(Op, [settle(C, 0, true), settle(C, 0, false),
                                                     cancel(C, 0, 150), ack(0, true), ack(0, false)]) ),
           ( step(S, Op, _, S1), status_of(S1, 0, St), check(not_terminal(Op), \+ terminal(St)) )) )).

test('F-1 needs the disturbance: without the observe the same reservation is rejected', (
    init(wedge, S0),
    % healthy [5,5]: the reservation pulls metric 0 to 3, the completion envelope [3,5] fits;
    % the energy (term on metric 1) does not change, so it is admitted and settles fine.
    run(S0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), dispatch(a1, 0, 101) - ok,
             settle(x1, 0, true) - ok], S),
    status_of(S, 0, completed) )).

%%% ========================================================
%%% F-2..F-6 (brief, further confirmed findings)
%%% ========================================================

test('F-2 witness: risk fixture, no observe; the position\'s honest release fails Bounds (spec:46 vs spec:66)', (
    init(risk, R0),
    run(R0, [submit(a1, 0, 1, 0, 200, 100) - ok(0),          % credit position: selloff loss 60 -> 80
             submit(a2, 3, 7, 1, 200, 100) - ok(1),          % hedge x7: admissible only because 80 - 70 >= 0
             dispatch(a1, 0, 101) - ok, dispatch(a2, 1, 101) - ok,
             settle(x1, 1, true) - ok,                        % hedge fills: selloff loss 10
             settle(x1, 0, false) - err(bounds),              % definitive nonexecution of the position: 10 - 20 < 0
             cancel(o, 0, 102) - err(pending),
             observe(o, [60, 40, 30, 40], 102) - err(pending)], S),
    pool_values(S, V), note("blocked at ~q", [V]), V == [10, 45, 30, 21],
    cfg(risk, RC), check(healthy, \+ violating(RC, V)),        % no metric outside its bounds: B = 0
    % LIVE-1 is unaffected: settle(true) would succeed (it is not the truth under ASM-EXEC)
    check(live1, step(S, settle(x1, 0, true), ok, _)),
    % a further loss reservation takes the reliance over: the old position can now be
    % released, and the new one is blocked the same way (the liability only moves)
    pool_version(S, N),
    run(S, [submit(a1, 0, 1, N, 300, 102) - ok(2), settle(x1, 0, false) - ok,
            cancel(a1, 2, 103) - err(bounds)], _) )).

test('F-2 needs the reliance: without the hedge the position releases (spec:46)', (
    init(risk, R0),
    run(R0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), dispatch(a1, 0, 101) - ok,
             settle(x1, 0, false) - ok], S),
    pool_values(S, V), cfg(risk, config(_, _, Ms, _, _)), findall(I, member(m(_, _, I), Ms), V) )).

test('F-3 witness: 256 free submit+cancel cycles exhaust the records; Full survives observe (handoff:34)', (
    init(wedge, S0),
    cycles(256, S0, S),
    pool_records(S, Rs), length(Rs, NRec), check(full_size, NRec =:= 256),
    check(all_cancelled, forall(member(c(_, _, _, St), Rs), St == cancelled)),
    pool_version(S, N),
    run(S, [submit(a1, 0, 1, N, 200, 100) - err(full),
            observe(o, [5, 5], 101) - ok], S1),
    pool_version(S1, N1),
    run(S1, [submit(a1, 0, 1, N1, 300, 101) - err(full)], _) )).

cycles(0, S, S) :- !.
cycles(K, S0, S) :-
    pool_version(S0, N), pool_records(S0, Rs), length(Rs, Id),
    run(S0, [submit(a1, 0, 1, N, 200, 100) - ok(Id), cancel(a1, Id, 100) - ok], S1),
    K1 is K - 1, cycles(K1, S1, S).

test('F-4 witness: a config with actor = executor validates and its principal settles its own work (spec:64)', (
    Cfg = config(o, 0, [m(0, 10, 5), m(-100, 100, 5)], [t(1, 0, 1, target)],
                 [r(a1, a1, [-2, 0], [2, -5], 1, [])]),
    check(validates, valid_config(Cfg)),
    init_state(Cfg, 100, S0),
    run(S0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), dispatch(a1, 0, 101) - ok,
             settle(a1, 0, true) - ok], S),
    status_of(S, 0, completed) )).

test('F-5 witness: at version u32::MAX settlement, acknowledgment and unpausing all fail (handoff:34)', (
    init(wedge, W0), W0 = pool(C, _, _, O, _, _), u32_max(M),
    S = pool(C, [3, 5], M, O, true, [c(0, 1, 200, dispatched)]),
    run(S, [settle(x1, 0, true) - err(arithmetic), settle(x1, 0, false) - err(arithmetic),
            ack(0, true) - err(arithmetic), pause(o, false) - err(arithmetic),
            observe(o, [5, 5], 101) - err(pending)], _) )).

test('F-6 witness: max_age > 0 and one in-flight record stop admission and dispatch until it settles (spec:19, 37, 54)', (
    init(risk, R0),                                            % max_age 300, observed_at 100
    run(R0, [submit(a2, 3, 1, 0, 1000, 100) - ok(0), submit(a2, 3, 1, 1, 1000, 100) - ok(1),
             dispatch(a2, 0, 101) - ok,
             dispatch(a2, 1, 401) - err(snapshot_expired),
             submit(a2, 3, 1, 3, 1000, 401) - err(snapshot_expired),
             cancel(o, 1, 401) - ok,
             observe(o, [60, 40, 30, 40], 401) - err(pending),   % record 0 is still in flight
             settle(x1, 0, true) - ok,
             observe(o, [60, 40, 30, 40], 402) - ok,
             submit(a2, 3, 1, 6, 1000, 402) - ok(2)], _) )).

%%% ========================================================
%%% Admission (spec:19-25, api:26-28)
%%% ========================================================

test('submit: the first failing guard decides (paused before stale, expiry, caller)', (
    init(wedge, S0),
    run(S0, [pause(o, true) - ok, submit(z, 7, 0, 99, 1, 100) - err(paused)], _) )).

test('submit: each documented reason is reachable (api:28)', (
    init(hiring, H0),
    run(H0, [submit(a1, 0, 1, 1, 200, 100) - err(stale),
             submit(a1, 0, 1, 0, 100, 100) - err(expired),          % expires_at <= now
             submit(a1, 0, 1, 0, 86501, 100) - err(expired),        % > now + 86400
             submit(a1, 3, 1, 0, 200, 100) - err(invalid_recipe),
             submit(a2, 0, 1, 0, 200, 100) - err(unauthorized),
             submit(a1, 0, 0, 0, 200, 100) - err(invalid_units),
             submit(a1, 0, 21, 0, 200, 100) - err(invalid_units),
             submit(a2, 2, 1, 0, 200, 100) - err(prerequisite),
             submit(a1, 0, 6, 0, 200, 100) - err(bounds),           % free 5 - 6 < 0
             submit(a1, 0, 5, 0, 200, 100) - err(energy)], _),     % coverage 5 >> target 2
    init(risk, R0),
    run(R0, [submit(a1, 0, 1, 0, 500, 401) - err(snapshot_expired)], _) )).

test('submit: expiry and freshness boundaries (spec:19; CODE-ONLY boundaries)', (
    init(risk, R0),
    run(R0, [submit(a2, 3, 1, 0, 86500, 100) - ok(0)], _),          % now + 86400 accepted
    run(R0, [submit(a2, 3, 1, 0, 101, 100) - ok(0)], _),            % now + 1 accepted
    run(R0, [submit(a2, 3, 1, 0, 500, 400) - ok(0)], _),            % now = observed_at + max_age
    run(R0, [submit(a2, 3, 1, 0, 500, 401) - err(snapshot_expired)], _) )).

test('submit: saturating u64 expiry horizon (CODE-ONLY)', (
    init(wedge, S0), u64_max(U), Now is U - 10,
    step(S0, submit(a1, 0, 1, 0, U, Now), R, _), note("result ~q", [R]),
    R \== err(expired) )).

test('version overflow at u32::MAX is Arithmetic (handoff:34)', (
    init(wedge, S0), S0 = pool(C, V, _, O, P, Rs), u32_max(M), S1 = pool(C, V, M, O, P, Rs),
    run(S1, [pause(o, true) - err(arithmetic), submit(a1, 0, 1, M, 200, 100) - err(arithmetic),
             pause(z, true) - err(unauthorized)], _) )).

test('DEP-1/CASH-PREREQ: review needs Completed research >= 2 and implementation >= 3 (spec:64)', (
    init(hiring, H0),
    run(H0, [submit(a1, 0, 2, 0, 200, 100) - ok(0), dispatch(a1, 0, 101) - ok, ack(0, true) - ok,
             submit(a2, 1, 3, 3, 200, 101) - ok(1), dispatch(a2, 1, 102) - ok, settle(x1, 1, true) - ok,
             % research only Active (acknowledged, not completed): handoff:19
             submit(a2, 2, 1, 6, 200, 102) - err(prerequisite),
             settle(x1, 0, true) - ok,
             submit(a2, 2, 1, 7, 200, 103) - ok(2)], _) )).

test('ADM-2 recovery hedge admitted in a disturbed state; a loss trade is not (spec:23, spec:66)', (
    init(risk, R0),
    run(R0, [observe(o, [110, 40, 30, 40], 100) - ok,
             submit(a1, 0, 1, 1, 200, 100) - err(bounds),
             submit(a2, 3, 1, 1, 200, 100) - ok(0)], S),
    pool_values(S, V), note("after hedge reservation ~q", [V]),
    V == [110, 40, 30, 38] )).                                     % benefit only on completion

test('STOCK: transit is never available before receipt; the sum stays 12 (spec:62)', (
    init(inventory, I0),
    % "Depot to A" would raise the position energy (Energy); "Depot to B" lowers it
    run(I0, [submit(a1, 0, 2, 0, 200, 100) - err(energy), submit(a2, 1, 2, 0, 200, 100) - ok(0)], I1),
    pool_values(I1, V1), V1 = [_, _, P1, D1, A1, B1, T1], check(sum1, D1 + A1 + B1 + T1 =:= 12),
    check(position_moves_at_reservation, P1 =:= 2),
    check(no_credit_at_reservation, B1 =:= 0),
    run(I1, [dispatch(a2, 0, 101) - ok, settle(x1, 0, true) - ok], I2),
    pool_values(I2, V2), V2 = [_, _, _, D2, A2, B2, T2], check(sum2, D2 + A2 + B2 + T2 =:= 12),
    check(received, B2 =:= 2) )).

%%% ========================================================
%%% Lifecycle (spec:37-44, api:12-15)
%%% ========================================================

test('acknowledge: Dispatched->Unknown->Active; repeated status is Ok without a version bump (div-ack-noop-version)', (
    init(wedge, S0),
    run(S0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), dispatch(a1, 0, 101) - ok, ack(0, false) - ok], S1),
    status_of(S1, 0, unknown), version(S1, N1),
    run(S1, [ack(0, false) - ok], S2), check(same_state, S2 == S1), version(S2, N1),
    run(S2, [ack(0, true) - ok], S3), status_of(S3, 0, active), version(S3, N3), check(bump, N3 =:= N1 + 1),
    run(S3, [ack(0, true) - ok, ack(0, false) - ok], S4), check(active_ignores, S4 == S3),
    run(S0, [ack(0, true) - err(not_found)], _) )).

test('TERM-1: same terminal again is Ok no-op; the opposite is InvalidState (spec:43)', (
    init(wedge, S0),
    run(S0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), dispatch(a1, 0, 101) - ok,
             settle(x1, 0, true) - ok], S1),
    run(S1, [settle(x1, 0, true) - ok], S2), check(noop, S2 == S1),
    run(S1, [settle(x1, 0, false) - err(invalid_state), settle(a1, 0, true) - err(unauthorized),
             ack(0, true) - ok], S3),
    check(late_ack_ignored, S3 == S1) )).

test('cancel: actor or owner before dispatch; afterwards Pending (api:15; div-cancel-terminal-name)', (
    init(wedge, S0),
    run(S0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), cancel(z, 0, 101) - err(unauthorized),
             cancel(o, 0, 101) - ok, cancel(a1, 0, 102) - ok,             % idempotent
             submit(a1, 0, 1, 2, 300, 102) - ok(1), dispatch(a1, 1, 103) - ok,
             cancel(a1, 1, 104) - err(pending), settle(x1, 1, true) - ok,
             cancel(a1, 1, 105) - err(pending)], S),
    status_of(S, 0, cancelled), status_of(S, 1, completed) )).

test('dispatch: actor, unpaused, Reserved, unexpired, fresh (spec:37)', (
    init(risk, R0),
    run(R0, [submit(a2, 3, 1, 0, 200, 100) - ok(0),
             dispatch(a1, 0, 101) - err(unauthorized),
             pause(o, true) - ok, dispatch(a2, 0, 101) - err(paused), pause(o, false) - ok,
             dispatch(a2, 0, 200) - err(expired),
             dispatch(a2, 9, 101) - err(not_found)], R1),
    run(R1, [dispatch(a2, 0, 199) - ok, dispatch(a2, 0, 199) - err(invalid_state)], _),
    run(R0, [submit(a2, 3, 1, 0, 1000, 100) - ok(0), dispatch(a2, 0, 401) - err(snapshot_expired)], _) )).

test('PAUSE-1: pausing blocks admission and dispatch, not settlement, ack, cancel or observe (spec:54)', (
    init(wedge, S0),
    run(S0, [submit(a1, 0, 1, 0, 200, 100) - ok(0), submit(a1, 0, 1, 1, 200, 100) - ok(1),
             dispatch(a1, 0, 101) - ok, pause(o, true) - ok,
             submit(a1, 0, 1, 4, 200, 101) - err(paused), dispatch(a1, 1, 101) - err(paused),
             ack(0, true) - ok, settle(x1, 0, true) - ok, cancel(a1, 1, 102) - ok,
             observe(o, [5, 5], 103) - ok, pause(o, true) - ok], S),
    version(S, N), note("version ~d (pause to the same value still bumps: CODE-ONLY)", [N]), N =:= 9 )).

test('observe: owner, all terminal, bounded values of the right length (spec:54)', (
    init(wedge, S0),
    run(S0, [observe(a1, [5, 5], 100) - err(unauthorized),
             observe(o, [5], 100) - err(bounds), observe(o, [5, 5, 5], 100) - err(bounds),
             observe(o, [1000001, 5], 100) - err(bounds),
             observe(o, [-1000000, 1000000], 150) - ok], S),
    pool_values(S, V), V == [-1000000, 1000000],
    S = pool(_, _, _, 150, _, _) )).

%%% ========================================================
%%% Reads (spec:27; model only: not compared with the code)
%%% ========================================================

test('RD-PREVIEW (model): preview_allowed <=> submit Ok, over a request grid', (
    init(risk, R0),
    run(R0, [submit(a2, 3, 1, 0, 200, 100) - ok(0)], R1),
    forall(( member(S, [R0, R1]), member(A, [a1, a2, z]), between(0, 4, RI), between(0, 21, U) ),
           ( pool_version(S, V),
             (   preview_allowed(S, A, req(RI, U, V, 200, 100))
             ->  check(allowed_submits(A, RI, U), step(S, submit(A, RI, U, V, 200, 100), ok(_), _))
             ;   check(rejected_rejects(A, RI, U), step(S, submit(A, RI, U, V, 200, 100), err(_), _))
             ) )) )).

test('RD-BEST (model): best_quantity = brute-force minimum energy, ties to larger units', (
    forall(( member(F, [hiring, risk, inventory]), init(F, S), cfg(F, C),
             C = config(_, _, _, _, Rs), length(Rs, NR), NR1 is NR - 1,
             between(0, NR1, RI), actor_of(C, RI, A), member(U, [1, 3, 20, 150]) ),
           ( best_quantity(S, A, req(RI, U, 0, 200, 100), B),
             Hi is min(U, 100),
             findall(E-K, ( between(1, Hi, K), admissible(S, A, req(RI, K, 0, 200, 100)),
                            step(S, submit(A, RI, K, 0, 200, 100), ok(_), S1),
                            pool_values(S1, V1), energy(C, V1, E) ), Cs),
             (   Cs == [] -> check(none(F, RI, U), B == none)
             ;   findall(E, member(E-_, Cs), Es), min_list(Es, Emin),
                 findall(K, member(Emin-K, Cs), Ks), max_list(Ks, Kb),
                 check(best(F, RI, U, B, Kb), B == some(Kb))
             ) )) )).

%%% ========================================================
%%% Properties on hand-built states (the checkers can fire)
%%% ========================================================

test('LIVE-1 checker fires on a B = 0 state whose in-flight record cannot settle', (
    init(wedge, S0),
    run(S0, [observe(o, [12, 5], 100) - ok, submit(a1, 0, 1, 1, 200, 100) - ok(0),
             dispatch(a1, 0, 101) - ok], S),
    % the real ghost has base [12,5] (B_0 = 2): LIVE-1 does not apply
    check(no_live1_with_real_base, \+ live1_violation(S, g([12, 5], 0, 3), _)),
    % pretend the base were in bounds (B = 0): the checker must report it
    check(live1_fires, live1_violation(S, g([10, 5], 1, 3), _)) )).

test('INV checkers fire on corrupted states (INV-LEDGER, INV-HEALTHY, INV-WF, INV-DEP, INV-VER)', (
    init(hiring, H0),
    run(H0, [submit(a1, 0, 2, 0, 200, 100) - ok(0)], H1),
    ghost_init(H0, G0), ghost_step(G0, H0, submit(a1, 0, 2, 0, 200, 100), ok(0), H1, G1),
    check(clean, \+ state_violation(H1, G1, _)),
    H1 = pool(C, V, N, O, P, R),
    V = [V0 | Vt], V0b is V0 + 1,
    check(ledger, state_violation(pool(C, [V0b | Vt], N, O, P, R), G1, 'INV-LEDGER'(_))),
    check(wf, state_violation(pool(C, V, N, O, P, [c(0, 0, 200, reserved)]), G1, 'INV-WF'(_))),
    check(dep, state_violation(pool(C, V, N, O, P, [c(2, 1, 200, completed)]), g(V, 0, 1), 'INV-DEP'(_))),
    check(ver, state_violation(pool(C, V, 7, O, P, R), G1, 'INV-VER'(_, _))),
    init(wedge, W0),
    W0 = pool(WC, _, _, WO, WP, _),
    % the F-1 state with its real base is consistent (EV_0 = B_0 = 2) ...
    check(f1_consistent, \+ state_violation(pool(WC, [10, 5], 3, WO, WP, [c(0, 1, 200, dispatched)]),
                                             g([12, 5], 0, 3), _)),
    % ... with an in-bounds base it breaks INV-HEALTHY (and the ledger)
    check(healthy, state_violation(pool(WC, [10, 5], 1, WO, WP, [c(0, 1, 200, dispatched)]),
                                   g([10, 5], 0, 1), 'INV-HEALTHY'(_, _))),
    % INV-HARD with B /= 0: a loss trade open next to a hedge in a disturbed risk state
    init(risk, R0), R0 = pool(RC, _, _, RO, RP, _),
    check(hard, state_violation(pool(RC, [130, 45, 30, 33], 2, RO, RP, [c(3, 1, 200, dispatched), c(0, 1, 200, reserved)]),
                                g([110, 40, 30, 40], 0, 2), 'INV-HARD'(_, _, _))) )).

test('init_state: version 0, observed_at = now, unpaused, no records, initial values (CFG-1 model side)', (
    forall(cfg(_, C), ( init_state(C, 100, S), S = pool(C, V, 0, 100, false, []),
                        C = config(_, _, Ms, _, _), findall(I, member(m(_, _, I), Ms), V) )) )).

test('valid_config rejects out-of-range configs (CFG-2 model side)', (
    cfg(wedge, config(O, A, Ms, Ts, Rs)),
    check(ok, valid_config(config(O, A, Ms, Ts, Rs))),
    check(term_metric, \+ valid_config(config(O, A, Ms, [t(2, 0, 1, target)], Rs))),
    check(weight, \+ valid_config(config(O, A, Ms, [t(1, 0, 1001, target)], Rs))),
    check(effect_len, \+ valid_config(config(O, A, Ms, Ts, [r(a1, x1, [1], [1, 1], 1, [])]))),
    check(units, \+ valid_config(config(O, A, Ms, Ts, [r(a1, x1, [1, 1], [1, 1], 101, [])]))),
    check(self_prereq, \+ valid_config(config(O, A, Ms, Ts, [r(a1, x1, [1, 1], [1, 1], 1, [p(0, 1)])]))),
    check(initial, \+ valid_config(config(O, A, [m(0, 10, 11), m(0, 1, 0)], Ts, Rs))) )).

min_list([X | Xs], M) :- foldl_min(Xs, X, M).
foldl_min([], M, M).
foldl_min([X | Xs], M0, M) :- M1 is min(X, M0), foldl_min(Xs, M1, M).
max_list([X | Xs], M) :- foldl_max(Xs, X, M).
foldl_max([], M, M).
foldl_max([X | Xs], M0, M) :- M1 is max(X, M0), foldl_max(Xs, M1, M).
