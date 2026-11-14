%% test_mc1.pl -- MC-1: bounded exploration of the model's small universes
%%
%% PROP: MC-1 LIVE-2 LIVE-1 INV-WF INV-LEDGER INV-HARD INV-HEALTHY INV-DEP INV-VER
%%
%% wedge   (trace 0's config; a disturbing and an in-bounds observation):
%%         every invariant and step property holds on every reachable state and
%%         edge, AND some dispatched record is certified dead (F-1): no
%%         reachable state has it terminal. LIVE-2 fails here, as the brief says.
%% healthy (two recipes with a prerequisite, freshness, in-bounds observations):
%%         every property holds and no open record is dead (LIVE-2 within the bound).
%% reliance (F-2 scaled down: a hedge relying on a credit position's
%%         reservation; only in-bounds observations, so B = 0 throughout):
%%         every property holds (LIVE-1 included), AND with no disturbing
%%         observe an in-flight position's honest settle(false) is blocked
%%         (Bounds) once a hedge relies on its reservation. No record is
%%         certified dead: settle(true) stays possible, and a further loss
%%         reservation (beyond the record cap, so the truncation rule applies)
%%         can unblock the release by taking over the reliance (test_model F-2).
%%
%% Run: scryer-prolog test_mc1.pl -g "(catch(run_tests,E,(write(E),nl,halt(2))) -> halt(0) ; halt(1))" </dev/null
%% (about 40 s)

:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module('support/harness').

:- discontiguous(test/2).
:- use_module('../verification/model_check').

run_tests :- run_suite("shared-pool Prolog: MC-1 small model check", x).

report(R) :-
    R = mc1(Name, St, Ed, Tr, violations(Vs), DI, DR, W, hits(H), complete(C), RB),
    length(Vs, NV),
    note("~w: ~w ~w ~w violations(~d) ~w ~w complete(~w)", [Name, St, Ed, Tr, NV, DI, DR, C]),
    note("witness: ~q", [W]),
    note("~q", [RB]),
    note("results: ~q", [H]),
    (   NV > 0 -> forall(( nth1(K, Vs, V), K =< 10 ), note("VIOLATION ~q", [V])) ; true ).

ok_kinds(H, Ks) :- findall(K, member(K-ok-_, H), Ks0), sort(Ks0, Ks).

test('MC-1 wedge: properties hold and the F-1 dead record is found', (
    mc1_run(wedge, R), report(R),
    R = mc1(_, states(NS), _, _, violations(Vs), dead_inflight(count(ND, _)), _, witness(W), hits(H), complete(C), _),
    check(complete, C == true), check(states(NS), NS > 100),
    check(no_violations, Vs == []),
    check(f1_found, ND > 0),
    check(witness_shape, ( W = dead(record(0), _, Path),
                           Path = [observe(o, [12, 5], _) | _],
                           memberchk(submit(a1, 0, 1, _, _, _), Path),
                           memberchk(dispatch(a1, 0, _), Path) )),
    ok_kinds(H, Ks), check(ok_kinds(Ks), Ks == [ack, cancel, dispatch, observe, pause, settle, submit]) )).

test('MC-1 healthy: properties hold and no open record is dead (LIVE-2 within the bound)', (
    mc1_run(healthy, R), report(R),
    R = mc1(_, states(NS), _, _, violations(Vs), dead_inflight(count(ND, _)), dead_reserved(count(NR, _)), _, hits(H), complete(C),
            release_blocked(count(NB), _)),
    check(complete, C == true), check(states(NS), NS > 100),
    check(no_violations, Vs == []),
    check(no_dead_inflight, ND =:= 0), check(no_dead_reserved, NR =:= 0),
    check(no_release_blocked, NB =:= 0),
    ok_kinds(H, Ks), check(ok_kinds(Ks), Ks == [ack, cancel, dispatch, observe, pause, settle, submit]),
    findall(E, ( member(_-E-_, H), E \== ok ), Es0), sort(Es0, Es),
    note("errors reached: ~q", [Es]),
    forall(member(E, [unauthorized, paused, stale, snapshot_expired, expired, prerequisite, bounds, energy, invalid_state, pending]),
           check(error_reached(E), memberchk(E, Es))) )).

test('MC-1 reliance: properties hold; F-2 found without any disturbing observe (honest settle(false) blocked)', (
    mc1_run(reliance, R), report(R),
    R = mc1(_, states(NS), _, _, violations(Vs), dead_inflight(count(ND, _)), dead_reserved(count(NR, _)), _, hits(H), complete(C),
            release_blocked(count(NB), witness(WB))),
    check(complete, C == true), check(states(NS), NS > 100),
    check(no_violations, Vs == []),                     % INV-*, step properties, LIVE-1 on every B = 0 state
    note("dead in-flight ~d, dead reserved ~d (none certified: see header)", [ND, NR]),
    check(no_dead_inflight, ND =:= 0),                  % settle(true) always remains possible (LIVE-1)
    check(f2_release_blocked, NB > 0),
    check(f2_blocked_witness, ( WB = blocked(record(J), _, P2),
                                memberchk(submit(a1, 0, 1, _, _, _), P2),
                                memberchk(submit(a2, 1, 1, _, _, _), P2),
                                memberchk(dispatch(a1, J, _), P2),
                                forall(member(observe(_, Ov, _), P2), Ov == [60, 40]) )),
    check(f2_bounds_seen, memberchk(settle-bounds-_, H)) )).
