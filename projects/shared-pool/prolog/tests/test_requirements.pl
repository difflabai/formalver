%% test_requirements.pl -- C-1..C-6: docs = code = TLA+, fixtures, traceability
%%
%% PROP: C-1 C-2 C-3 C-4 C-5 C-6
%%
%% Run (from prolog/tests or prolog/):
%%   scryer-prolog test_requirements.pl -g "(catch(run_tests,E,(write(E),nl,halt(2))) -> halt(0) ; halt(1))" </dev/null

:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module('support/harness').

:- discontiguous(test/2).
:- use_module('../requirements/pool_req').
:- use_module('../extracted/code_facts').
:- use_module('../extracted/tla_facts').
:- use_module('../verification/consistency').

run_tests :- run_suite("shared-pool Prolog: requirement checks C-1..C-6", x).

c_ok(Id) :-
    c_check(Id, R),
    (   R = ok(Info) -> note("~w ok: ~q", [Id, Info])
    ;   R = fail(Ps, Info),
        note("~w FAILED (~q)", [Id, Info]),
        forall(member(P, Ps), note("  problem: ~q", [P])),
        fail
    ).

test('C-1 authority matrix: api.md/spec:11 = shell attributes + core caller checks', c_ok('C-1')).
test('C-2 guard order: spec = code paths = TLA+ GuardOrder', c_ok('C-2')).
test('C-3 lifecycle: spec = code = TLA+ Edges = LIFE-1, and the real traces', c_ok('C-3')).
test('C-4 constants: docs = code, model bounds = code', c_ok('C-4')).
test('C-5 fixture conservation on trace configs 1-5', c_ok('C-5')).
test('C-6 traceability: catalogue, requirements, threats, assumptions', c_ok('C-6')).

% C-2 is not vacuous: every op kind's alignment uses reachable items of the code,
% and the comparison would see a swapped pair.
test('C-2 alignment covers every op kind and rejects a swapped spec', (
    forall(op_kind(K), (
        consistency:kind_code(K, Fn, Fl), code_path(Fn, Fl, Items), spec_outcomes(K, S),
        check(aligned(K), once(c2_align(S, Items, _))),
        length(S, N), check(nonempty(K), N > 0),
        (   S = [A, B | Rest], A \== B
        ->  check(swap_detected(K), \+ c2_align([B, A | Rest], Items, _))
        ;   true
        ) )) )).

% C-3: the code derivation is total and the only static spec/code difference is
% the recorded divergence (Unknown -> Unknown on a negative acknowledgment).
test('C-3 static spec/code differences are exactly div-ack-noop-version', (
    findall(Op-F-S, ( consistency:life_domain(Op, F, S), life(Op, F, S, SO, _),
                      code_life(Op, F, S, CO), SO \== CO ), Ds),
    note("differences: ~q", [Ds]),
    Ds == [ack-false-unknown],
    divergence('div-ack-noop-version', _, _, _) )).

% The TLA+ leg is live (the file exists at this pin) or explicitly a gap.
test('C-2/C-3 TLA+ leg status is recorded', (
    tla_source(Src), note("tla/SharedPool.tla: ~w", [Src]),
    (   Src == present
    ->  findall(Op, tla_guard_order(Op, _), Ops), length(Ops, NO), check(tla_ops(NO), NO >= 7),
        findall(x, tla_status_edge(_, _), Es), length(Es, NE), check(tla_edges(NE), NE > 0)
    ;   true
    ) )).

% The divergences are findings: each cites doc lines and states both sides.
test('divergences are recorded with doc citations', (
    findall(D, divergence(D, _, _, _), Ds), note("divergences: ~q", [Ds]),
    length(Ds, N), N >= 3,
    forall(divergence(_, Cite, Doc, Code), ( atom(Cite), Doc = [_ | _], Code = [_ | _] )) )).

% Extracted fixture accounts (fixtures.rs) behind CASH-SELF.
test('C-5 CASH-SELF uses the fixtures.rs account names, not the renamed trace atoms', (
    fixture_executor(X, _), fixture_actors(hiring, As),
    note("hiring actors ~q, executor ~q", [As, X]),
    As = [_ | _], \+ memberchk(X, As) )).

% C-5 known findings: each is REPRODUCED (not skipped), with the brief's shape.
test('C-5 reproduces F-2 (risk release blocked) and F-4 (validate accepts actor = executor)', (
    c_check('C-5', R), ( R = ok(Info) ; R = fail(_, Info) ),
    memberchk(findings(Fs), Info),
    note("findings: ~q", [Fs]),
    check(f2, ( member('RISK-RELEASE'-'F-2'-release_blocked(count(N), first(rel(p(0, 1, 3, _), release(0), _, _)-err(bounds))), Fs),
                N > 0 )),
    check(f4, member('CASH-SELF-ENFORCED'-'F-4'-validate_accepts(actor = executor, _), Fs)),
    check(only_risk_blocks, forall(( fixture_claim(Id, _, release_never_blocked, _), \+ known_finding(Id, _) ),
                                   \+ member(Id-_-_, Fs))),
    findall(F, finding(F, _, _, _), All), note("findings recorded: ~q", [All]),
    check(six_findings, All == ['F-1', 'F-2', 'F-3', 'F-4', 'F-5', 'F-6']) )).
