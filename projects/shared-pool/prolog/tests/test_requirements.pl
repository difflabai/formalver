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
:- use_module('../requirements/traceability').
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
test('C-6 traceability: catalogue = strategy.md section 5, requirements, threats, assumptions', c_ok('C-6')).

% C-6 is not vacuous: strategy.md section 5 is read, and every catalogue ID and
% every layer list is compared with it.
test('C-6 compares every catalogue ID and layer list with strategy.md section 5', (
    c_check('C-6', R), ( R = ok(Info) ; R = fail(_, Info) ),
    memberchk(properties(NP), Info), memberchk(strategy_rows(NS), Info),
    memberchk(layers_equal(NL), Info),
    note("properties ~d, strategy.md section 5 rows ~d, equal layer lists ~d", [NP, NS, NL]),
    check(nonempty, NP > 0), check(rows(NS), NS =:= NP), check(layers(NL), NL =:= NP) )).

% ... and the comparison reports each kind of disagreement: a property/3 row
% missing from the catalogue (what mutant r01 does), a section 5 row missing,
% a repeated row, a layer list that differs (mutant r02) and an empty section.
test('C-6 reports a dropped, an added, a repeated and a relabelled ID, and an empty section', (
    strategy_path(SP), strategy_catalogue(SP, Rows, SPs),
    check(read_clean(SPs), SPs == []),
    findall(Id-Ls, property(Id, Ls, _), Cat),
    check(agree, catalogue_problems(Rows, Cat, [])),
    Cat = [C1-CL1 | CatRest],
    catalogue_problems(Rows, CatRest, P1), note("property ~w dropped: ~q", [C1, P1]),
    check(dropped_property, P1 = [strategy_id_not_in_catalogue(C1, line(_))]),
    Rows = [row(N1, R1, RL1) | RowsRest],
    catalogue_problems(RowsRest, Cat, P2), note("row ~w dropped: ~q", [R1, P2]),
    check(dropped_row, P2 == [catalogue_id_not_in_strategy(R1)]),
    append(Rows, [row(9999, R1, RL1)], Rows3),
    catalogue_problems(Rows3, Cat, P3), note("row ~w repeated: ~q", [R1, P3]),
    check(repeated_row, P3 == [strategy_duplicate_id(R1, lines([N1, 9999]))]),
    catalogue_problems(Rows, [C1-[prolog | CL1] | CatRest], P4), note("layers of ~w changed: ~q", [C1, P4]),
    check(relabelled, P4 = [layers_differ(C1, line(_), strategy(_), catalogue([prolog | CL1]))]),
    catalogue_problems([], Cat, P5),
    check(empty, memberchk(strategy_no_ids, P5)) )).

% The section 5 reader on small documents: only section 5's tables count,
% header and separator rows are skipped, an escaped bar stays in its cell, and
% a missing section, a non-ID first cell, a short row, a table with another
% header and a table without a separator are each reported with their line.
test('C-6 strategy.md reader: section 5 only, headers skipped, malformed rows reported', (
    Doc = "# T\n## 4. Before\n| ID | S | Layer(s) |\n|---|---|---|\n| X-1 | s | tla |\n## 5. Catalogue\n\nText.\n\n### 5.1 Sub\n\n| ID | Statement | Layer(s) | Evidence |\n|---|---|---|---|\n| A-1 | a \\| b | kani, lean | e |\n| B-2 | b | near-tests, prolog | e |\n\n| ID | S | Layer(s) |\n|:--|---|---|\n| C-3 | c | assumption |\n## 6. After\n| ID | S | Layer(s) |\n|---|---|---|\n| Z-9 | z | tla |\n",
    catalogue_rows(Doc, Rows, Ps), note("rows ~q, problems ~q", [Rows, Ps]),
    check(rows, Rows == [row(14, 'A-1', [kani, lean]), row(15, 'B-2', ['near-tests', prolog]),
                         row(19, 'C-3', [assumption])]),
    check(no_problems, Ps == []),
    catalogue_rows("# T\n## 6. X\n| ID | S | Layer(s) |\n|---|---|---|\n| A-1 | s | tla |\n", R2, P2),
    check(no_section, ( R2 == [], P2 == [strategy_section_5_missing] )),
    Bad = "## 5. C\n| ID | S | Layer(s) |\n|---|---|---|\n| `A-1` | s | tla |\n| B-2 | s |\n\n| Name | Layer(s) |\n|---|---|\n| C-3 | tla |\n\n| D-4 | s | tla |\n",
    catalogue_rows(Bad, R3, P3), note("malformed: rows ~q, problems ~q", [R3, P3]),
    check(malformed_rows, R3 == [row(5, 'B-2', none)]),
    check(malformed_problems, P3 == [strategy_row_not_a_bare_id(line(4), '`A-1`'),
                                     strategy_row_without_layers(line(5), 'B-2', cells(2)),
                                     strategy_table_header(line(7), ['Name', 'Layer(s)']),
                                     strategy_table_without_separator(line(11))]) )).

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
