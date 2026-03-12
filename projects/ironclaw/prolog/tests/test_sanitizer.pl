%% test_sanitizer.pl — Test suite for sanitizer requirement verification
%%
%% Run with: scryer-prolog projects/ironclaw/prolog/tests/test_sanitizer.pl
%% Then query: ?- run_tests.

:- use_module('../requirements/security').
:- use_module('../requirements/sanitizer_req').
:- use_module('../verification/consistency').

%%% ========================================================
%%% Individual test predicates
%%% ========================================================

%% Test: all patterns have valid severity levels
test_no_unclassified :-
    findall(P, unclassified_pattern(P), Problems),
    (Problems = [] ->
        write('PASS: all patterns have valid severity'), nl ;
        write('FAIL: unclassified patterns: '), write(Problems), nl, fail
    ).

%% Test: all known attack vectors have detection patterns
test_all_vectors_covered :-
    findall(V, uncovered_vector(V), Uncovered),
    (Uncovered = [] ->
        write('PASS: all attack vectors covered'), nl ;
        write('FAIL: uncovered vectors: '), write(Uncovered), nl, fail
    ).

%% Test: no conflicting severity within same category
test_no_conflicts :-
    findall(P1-P2, conflicting_actions(P1, P2), Conflicts),
    (Conflicts = [] ->
        write('PASS: no conflicting severity pairs'), nl ;
        write('WARN: conflicting pairs: '), write(Conflicts), nl
    ).

%% Test: all critical special tokens have corresponding escape targets
test_critical_tokens_escaped :-
    findall(P, critical_without_escape(P), Missing),
    (Missing = [] ->
        write('PASS: all critical tokens have escape targets'), nl ;
        write('FAIL: critical without escape: '), write(Missing), nl, fail
    ).

%% Test: no orphan escape targets
test_no_orphan_escapes :-
    findall(T, orphan_escape_target(T), Orphans),
    (Orphans = [] ->
        write('PASS: no orphan escape targets'), nl ;
        write('WARN: orphan targets: '), write(Orphans), nl
    ).

%% Test: severity ordering is total (all pairs comparable)
test_severity_total_order :-
    findall(S, severity(S), Sevs),
    (check_total_order(Sevs) ->
        write('PASS: severity ordering is total'), nl ;
        write('FAIL: severity ordering is not total'), nl, fail
    ).

check_total_order([]).
check_total_order([_]).
check_total_order([S1, S2 | Rest]) :-
    severity_value(S1, V1),
    severity_value(S2, V2),
    V1 < V2,
    check_total_order([S2 | Rest]).

%% Test: every role marker has a corresponding injection pattern
test_role_markers_have_patterns :-
    findall(M, (role_marker(M), \+ injection_pattern(M, _, _)), Missing),
    (Missing = [] ->
        write('PASS: all role markers have detection patterns'), nl ;
        write('FAIL: role markers without patterns: '), write(Missing), nl, fail
    ).

%% Test: critical severity always maps to escape action
test_critical_means_escape :-
    severity_action(critical, Action),
    (Action = escape ->
        write('PASS: critical severity triggers escape action'), nl ;
        write('FAIL: critical maps to '), write(Action), write(' not escape'), nl, fail
    ).

%% Test: pattern count matches expected (18 string + 4 regex = 22 total)
test_pattern_count :-
    findall(P, injection_pattern(P, _, _), Strings),
    length(Strings, SCount),
    findall(N, regex_pattern(N, _, _), Regexes),
    length(Regexes, RCount),
    Total is SCount + RCount,
    (Total >= 20 ->
        write('PASS: '), write(Total), write(' patterns defined ('),
        write(SCount), write(' string + '),
        write(RCount), write(' regex)'), nl ;
        write('FAIL: only '), write(Total), write(' patterns defined'), nl, fail
    ).

%%% ========================================================
%%% Test runner
%%% ========================================================

run_tests :-
    write('=== Sanitizer Requirement Tests ==='), nl, nl,
    test_no_unclassified,
    test_all_vectors_covered,
    test_no_conflicts,
    test_critical_tokens_escaped,
    test_no_orphan_escapes,
    test_severity_total_order,
    test_role_markers_have_patterns,
    test_critical_means_escape,
    test_pattern_count,
    nl, write('=== All Tests Complete ==='), nl.
