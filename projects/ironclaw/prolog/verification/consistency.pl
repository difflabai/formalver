%% consistency.pl — Consistency and completeness verification queries
%%
%% Run these queries to verify that the sanitizer requirements are
%% internally consistent and cover all known attack vectors.

:- module(consistency, [
    unclassified_pattern/1,
    uncovered_vector/1,
    conflicting_actions/2,
    redundant_patterns/2,
    critical_without_escape/1,
    orphan_escape_target/1,
    verify_all/0
]).

:- use_module('../requirements/security').
:- use_module('../requirements/sanitizer_req').

%%% ========================================================
%%% Consistency checks
%%% ========================================================

%% A pattern whose severity is not a valid severity level
unclassified_pattern(Pattern) :-
    injection_pattern(Pattern, Sev, _),
    \+ severity(Sev).

unclassified_pattern(Name) :-
    regex_pattern(Name, Sev, _),
    \+ severity(Sev).

%% Two patterns in the same category with contradictory severity
%% (one critical, one low/medium — may indicate inconsistency)
conflicting_actions(P1, P2) :-
    injection_pattern(P1, critical, Cat),
    injection_pattern(P2, S2, Cat),
    P1 \= P2,
    \+ severity_gte(S2, high).

%%% ========================================================
%%% Completeness checks
%%% ========================================================

%% An attack vector with no corresponding detection pattern
uncovered_vector(Vector) :-
    attack_vector(Vector),
    \+ injection_pattern(_, _, Vector),
    \+ regex_pattern(_, _, Vector).

%% A critical pattern that is not in the escape target list
%% (critical patterns should trigger escaping, but are the right
%% things being escaped?)
critical_without_escape(Pattern) :-
    injection_pattern(Pattern, critical, special_token_injection),
    \+ escape_target(Pattern).

%%% ========================================================
%%% Redundancy checks
%%% ========================================================

%% Two string patterns where one is a substring of the other
%% in the same category (the shorter one makes the longer redundant
%% in Aho-Corasick matching)
redundant_patterns(Shorter, Longer) :-
    injection_pattern(Shorter, _, Cat),
    injection_pattern(Longer, _, Cat),
    Shorter \= Longer,
    atom_length(Shorter, SLen),
    atom_length(Longer, LLen),
    SLen < LLen,
    sub_atom(Longer, _, _, _, Shorter).

%% An escape target that doesn't correspond to any critical pattern
orphan_escape_target(Target) :-
    escape_target(Target),
    Target \= "\x00",  % null byte is special (regex pattern, not string)
    \+ injection_pattern(Target, critical, _).

%%% ========================================================
%%% Run all checks
%%% ========================================================

verify_all :-
    write('=== Sanitizer Requirements Verification ==='), nl, nl,

    %% Check 1: All patterns have valid severities
    write('1. Unclassified patterns: '),
    findall(P, unclassified_pattern(P), Unclassified),
    (Unclassified = [] ->
        write('PASS (none)') ;
        write('FAIL'), nl, write('   '), write(Unclassified)
    ), nl,

    %% Check 2: All attack vectors covered
    write('2. Uncovered attack vectors: '),
    findall(V, uncovered_vector(V), Uncovered),
    (Uncovered = [] ->
        write('PASS (none)') ;
        write('FAIL'), nl, write('   '), write(Uncovered)
    ), nl,

    %% Check 3: No conflicting severity within categories
    write('3. Conflicting severity pairs: '),
    findall(P1-P2, conflicting_actions(P1, P2), Conflicts),
    (Conflicts = [] ->
        write('PASS (none)') ;
        write('WARN'), nl, write('   '), write(Conflicts)
    ), nl,

    %% Check 4: Critical special tokens have escape targets
    write('4. Critical patterns without escape: '),
    findall(P, critical_without_escape(P), NoEscape),
    (NoEscape = [] ->
        write('PASS (none)') ;
        write('FAIL'), nl, write('   '), write(NoEscape)
    ), nl,

    %% Check 5: Redundant patterns
    write('5. Redundant pattern pairs: '),
    findall(S-L, redundant_patterns(S, L), Redundant),
    (Redundant = [] ->
        write('PASS (none)') ;
        write('INFO'), nl, write('   '), write(Redundant)
    ), nl,

    %% Check 6: Orphan escape targets
    write('6. Orphan escape targets: '),
    findall(T, orphan_escape_target(T), Orphans),
    (Orphans = [] ->
        write('PASS (none)') ;
        write('WARN'), nl, write('   '), write(Orphans)
    ), nl,

    nl, write('=== Verification Complete ==='), nl.
