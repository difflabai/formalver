%% test_approval.pl -- M4 test suite for the NEAR approval contract
%%
%% Run: tools/scripts/run-prolog.sh near-approval   (runs from prolog/tests/)
%%  or: cd projects/near-approval/prolog/tests && scryer-prolog test_approval.pl -g run_tests
%%
%% run_tests prints PASS/FAIL per test and halts: 0 if every test passed, 1 if any
%% failed, 2 on an uncaught exception. It never returns, so a caller's trailing
%% `halt` cannot mask a failure.
%%
%% Sections:
%%   1. requirement checks C-1..C-10, C-2t (pending results need a recorded decision)
%%   2. unit tests of step/4, one or more per requirement
%%   3. MC-1 and MC-1s (strategy 5.11)
%%
%% Canary: with APPROVAL_PROLOG_CANARY=1 in the environment one deliberately
%% failing test is added, so CI can show that a failure makes the run exit non-zero.

:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(iso_ext)).
:- use_module(library(os)).
:- use_module(library(between)).
:- use_module('../requirements/approval_req').
:- use_module('../requirements/threat_model').
:- use_module('../requirements/traceability').
:- use_module('../model/approval_machine').
:- use_module('../verification/consistency').
:- use_module('../verification/model_check').

:- dynamic(failures/1).
failures(0).

%%% ========================================================
%%% Runner
%%% ========================================================

run_tests :-
    catch(run_all, E, ( format("ERROR: uncaught exception ~q~n", [E]), halt(2) )),
    failures(N),
    (   N =:= 0
    ->  format("~n=== ALL TESTS PASSED ===~n", []), halt(0)
    ;   format("~n=== ~d TEST(S) FAILED ===~n", [N]), halt(1)
    ).

run_all :-
    format("=== NEAR approval: M4 Prolog requirements model ===~n~n", []),
    format("--- Requirement checks (C) ---~n", []),
    c_ids(Ids),
    forall(member(Id, Ids), run_c(Id)),
    format("~n--- step/4 unit tests ---~n", []),
    forall(unit_test(Name, _), run_unit(Name)),
    canary,
    format("~n--- Model checks (MC) ---~n", []),
    run_mc('MC-1'),
    run_mc('MC-1s').

fail_one :-
    retract(failures(N)), N1 is N + 1, assertz(failures(N1)).

run_c(Id) :-
    (   catch(c_check(Id, R), E, R = fail(exception(E))) -> true ; R = fail(no_result) ),
    (   R = pass(Note) -> format("PASS: ~a ~w~n", [Id, Note])
    ;   R = pending(D, Note), decision(D, _)
    ->  format("PASS (pending, decision ~a): ~a ", [D, Id]), print_note(Note), nl
    ;   R = pending(D, Note)
    ->  format("FAIL: ~a pending without a recorded decision ~w: ", [Id, D]), print_note(Note), nl, fail_one
    ;   format("FAIL: ~a ~w~n", [Id, R]), fail_one
    ).

print_note(Note) :-
    (   Note = [C | _], atom(C), atom_length(C, 1) -> format("~s", [Note]) ; format("~w", [Note]) ).

run_unit(Name) :-
    unit_test(Name, Goal),
    (   catch(Goal, E, ( format("  exception: ~q~n", [E]), fail ))
    ->  format("PASS: ~a~n", [Name])
    ;   format("FAIL: ~a~n", [Name]), fail_one
    ).

canary :-
    (   catch(getenv("APPROVAL_PROLOG_CANARY", V), _, fail), V == "1"
    ->  format("FAIL: canary (planted failure, APPROVAL_PROLOG_CANARY=1)~n", []), fail_one
    ;   true
    ).

run_mc(Name) :-
    mc_profile(Name, Params, Depth),
    mc_run(Name, Params, Depth, R),
    format_mc(R),
    mc_check(R, Failures, Notes),
    R = mc(_, _, NStates, _, _, _, _, Ms),
    state_floor(Name, Floor),
    (   Failures == [], NStates >= Floor
    ->  format("PASS: ~a (~d states, ~d ms, floor ~d) ~w~n", [Name, NStates, Ms, Floor, Notes])
    ;   format("FAIL: ~a ~w (states ~d, floor ~d)~n", [Name, Failures, NStates, Floor]), fail_one
    ).

%% mc1_state_floor from status.toml applies to MC-1 (strategy 5.11); 0 until recorded.
state_floor('MC-1', F) :- !, ( catch(toml_int("mc1_state_floor", F), _, fail) -> true ; F = 0 ).
state_floor(_, 0).

toml_int(Key, V) :-
    prolog_root(Root),
    append(Root, "/../status.toml", Path),
    setup_call_cleanup(open(Path, read, In), find_key_line(In, Key, Line), close(In)),
    append(Key, Rest0, Line),
    drop_non_digits(Rest0, Rest),
    take_digits(Rest, Ds), Ds \== [],
    number_chars(V, Ds).

find_key_line(In, Key, Line) :-
    read_line_chars(In, L),
    L \== end_of_file,
    (   append(Key, [' ' | _], L) -> Line = L ; find_key_line(In, Key, Line) ).

read_line_chars(In, L) :-
    get_char(In, C),
    (   C == end_of_file -> L = end_of_file
    ;   C == '\n' -> L = []
    ;   read_line_rest(In, Cs), L = [C | Cs]
    ).
read_line_rest(In, Cs) :-
    get_char(In, C),
    (   ( C == end_of_file ; C == '\n' ) -> Cs = []
    ;   Cs = [C | Cs1], read_line_rest(In, Cs1)
    ).

drop_non_digits([C | Cs], R) :- \+ digit(C), !, drop_non_digits(Cs, R).
drop_non_digits(R, R).
take_digits([C | Cs], [C | Ds]) :- digit(C), !, take_digits(Cs, Ds).
take_digits(_, []).
digit(C) :- member(C, ['0','1','2','3','4','5','6','7','8','9']).

%%% ========================================================
%%% Fixtures
%%% ========================================================

s0(S) :- real_params(P), init_state(P, o, S).

%% run(+S0, +Steps, -S): Steps = [Op-Expected], Expected unifies with the Result.
run(S, [], S).
run(S0, [Op-Exp | T], S) :-
    step(S0, Op, R, S1),
    (   R = Exp -> true
    ;   format("  step ~w: expected ~w, got ~w~n", [Op, Exp, R]), fail
    ),
    run(S1, T, S).

%% Standard setup: agent key k1 of account a, approver key k2 of account b.
base(S) :-
    s0(S0),
    run(S0, [ add(o, k1, a, agent) - ok(_),
              add(o, k2, b, approver) - ok(_) ], S).

with_request(S) :-
    base(S0),
    run(S0, [ request(c(a, a, k1), ok(x)) - ok(0) ], S).

err_stutters(S, Op, E) :- step(S, Op, err(E0), S1), E0 == E, S1 == S.

%%% ========================================================
%%% Unit tests
%%% ========================================================

% R1 / TX-4: an agent requests with its own key.
unit_test('R1 agent requests with its key (TX-4)', (
    with_request(S),
    request_at(S, 0, req(0, a, k1, 0, ok(x), none, none)),
    principal(S, k1, p(a, agent, 0, 0, 1)),
    status(S, 0, pending))).
unit_test('R2 request emits approval_requested', emits(request_action, approval_requested)).
% R3 / TX-5: an approver of another account approves with its own key.
unit_test('R3 approver approves with its key (TX-5)', (
    with_request(S0),
    run(S0, [ approve(c(b, b, k2), 0, ok(x)) - ok(proof(0, 0, ok(x), a, k1, 0, b, k2, 1)) ], S),
    status(S, 0, approved),
    principal(S, k1, p(a, agent, 0, 0, 0)),
    approval_count(S, 1))).
unit_test('R4 approve emits action_approved', emits(approve, action_approved)).
% R5 / RD-1: per-request proof is public and equals the recorded proof.
unit_test('R5 get_approval returns the recorded proof (RD-1)', (
    with_request(S0),
    view(S0, get_approval(0), none),
    step(S0, approve(c(b, b, k2), 0, ok(x)), ok(P), S),
    view(S, get_approval(0), some(proof_view(P, none, none))),
    view(S, get_approval(1), none),
    approval(S, 0, some(P)))).
% R6 / RD-2 / RD-4: paged log, clamp, defaults, client loop.
unit_test('R6 paged log: client loop yields the log once, in order (RD-4)', (
    three_approvals(S),
    S = st(_, _, _, _, L, _, _),
    findall(P, ( member(I, L), approval(S, I, some(P)) ), All),
    forall(member(Lim, [1, 2, 3, 99, 100, 101, 200]),
           ( client_enumerate(S, Lim, Got, _), Got == All )))).
unit_test('R6 page bounds: |page| = e - f, clamp to PG, defaults (RD-2, SH-7)', (
    three_approvals(S3),
    S3 = st(_, O, P, R, L, G, V),
    Small = params(2048, 16, 18446744073709551615, 2, 1),
    S = st(Small, O, P, R, L, G, V),
    approvals(S, 0, 100, E1, Pg1), E1 =:= 2, length(Pg1, 2),     % clamped to PG = 2
    approvals(S, 1, 5, E2, Pg2), E2 =:= 3, length(Pg2, 2),
    approvals(S, 3, 5, _, []),
    approvals(S, 7, 5, _, []),
    approvals(S, 0, 0, _, []),
    view(S, get_approvals(none, none), D), length(D, 1),         % default DPG = 1
    approvals(S3, 18446744073709551615, 100, _, []))).            % saturating, no overflow
% D1 / TX-3: key+account identity.
unit_test('D1 unknown key, wrong role, key bound to another account (TX-3)', (
    with_request(S),
    err_stutters(S, request(c(a, a, k3), ok(x)), 'UnknownKey'),
    err_stutters(S, request(c(b, b, k2), ok(x)), 'WrongRole'),
    err_stutters(S, request(c(b, b, k1), ok(x)), 'KeyAccountMismatch'),
    err_stutters(S, approve(c(a, a, k1), 0, ok(x)), 'WrongRole'),
    err_stutters(S, approve(c(a, a, k2), 0, ok(x)), 'KeyAccountMismatch'))).
% D2: predecessor must equal signer.
unit_test('D2 relayed calls fail IndirectCall', (
    with_request(S),
    err_stutters(S, request(c(r, a, k1), ok(x)), 'IndirectCall'),
    err_stutters(S, approve(c(r, b, k2), 0, ok(x)), 'IndirectCall'),
    err_stutters(S, reject(c(r, b, k2), 0), 'IndirectCall'))).
% D3 / TX-1, TX-2, TX-6: owner manages keys; owner never changes.
unit_test('D3 only the owner adds and revokes keys (TX-1, TX-2, TX-6)', (
    base(S),
    err_stutters(S, add(a, k3, a, agent), 'NotOwner'),
    err_stutters(S, revoke(b, k1), 'NotOwner'),
    err_stutters(S, revoke(o, k3), 'KeyNotRegistered'),
    step(S, add(o, k3, a, approver), ok(principal(a, approver, 2, 0, 0)), S1),
    view(S1, get_owner, o),
    step(S1, revoke(o, k3), ok(principal(a, approver, 2, 0, 0)), S2),
    view(S2, get_principal(k3), none),
    view(S2, get_owner, o))).
% D4: one registration, one role per key.
unit_test('D4 a registered key cannot be added again (KeyAlreadyRegistered)', (
    base(S),
    err_stutters(S, add(o, k1, a, approver), 'KeyAlreadyRegistered'),
    err_stutters(S, add(o, k2, a, approver), 'KeyAlreadyRegistered'))).
% D5: separation of duties, for approve and reject.
unit_test('D5 approver of the agent account cannot decide (SelfApproval)', (
    with_request(S0),
    run(S0, [ add(o, k3, a, approver) - ok(_) ], S),
    err_stutters(S, approve(c(a, a, k3), 0, ok(x)), 'SelfApproval'),
    err_stutters(S, reject(c(a, a, k3), 0), 'SelfApproval'))).
% D6: decided at most once.
unit_test('D6 a request is decided at most once', (
    with_request(S0),
    run(S0, [ approve(c(b, b, k2), 0, ok(x)) - ok(_) ], S1),
    err_stutters(S1, approve(c(b, b, k2), 0, ok(x)), 'AlreadyApproved'),
    err_stutters(S1, reject(c(b, b, k2), 0), 'AlreadyApproved'),
    run(S0, [ reject(c(b, b, k2), 0) - ok(_) ], S2),
    err_stutters(S2, approve(c(b, b, k2), 0, ok(x)), 'AlreadyRejected'),
    err_stutters(S2, reject(c(b, b, k2), 0), 'AlreadyRejected'))).
% D7 / TR-3 / HIST-8: durable revocation, no revival after re-registration.
unit_test('D7 revoked agent: pending request void forever, even after re-add (TR-3)', (
    with_request(S0),
    run(S0, [ revoke(o, k1) - ok(principal(a, agent, 0, 0, 1)) ], S1),
    status(S1, 0, void),
    view(S1, get_revocation(0), some(revoked)),
    view(S1, get_revocation(1), none),
    view(S1, get_revocation(7), none),
    run(S1, [ add(o, k1, a, agent) - ok(principal(a, agent, 2, 1, 0)) ], S2),
    status(S2, 0, void),
    err_stutters(S2, approve(c(b, b, k2), 0, ok(x)), 'AgentRevoked'),
    err_stutters(S2, reject(c(b, b, k2), 0), 'AgentRevoked'),
    run(S2, [ request(c(a, a, k1), ok(x)) - ok(1),
              approve(c(b, b, k2), 1, ok(x)) - ok(_) ], S3),
    status(S3, 0, void), status(S3, 1, approved))).
unit_test('D7 proofs report later revocations of either key (RD-8)', (
    with_request(S0),
    run(S0, [ approve(c(b, b, k2), 0, ok(x)) - ok(P),
              revoke(o, k2) - ok(_) ], S1),
    view(S1, get_approval(0), some(proof_view(P, none, revoked))),
    approval(S1, 0, some(P)),                                    % HIST-5: core proof unchanged
    run(S1, [ revoke(o, k1) - ok(_) ], S2),
    view(S2, get_approval(0), some(proof_view(P, revoked, revoked))),
    status(S2, 0, approved))).
% D8: append-only, dense ids.
unit_test('D8 dense request ids and append-only log (INV-1, HIST-3)', (
    three_approvals(S),
    S = st(_, _, _, R, L, _, _),
    findall(I, member(req(I, _, _, _, _, _, _), R), Ids), Ids == [0, 1, 2],
    L == [1, 0, 2],
    view(S, get_request_count, 3), view(S, get_approval_count, 3))).
% D9: action length and pending cap.
unit_test('D9 action length 1..2048 bytes (ROB-3 boundaries)', (
    real_params(P),
    action_of_length(0, P, empty), action_of_length(1, P, ok(_)),
    action_of_length(2048, P, ok(_)), action_of_length(2049, P, too_long),
    action_of_length(2050, P, too_long),
    base(S),
    err_stutters(S, request(c(a, a, k1), empty), 'EmptyAction'),
    err_stutters(S, request(c(a, a, k1), too_long), 'ActionTooLong'),
    action_of_length(2048, P, A2048),
    step(S, request(c(a, a, k1), A2048), ok(0), _))).
unit_test('D9 at most 16 pending per agent key; deciding frees a slot', (
    base(S0),
    findall(request(c(a, a, k1), ok(x)) - ok(_), between(1, 16, _), Ops),
    run(S0, Ops, S16),
    principal(S16, k1, p(_, _, _, _, 16)),
    err_stutters(S16, request(c(a, a, k1), ok(x)), 'TooManyPending'),
    run(S16, [ approve(c(b, b, k2), 3, ok(x)) - ok(_),
               request(c(a, a, k1), ok(x)) - ok(16) ], S17),
    err_stutters(S17, request(c(a, a, k1), ok(x)), 'TooManyPending'),
    run(S17, [ reject(c(b, b, k2), 4) - ok(_),
               request(c(a, a, k1), ok(x)) - ok(17) ], _))).
unit_test('D9 revoking the key clears its backlog (README rotation)', (
    with_request(S0),
    run(S0, [ revoke(o, k1) - ok(_), add(o, k1, a, agent) - ok(_) ], S1),
    principal(S1, k1, p(a, agent, 2, 1, 0)),
    pend_count(S1, k1, 0))).
% D10: approval commits to content.
unit_test('D10 approve fails unless the action matches (ActionMismatch)', (
    with_request(S),
    err_stutters(S, approve(c(b, b, k2), 0, ok(y)), 'ActionMismatch'),
    err_stutters(S, approve(c(b, b, k2), 0, empty), 'ActionMismatch'))).
% D11: no upgrade, ownership transfer, expiry or threshold.
unit_test('D11 no upgrade, ownership-transfer, expiry or threshold method', (
    c_check('C-1', pass(_)),
    \+ method(set_owner, _, _), \+ method(upgrade, _, _))).
% D12 / TX-0: rejected calls write nothing (stutter), guards before writes.
unit_test('D12 every rejected call leaves the state unchanged (TX-0)', (
    with_request(S),
    forall(( member(Op, [ add(a, k3, a, agent), add(o, k1, b, agent), revoke(a, k1), revoke(o, k9),
                          request(c(a, a, k9), ok(x)), request(c(a, a, k1), empty),
                          approve(c(b, b, k2), 5, ok(x)), approve(c(b, b, k2), 0, ok(z)),
                          reject(c(a, a, k1), 0), reject(c(b, b, k2), 9) ]) ),
           ( step(S, Op, err(_), S1), S1 == S )))).
% D12: guard precedence (first failing guard in guard/4 order).
unit_test('D12 guard precedence: first failing guard wins', (
    with_request(S0),
    run(S0, [ revoke(o, k1) - ok(_), add(o, k3, a, approver) - ok(_) ], S),
    % unknown key beats empty action
    err_stutters(S0, request(c(a, a, k9), empty), 'UnknownKey'),
    % role before account
    err_stutters(S0, approve(c(a, a, k1), 9, empty), 'WrongRole'),
    % request not found before anything about the request
    err_stutters(S0, approve(c(b, b, k2), 1, empty), 'RequestNotFound'),
    % AgentRevoked before ActionMismatch and SelfApproval
    err_stutters(S, approve(c(a, a, k3), 0, empty), 'AgentRevoked'),
    % ActionMismatch before SelfApproval
    run(S0, [ add(o, k3, a, approver) - ok(_) ], S2),
    err_stutters(S2, approve(c(a, a, k3), 0, empty), 'ActionMismatch'),
    % EmptyAction before TooManyPending
    real_params(_),
    guard_sequence(request_action, RS), nth0(I1, RS, 'EmptyAction'), nth0(I2, RS, 'TooManyPending'), I1 < I2)).
% LogFull (scaled MAXU = 2): add and request; approve's is unreachable (LEM-3).
unit_test('LogFull at MAXU for add and request (ROB-2, scaled)', (
    scaled_params(16, 2, P), init_state(P, o, S0),
    run(S0, [ add(o, k1, a, agent) - ok(_), add(o, k2, b, approver) - ok(_) ], S1),
    err_stutters(S1, add(o, k3, a, agent), 'LogFull'),
    run(S1, [ request(c(a, a, k1), ok(x)) - ok(0), request(c(a, a, k1), ok(x)) - ok(1) ], S2),
    err_stutters(S2, request(c(a, a, k1), ok(x)), 'LogFull'),
    run(S2, [ approve(c(b, b, k2), 0, ok(x)) - ok(_), approve(c(b, b, k2), 1, ok(x)) - ok(_) ], _))).
% D13: times are abstracted in this model.
unit_test('D13 timestamps: out of model scope (times abstracted, strategy 17.1)', (
    requirement('D13', _), verified_by('D13', 'INV-10'), verified_by('D13', 'TR-4'))).
% D17: rejection.
unit_test('D17 approver of another account rejects; terminal; frees slot', (
    with_request(S0),
    run(S0, [ reject(c(b, b, k2), 0) - ok(rejection(req(0, a, k1, 0, ok(x), none, rj(b, k2, 1)))) ], S),
    status(S, 0, rejected),
    principal(S, k1, p(a, agent, 0, 0, 0)),
    approval_count(S, 0),
    view(S, get_rejection(0), some(rejection(0, ok(x), a, k1, 0, b, k2, 1))),
    view(S, get_approval(0), none),
    view(S, request_status(0), some(rejected)),
    err_stutters(S, approve(c(b, b, k2), 0, ok(x)), 'AlreadyRejected'),
    err_stutters(S0, reject(c(a, a, k1), 0), 'WrongRole'),
    emits(reject, action_rejected),
    method(reject, change, approver))).
unit_test('D17 a void request cannot be rejected', (
    with_request(S0),
    run(S0, [ revoke(o, k1) - ok(_) ], S),
    err_stutters(S, reject(c(b, b, k2), 0), 'AgentRevoked'))).
% Views.
unit_test('Views: request_status, get_request, get_principal, counts (RD-7, SH-7)', (
    with_request(S),
    view(S, request_status(0), some(pending)),
    view(S, request_status(1), none),
    view(S, get_request(0), some(request_view(req(0, a, k1, 0, ok(x), none, none), pending))),
    view(S, get_request(1), none),
    view(S, get_principal(k1), some(principal(a, agent, 1))),
    view(S, get_principal(k3), none),
    step(S, view(get_request_count), ok(1), S1), S1 == S)).
%% three_approvals(S): requests 0, 1, 2 approved in order 1, 0, 2.
three_approvals(S) :-
    base(S0),
    run(S0, [ request(c(a, a, k1), ok(x)) - ok(0),
              request(c(a, a, k1), ok(y)) - ok(1),
              request(c(a, a, k1), ok(z)) - ok(2),
              approve(c(b, b, k2), 1, ok(y)) - ok(_),
              approve(c(b, b, k2), 0, ok(x)) - ok(_),
              approve(c(b, b, k2), 2, ok(z)) - ok(_) ], S).
