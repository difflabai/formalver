%% test_verifier_rules.pl -- M7 tests of verification/verifier_rules.pl (VER-1..8)
%%
%% Run: tools/scripts/run-prolog.sh near-approval   (runs every tests/*.pl)
%%  or: tools/scripts/run-prolog.sh near-approval test_verifier_rules.pl
%%
%% Each rule has accepting and rejecting cases; a rule that accepted
%% everything (or nothing) fails here. The same rules are fed sandbox
%% observations by sandbox/tests/runtime.rs (RT-SPOOF) and deploy.rs (VER-8).
%% run_tests halts 0 if all pass, 1 if any fail, 2 on an exception.

:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(between)).
:- use_module(library(iso_ext)).
:- use_module('../verification/verifier_rules').

:- dynamic(failures/1).
:- discontiguous(t/2).
failures(0).

run_tests :-
    catch(run_all, E, ( format("ERROR: uncaught exception ~q~n", [E]), halt(2) )),
    failures(N),
    (   N =:= 0
    ->  format("~n=== ALL TESTS PASSED ===~n", []), halt(0)
    ;   format("~n=== ~d TEST(S) FAILED ===~n", [N]), halt(1)
    ).

run_all :-
    format("=== NEAR approval: M7 verifier rules (VER-1..8) ===~n~n", []),
    forall(t(Name, _), run_one(Name)).

run_one(Name) :-
    once(t(Name, Goal)),
    (   catch(once(Goal), E, ( format("  exception ~q~n", [E]), fail ))
    ->  format("PASS ~a~n", [Name])
    ;   format("FAIL ~a~n", [Name]),
        retract(failures(N)), N1 is N + 1, assertz(failures(N1))
    ).

%% Fixtures
c('approvals.near').
proof(proof('approvals.near', 3, 'pay 10', 'agent.near', 'ed25519:A',
            'approver.near', 'ed25519:P', 1700000000000000000)).
agent_key(key('agent.near', 'ed25519:A',
              function_call('approvals.near', [request_action], 250000000000000000000000))).
approver_key(key('approver.near', 'ed25519:P',
                 function_call('approvals.near', [approve, reject], 250000000000000000000000))).
good_log(log(receipt('approvals.near', success, final),
             event(trust_approval, '1.0.0', action_approved, 3))).

%%% VER-1
t('VER-1 view get_approval at final accepted',
  ( c(C), ver1_accept(C, view(C, get_approval, final)) )).
t('VER-1 view at optimistic finality rejected',
  ( c(C), \+ ver1_accept(C, view(C, get_approval, optimistic)) )).
t('VER-1 view of another contract rejected',
  ( c(C), \+ ver1_accept(C, view('other.near', get_approval, final)) )).
t('VER-1 view of another method rejected',
  ( c(C), \+ ver1_accept(C, view(C, get_request, final)) )).
t('VER-1 log of a successful final receipt on C accepted',
  ( c(C), good_log(L), ver1_accept(C, L) )).
t('VER-1 spoofed log (executor not C) rejected',
  ( c(C), \+ ver1_accept(C, log(receipt('spoofer.near', success, final),
                                    event(trust_approval, '1.0.0', action_approved, 3))) )).
t('VER-1 log of a failed receipt on C rejected (RT-REVERT, RT-BATCH)',
  ( c(C), \+ ver1_accept(C, log(receipt(C, failure, final),
                                    event(trust_approval, '1.0.0', action_approved, 3))) )).
t('VER-1 log in a non-final block rejected',
  ( c(C), \+ ver1_accept(C, log(receipt(C, success, optimistic),
                                    event(trust_approval, '1.0.0', action_approved, 3))) )).
t('VER-1 other event or standard rejected',
  ( c(C),
    \+ ver1_accept(C, log(receipt(C, success, final), event(trust_approval, '1.0.0', approval_requested, 3))),
    \+ ver1_accept(C, log(receipt(C, success, final), event(nep171, '1.0.0', action_approved, 3))),
    \+ ver1_accept(C, log(receipt(C, success, final), event(trust_approval, '2.0.0', action_approved, 3))) )).
t('VER-1 unbound source does not unify into acceptance',
  ( c(C), \+ ver1_accept(C, log(receipt(_, _, _), event(_, _, _, _))) )).

%%% VER-2
t('VER-2 same hash at proof block and now', ver2_ok(h1, h1, h1)).
t('VER-2 changed since the proof', \+ ver2_ok(h1, h1, h2)).
t('VER-2 different at the proof block', \+ ver2_ok(h1, h2, h1)).
t('VER-2 no code (missing) rejected', \+ ver2_ok(h1, missing, h1)).

%%% VER-3
t('VER-3 locked: no full-access key since b0', ver3_ok(locked, [], [function_call])).
t('VER-3 locked: a full-access key since b0 fails', \+ ver3_ok(locked, ['ed25519:X'], [])).
t('VER-3 locked: a DeleteAccount receipt fails (RT-RESET)', \+ ver3_ok(locked, [], [function_call, delete_account])).
t('VER-3 governance: keys allowed, no forbidden receipts', ver3_ok(governance, ['ed25519:G'], [function_call, transfer])).
t('VER-3 governance: each forbidden action fails',
  forall(member(A, [deploy_contract, use_global_contract, add_key, delete_account]),
         \+ ver3_ok(governance, ['ed25519:G'], [function_call, A]))).

%%% VER-4
t('VER-4 expected action and agent, approver allowlisted',
  ( proof(P), ver4_ok(P, expect('pay 10', 'agent.near'), ['approver.near']) )).
t('VER-4 trusting the owner registry (any)',
  ( proof(P), ver4_ok(P, expect('pay 10', 'agent.near'), any) )).
t('VER-4 other action rejected',
  ( proof(P), \+ ver4_ok(P, expect('pay 11', 'agent.near'), any) )).
t('VER-4 other agent rejected',
  ( proof(P), \+ ver4_ok(P, expect('pay 10', 'mallory.near'), any) )).
t('VER-4 approver not on the allowlist rejected',
  ( proof(P), \+ ver4_ok(P, expect('pay 10', 'agent.near'), ['other.near']) )).

%%% VER-5
t('VER-5 RD-4 loop yields the log exactly once, in order, for every limit',
  forall(( member(Len, [0, 1, 99, 100, 101, 250]),
           member(Limit, [none, 0, 1, 2, 99, 100, 101, 200]), Limit \== 0 ),
         ( numlist_(Len, Log), ver5_enumerate(Log, Limit, Items), Items == Log ))).
t('VER-5 limit 0 never advances (stops on the empty page; README R-3)',
  ( numlist_(5, Log), rd4_client(Log, 0, Reads, Items), Items == [], Reads = [page(_, 0, 0, [])] )).
t('VER-5 a client that stops on a short page misses proofs (limit > 100 is clamped)',
  ( numlist_(150, Log), ver5_enumerate(Log, 200, All), All == Log,
    rd4_client(Log, 200, [page(_, 0, 200, First) | _], _),
    length(First, 100), First \== Log )).
t('VER-5 pages read at different blocks rejected',
  \+ ver5_ok([page(b1, 0, 2, [0, 1]), page(b2, 2, 2, [])], _)).
t('VER-5 a gap in from_index rejected',
  \+ ver5_ok([page(b, 0, 2, [0, 1]), page(b, 3, 2, [])], _)).
t('VER-5 no final empty page rejected',
  \+ ver5_ok([page(b, 0, 2, [0, 1])], _)).

%%% VER-6
t('VER-6 request counter decrease invalidates (RT-RESET)', ver6_invalidates(state(5, 2, h), state(0, 0, h))).
t('VER-6 approval counter decrease invalidates', ver6_invalidates(state(5, 2, h), state(6, 1, h))).
t('VER-6 code hash change invalidates', ver6_invalidates(state(5, 2, h), state(5, 2, h2))).
t('VER-6 growth keeps the cache', \+ ver6_invalidates(state(5, 2, h), state(9, 3, h))).
t('VER-6 is only a heuristic: a reset that caught up is missed',
  \+ ver6_invalidates(state(2, 1, h), state(2, 1, h))).

%%% VER-7
t('VER-7 first execution within max age', ver7_execute([], c, 3, 100, 150, 60)).
t('VER-7 duplicate (C, id) refused', \+ ver7_execute([c-3], c, 3, 100, 150, 60)).
t('VER-7 same id on another contract is a different approval', ver7_execute([d-3], c, 3, 100, 150, 60)).
t('VER-7 too old refused', \+ ver7_execute([], c, 3, 100, 161, 60)).
t('VER-7 approval from the future refused', \+ ver7_execute([], c, 3, 200, 150, 60)).

%%% VER-8
t('VER-8 function-call keys scoped to C accepted',
  ( c(C), proof(P), agent_key(A), approver_key(K), ver8_ok(C, P, A, K) )).
t('VER-8 approver key [approve] only accepted',
  ( c(C), proof(P), agent_key(A),
    ver8_ok(C, P, A, key('approver.near', 'ed25519:P', function_call(C, [approve], 1))) )).
t('VER-8 full-access agent key rejected (F-9)',
  ( c(C), proof(P), approver_key(K), \+ ver8_ok(C, P, key('agent.near', 'ed25519:A', full_access), K) )).
t('VER-8 missing key rejected',
  ( c(C), proof(P), approver_key(K), \+ ver8_ok(C, P, key('agent.near', 'ed25519:A', missing), K) )).
t('VER-8 receiver other than C rejected',
  ( c(C), proof(P), approver_key(K),
    \+ ver8_ok(C, P, key('agent.near', 'ed25519:A', function_call('relay.near', [request_action], 1)), K) )).
t('VER-8 wrong or extra methods rejected',
  ( c(C), proof(P), approver_key(K),
    \+ ver8_ok(C, P, key('agent.near', 'ed25519:A', function_call(C, [request_action, approve], 1)), K),
    \+ ver8_ok(C, P, key('agent.near', 'ed25519:A', function_call(C, [], 1)), K) )).
t('VER-8 unlimited allowance rejected',
  ( c(C), proof(P), approver_key(K),
    \+ ver8_ok(C, P, key('agent.near', 'ed25519:A', function_call(C, [request_action], unlimited)), K) )).
t('VER-8 key view of another key or account rejected',
  ( c(C), proof(P), approver_key(K),
    \+ ver8_ok(C, P, key('agent.near', 'ed25519:B', function_call(C, [request_action], 1)), K),
    \+ ver8_ok(C, P, key('other.near', 'ed25519:A', function_call(C, [request_action], 1)), K) )).
t('VER-8 approver key with agent methods rejected',
  ( c(C), proof(P), agent_key(A),
    \+ ver8_ok(C, P, A, key('approver.near', 'ed25519:P', function_call(C, [request_action], 1))) )).

%%% accept_proof (all of VER-1..4, VER-8)
evidence(evidence(view('approvals.near', get_approval, final), hashes(h, h, h), lock(locked, [], [function_call]),
                  expect('pay 10', 'agent.near'), ['approver.near'], keys(A, K))) :-
    agent_key(A), approver_key(K).
t('accept_proof: everything holds', ( proof(P), evidence(E), accept_proof(P, E) )).
t('accept_proof: each single violation rejects',
  ( proof(P), evidence(E0),
    forall(mutate(E0, E), \+ accept_proof(P, E)) )).

mutate(evidence(_, H, L, X, W, K), evidence(view('approvals.near', get_approval, optimistic), H, L, X, W, K)).
mutate(evidence(S, _, L, X, W, K), evidence(S, hashes(h, h, h2), L, X, W, K)).
mutate(evidence(S, H, _, X, W, K), evidence(S, H, lock(locked, ['ed25519:X'], []), X, W, K)).
mutate(evidence(S, H, L, _, W, K), evidence(S, H, L, expect('pay 11', 'agent.near'), W, K)).
mutate(evidence(S, H, L, X, _, K), evidence(S, H, L, X, ['nobody.near'], K)).
mutate(evidence(S, H, L, X, W, keys(_, PK)), evidence(S, H, L, X, W, keys(key('agent.near', 'ed25519:A', full_access), PK))).

%% numlist_(N, L): L = [0, ..., N-1]
numlist_(0, []) :- !.
numlist_(N, L) :- N1 is N - 1, findall(I, between(0, N1, I), L).
