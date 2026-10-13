%% mc2.pl -- MC-2: traces shared between step/4 and the real core.
%%
%% Format (kani/src/mc2.rs): one line per call, `<call>\t<result>\t<post>`,
%% a line `#` ends a trace, each trace starts from Init with owner o. Store
%% and call texts are graph_export.pl's; actions t1..t3 are ok(t1)..ok(t3).
%%
%%   replay(File)       replays the core's traces (kani: target/mc2/core.txt)
%%                      on step/4; fails at the first disagreement
%%   generate(File, N)  writes N traces of 80 calls from step/4, for
%%                      kani's mc2_prolog_traces to replay on the core
%%
%% Real constants, except max_u (no counter gets near u64::MAX in a trace).

:- module(mc2, [replay/1, generate/2]).

:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(iso_ext)).
:- use_module(library(format)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(charsio)).
:- use_module('../model/approval_machine').
:- use_module(graph_export).

params(P) :- real_params(P0), P0 = params(N, MP, _, PG, DPG), P = params(N, MP, 1000000000, PG, DPG).

start(S) :- params(P), init_state(P, o, S).

%%% Reading ------------------------------------------------------------

lines([L | Ls]) --> line(L), !, lines(Ls).
lines([]) --> [].
line(L) --> chars_until_nl(L), ( "\n" -> [] ; { L \== [] } ).
chars_until_nl([C | Cs]) --> [C], { C \== '\n' }, !, chars_until_nl(Cs).
chars_until_nl([]) --> [].

split([], _, [[]]).
split([C | Cs], C, [[] | Rest]) :- !, split(Cs, C, Rest).
split([X | Cs], C, [[X | W] | Rest]) :- split(Cs, C, [W | Rest]).

atom_or_num(Cs, T) :- catch(number_chars(T, Cs), _, fail), !.
atom_or_num(Cs, T) :- atom_chars(T, Cs).

action(t1, ok(t1)).
action(t2, ok(t2)).
action(t3, ok(t3)).
action(empty, empty).
action(too_long, too_long).

parse_call(Cs, Op) :-
    split(Cs, ',', Fs0), maplist(atom_or_num, Fs0, Fs),
    call_term(Fs, Op).

call_term([add, C, K, A, R], add(C, K, A, R)).
call_term([revoke, C, K], revoke(C, K)).
call_term([request, P, S, K, X], request(c(P, S, K), A)) :- action(X, A).
call_term([approve, P, S, K, I, X], approve(c(P, S, K), I, A)) :- action(X, A).
call_term([reject, P, S, K, I], reject(c(P, S, K), I)).

result_text(ok(_), "Ok").
result_text(err(E), T) :- atom_chars(E, T).

%%% Replay ---------------------------------------------------------------

replay(File) :-
    phrase_from_file(lines(Ls), File),
    start(S0),
    replay_(Ls, S0, 1, 0, 0, NT, NS),
    format("mc2: ~d core traces, ~d steps replayed on step/4~n", [NT, NS]).

replay_([], _, _, T, S, T, S).
replay_(["#" | Ls], _, N, T0, S0, T, S) :- !,
    start(St), N1 is N + 1, T1 is T0 + 1,
    replay_(Ls, St, N1, T1, S0, T, S).
replay_([L | Ls], St0, N, T0, S0, T, S) :-
    split(L, '\t', [CallT, ResT, PostT]),
    parse_call(CallT, Op),
    once(step(St0, Op, Res, St1)),
    result_text(Res, RT),
    text_store(St1, PT),
    (   RT == ResT, PT == PostT -> true
    ;   format("MC-2 line ~d: ~s~n  core:   ~s -> ~s~n  step/4: ~s -> ~s~n",
               [N, CallT, ResT, PostT, RT, PT]),
        fail
    ),
    N1 is N + 1, S1 is S0 + 1,
    replay_(Ls, St1, N1, T0, S1, T, S).

%%% Generation -----------------------------------------------------------

%% A 31-bit LCG, so the traces are the same on every run.
next(X0, X) :- X is (X0 * 1103515245 + 12345) mod 2147483648.
pick(L, X0, X, E) :- next(X0, X), length(L, N), I is (X >> 8) mod N, nth0(I, L, E).

accounts([o, a1, a2, a3]).
keys([k0, k1, k2, k3]).

%% A random call, biased toward ones that can pass: callers sign with the
%% account a key is registered to.
rand_call(S, X0, X, Op) :-
    next(X0, X1), Kind is (X1 >> 8) mod 10,
    accounts(As), keys(Ks),
    pick(Ks, X1, X2, K),
    (   principal(S, K, p(Acct, _, _, _, _)), next(X2, X3), (X3 >> 8) mod 100 < 85
    ->  Signer = Acct
    ;   next(X2, X3), pick(As, X3, _, Signer)
    ),
    next(X3, X4),
    (   (X4 >> 8) mod 100 < 92 -> Pred = Signer ; pick(As, X4, _, Pred) ),
    next(X4, X5),
    pick([t1, t2, t3, t1, t2, t3, empty, too_long], X5, X6, XA), action(XA, Act),
    request_count(S, NR),
    next(X6, X7), I is (X7 >> 8) mod (NR + 1),
    (   I < NR, request_at(S, I, req(_, _, _, _, Stored, _, _)), (X7 >> 4) mod 100 < 85
    ->  AAct = Stored
    ;   AAct = Act
    ),
    next(X7, X8),
    (   (X8 >> 8) mod 100 < 90 -> Admin = o ; pick(As, X8, _, Admin) ),
    pick(As, X8, X9, Acc2),
    next(X9, X10), ( (X10 >> 8) mod 2 =:= 0 -> Role = agent ; Role = approver ),
    (   Kind =< 2 -> Op = add(Admin, K, Acc2, Role)
    ;   Kind =:= 3 -> Op = revoke(Admin, K)
    ;   Kind =< 6 -> Op = request(c(Pred, Signer, K), Act)
    ;   Kind =:= 7 -> Op = reject(c(Pred, Signer, K), I)
    ;   Op = approve(c(Pred, Signer, K), I, AAct)
    ),
    X = X10.

generate(File, N) :-
    open(File, write, Out),
    forall(between(1, N, T), \+ \+ gen_trace(Out, T)),
    close(Out),
    format("mc2: wrote ~d traces from step/4~n", [N]).

gen_trace(Out, T) :-
    start(S0),
    Seed is T * 7919 + 17,
    gen_steps(80, S0, Seed, Out),
    format(Out, "#~n", []).

gen_steps(0, _, _, _) :- !.
gen_steps(N, S0, X0, Out) :-
    rand_call(S0, X0, X1, Op),
    once(step(S0, Op, Res, S1)),
    text_call(Op, CT),
    result_text(Res, RT),
    text_store(S1, PT),
    format(Out, "~s\t~s\t~s~n", [CT, RT, PT]),
    N1 is N - 1,
    gen_steps(N1, S1, X1, Out).
