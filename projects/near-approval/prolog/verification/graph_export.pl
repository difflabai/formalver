%% graph_export.pl -- MC-3: the labelled reachable graph of step/4 for one
%% small universe, for comparison with TLC's (tools/scripts/mc3.py,
%% tla/MC_Graph.tla).
%%
%% Universe (same as tla/MC_Graph.cfg): owner o, accounts {o, a1, a2}, keys
%% {k1, k2}, roles {agent, approver}, actions {ok(x), empty, too_long},
%% max_pending 1, at most 2 requests and 3 registrations. Every call with
%% every argument is tried in every reached state, including request ids
%% one past the end. A successful call whose target exceeds the bounds is
%% not followed (TLC's actions carry the same bounds).
%%
%% Output, one line per fact, tab-separated:
%%   S <store>                     a reachable store
%%   R <store> <results>           the result (Ok or the error) of every call,
%%                                 comma-separated, in gcall/2's order (mc3.py
%%                                 enumerates the same order)
%%   E <store> <call> <store'>     a successful call within the bounds
%% <store> is P|R|L|G|V in the text format mc3.py also builds from TLC:
%%   P  key,acct,role,rid,from,pending entries, sorted, joined by ';'
%%   R  acct,key,rid,act,AP,RJ per request in id order, joined by ';', with
%%      AP = - | idx/acct/key/rid and RJ = - | acct/key/rid
%%   L  request ids in log order, joined by ','
%%   V  revoked registration ids, sorted, joined by ','
%%
%% Usage: scryer-prolog graph_export.pl -g "export('out.txt'), halt."

:- module(graph_export, [export/1, text_store/2, text_call/2]).

:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(iso_ext)).
:- use_module(library(format)).
:- use_module(library(charsio)).
:- use_module('../model/approval_machine').

accounts([o, a1, a2]).
keys([k1, k2]).
max_req(2).
max_reg(3).

params(P) :- scaled_params(1, 1000000, P).

gcall(_, add(C, K, A, R)) :-
    accounts(As), keys(Ks), member(C, As), member(K, Ks), member(A, As),
    member(R, [agent, approver]).
gcall(_, revoke(C, K)) :-
    accounts(As), keys(Ks), member(C, As), member(K, Ks).
gcall(_, request(c(P, Sg, K), X)) :-
    accounts(As), keys(Ks), member(P, As), member(Sg, As), member(K, Ks),
    member(X, [ok(x), empty, too_long]).
gcall(S, approve(c(P, Sg, K), I, X)) :-
    accounts(As), keys(Ks), member(P, As), member(Sg, As), member(K, Ks),
    request_count(S, N), between(0, N, I), member(X, [ok(x), empty, too_long]).
gcall(S, reject(c(P, Sg, K), I)) :-
    accounts(As), keys(Ks), member(P, As), member(Sg, As), member(K, Ks),
    request_count(S, N), between(0, N, I).

in_bounds(st(_, _, _, R, _, G, _)) :-
    length(R, NR), max_req(MR), NR =< MR, max_reg(MG), G =< MG.

%% Scryer 0.10 reclaims memory only on backtracking, so the search is a
%% failure-driven loop over a FIFO of states in the database; stores are
%% remembered by their text form as an atom (first-argument indexed).
:- dynamic(todo/1).
:- dynamic(seen/1).

export(File) :-
    retractall(todo(_)), retractall(seen(_)),
    params(Ps),
    init_state(Ps, o, S0),
    text_store(S0, T0), atom_chars(A0, T0),
    assertz(seen(A0)), assertz(todo(S0)),
    open(File, write, Out),
    loop(Out),
    close(Out),
    findall(x, seen(_), Xs), length(Xs, N),
    format("graph_export: ~d stores~n", [N]).

loop(Out) :-
    repeat,
    (   retract(todo(S)) -> \+ \+ process(S, Out), fail
    ;   !
    ).

process(S, Out) :-
    text_store(S, TS),
    format(Out, "S\t~s~n", [TS]),
    findall(R, ( gcall(S, C), once(step(S, C, Res, _)), res_text(Res, R) ), Rs),
    join(Rs, ",", TRs),
    format(Out, "R\t~s\t~s~n", [TS, TRs]),
    forall(( gcall(S, C), once(step(S, C, ok(_), S1)) ), edge(C, S1, TS, Out)).

res_text(ok(_), "Ok").
res_text(err(E), T) :- atom_chars(E, T).

edge(C, S1, TS, Out) :-
    (   in_bounds(S1) ->
        text_call(C, TC),
        text_store(S1, TS1),
        format(Out, "E\t~s\t~s\t~s~n", [TS, TC, TS1]),
        atom_chars(A1, TS1),
        (   seen(A1) -> true
        ;   assertz(seen(A1)), assertz(todo(S1))
        )
    ;   true
    ).

%% Text forms (must match mc3.py).
text_store(st(_, _, P, R, L, G, V), T) :-
    maplist(text_p, P, Ps0), sort(Ps0, Ps), join(Ps, ";", TP),
    maplist(text_r, R, Rs), join(Rs, ";", TR),
    maplist(num_chars, L, Ls), join(Ls, ",", TL),
    sort(V, V1), maplist(num_chars, V1, Vs), join(Vs, ",", TV),
    number_codes(G, GC), atom_codes(GA, GC), atom_chars(GA, TG),
    append([TP, "|", TR, "|", TL, "|", TG, "|", TV], T).

text_p(K-p(A, Role, Rid, From, Pend), T) :-
    fmt("~w,~w,~w,~d,~d,~d", [K, A, Role, Rid, From, Pend], T).

text_r(req(_, A, K, Rid, Act, Ap, Rj), T) :-
    text_act(Act, TA), text_ap(Ap, TAp), text_rj(Rj, TRj),
    fmt("~w,~w,~d,~s,~s,~s", [A, K, Rid, TA, TAp, TRj], T).

text_ap(none, "-").
text_ap(ap(I, A, K, Rid), T) :- fmt("~d/~w/~w/~d", [I, A, K, Rid], T).
text_rj(none, "-").
text_rj(rj(A, K, Rid), T) :- fmt("~w/~w/~d", [A, K, Rid], T).

text_act(ok(X), T) :- fmt("~w", [X], T).
text_act(empty, "empty").
text_act(too_long, "too_long").

text_call(add(C, K, A, R), T) :- fmt("add,~w,~w,~w,~w", [C, K, A, R], T).
text_call(revoke(C, K), T) :- fmt("revoke,~w,~w", [C, K], T).
text_call(request(c(P, S, K), X), T) :-
    text_act(X, TX), fmt("request,~w,~w,~w,~s", [P, S, K, TX], T).
text_call(approve(c(P, S, K), I, X), T) :-
    text_act(X, TX), fmt("approve,~w,~w,~w,~d,~s", [P, S, K, I, TX], T).
text_call(reject(c(P, S, K), I), T) :- fmt("reject,~w,~w,~w,~d", [P, S, K, I], T).

fmt(F, Args, T) :- phrase(format_(F, Args), T).
num_chars(N, T) :- fmt("~d", [N], T).

join([], _, []).
join([X], _, X) :- !.
join([X | Xs], Sep, T) :- join(Xs, Sep, T1), append([X, Sep, T1], T).
