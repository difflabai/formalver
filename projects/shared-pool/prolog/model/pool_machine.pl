%% pool_machine.pl -- Reference semantics step/4 of pool-core (shared-pool-controls)
%%
%% PROP: MC-1 MC-2 C-5
%%
%% Written from docs/spec.md and docs/api.md (cited per clause). The guard
%% ORDER is not restated here: step/4 walks guard/5 of requirements/pool_req.pl,
%% so the model's behaviour is the requirement table, and MC-2 checks it against
%% the real core. Where the docs are silent the clause follows the code and is
%% tagged CODE-ONLY; where docs and code disagree the clause follows the code
%% and names the divergence/4 id (a finding, see RESULTS.md).
%%
%% Values are exact integers; u32/u64 widths appear only where the code can
%% reach them (version overflow, saturating time sums).
%%
%% Config (conformance trace format):
%%   config(Owner, MaxAge, Metrics, Terms, Recipes)
%%     Metrics = [m(Min, Max, Initial)..]
%%     Terms   = [t(Metric, Target, Weight, Shape)..]   Shape: target | excess | deficit
%%     Recipes = [r(Actor, Executor, Reserve, Complete, MaxUnits, [p(Recipe, Units)..])..]
%% State:
%%   pool(Config, Values, Version, ObservedAt, Paused, Records)
%%     Records = [c(Recipe, Units, ExpiresAt, Status)..], id = list index (spec:25 append)
%% Ops (trace format):
%%   submit(Caller, Recipe, Units, Version, ExpiresAt, Now)
%%   dispatch(Caller, Id, Now)    ack(Id, Accepted)        cancel(Caller, Id, Now)
%%   settle(Caller, Id, Completed) pause(Caller, Paused)   observe(Caller, Values, Now)
%% Result: ok | ok(Id) | err(snake_case_error)

:- module(pool_machine, [
    valid_config/1,
    init_state/3,
    step/4,
    classify/3,
    op_guard_kind/2,
    to_trace_state/2,
    pool_config/2,
    pool_values/2,
    pool_version/2,
    pool_records/2,
    pool_paused/2,
    recipe_of/3,
    record_of/3,
    actor_of/3,
    executor_of/3,
    owner_of/2,
    add_vec/4,
    sub_vec/4,
    envelope/7,
    envelope_opts/8,
    point_violation/3,
    interval_violation/4,
    violating/2,
    energy/3,
    completed_units/3,
    admissible/3,
    admissible_opts/4,
    preview_allowed/3,
    best_quantity/4,
    u32_max/1,
    u64_max/1,
    model_constant/3
]).

:- use_module(library(lists)).
:- use_module(library(between)).
:- use_module(library(iso_ext)).
:- use_module('../requirements/pool_req').

:- discontiguous(holds/4).

u32_max(M) :- model_constant(version_width, W, _), M is 2^W - 1.
u64_max(M) :- model_constant(time_width, W, _), M is 2^W - 1.

%% model_constant(Name, Value, Basis): the bounds this model uses that the docs
%% do not state (CODE-ONLY). C-4 compares each with extracted/code_facts.pl.
model_constant(max_metrics, 32,  code_only('docs silent; core MAX_METRICS')).
model_constant(max_recipes, 32,  code_only('docs silent; core MAX_RECIPES')).
model_constant(max_units,   100, code_only('docs silent; core MAX_UNITS')).
model_constant(max_requires, 32, code_only('docs silent; validate bounds requires by MAX_RECIPES')).
model_constant(version_width, 32, code_only('handoff:34 names version overflow; the width u32 is the code\'s')).
model_constant(time_width,    64, code_only('saturating u64 time sums (expiry, freshness)')).

max_value(V) :- constant(max_value, V, _).

bounded(X) :- max_value(M), X >= -M, X =< M.

sat_add64(A, B, C) :- u64_max(U), C is min(A + B, U).

%%% ========================================================
%%% Accessors
%%% ========================================================

pool_config(pool(C, _, _, _, _, _), C).
pool_values(pool(_, V, _, _, _, _), V).
pool_version(pool(_, _, N, _, _, _), N).
pool_records(pool(_, _, _, _, _, R), R).
pool_paused(pool(_, _, _, _, P, _), P).

owner_of(config(O, _, _, _, _), O).
recipe_of(config(_, _, _, _, Rs), I, R) :- integer(I), I >= 0, nth0(I, Rs, R).
actor_of(Cfg, I, A) :- recipe_of(Cfg, I, r(A, _, _, _, _, _)).
executor_of(Cfg, I, X) :- recipe_of(Cfg, I, r(_, X, _, _, _, _)).
record_of(pool(_, _, _, _, _, Rs), Id, Rec) :- integer(Id), Id >= 0, nth0(Id, Rs, Rec).

to_trace_state(pool(_, V, N, O, P, R), s(V, N, O, P, R)).

%%% ========================================================
%%% Configuration (spec:9, spec:13; handoff:11)
%%% ========================================================
%% Numeric part of Config::validate. The code also checks name/unit/owner
%% string lengths (1..128): CODE-ONLY and not representable in trace configs.

valid_config(config(Owner, MaxAge, Ms, Ts, Rs)) :-
    atom(Owner), integer(MaxAge), MaxAge >= 0,
    model_constant(max_metrics, MaxM, _), model_constant(max_recipes, MaxR, _),
    length(Ms, N), N >= 1, N =< MaxM,                   % CODE-ONLY: MAX_METRICS
    length(Rs, NR), NR >= 1, NR =< MaxR,                 % CODE-ONLY: MAX_RECIPES
    length(Ts, NT), NT >= 1, constant(max_terms, MT, _), NT =< MT,   % spec:13
    forall(member(m(Lo, Hi, I), Ms),
           ( bounded(Lo), bounded(Hi), Lo =< Hi, I >= Lo, I =< Hi )),      % spec:13
    constant(max_weight, MW, _),
    forall(member(t(K, Tg, W, Sh), Ts),
           ( integer(K), K >= 0, K < N, bounded(Tg), W >= 1, W =< MW,        % spec:13, 31
             member(Sh, [target, excess, deficit]) )),
    valid_recipes(Rs, 0, N).

valid_recipes([], _, _).
valid_recipes([r(A, X, Res, Com, MU, Req) | Rs], I, N) :-
    % CODE-ONLY (amb-self-executor, finding F-4): A == X, or either equal to the
    % owner, is accepted, as in Config::validate; the docs claim independence
    % only for the hiring fixture (spec:64).
    atom(A), atom(X),
    length(Res, N), length(Com, N),                      % spec:9 effects span all metrics
    forall(member(D, Res), bounded(D)), forall(member(D, Com), bounded(D)),  % spec:13
    model_constant(max_units, MaxU, _), model_constant(max_requires, MaxQ, _),
    MU >= 1, MU =< MaxU,                                 % CODE-ONLY: MAX_UNITS
    length(Req, NQ), NQ =< MaxQ,
    forall(member(p(P, U), Req), ( P >= 0, P < I, U >= 1, U =< MaxU )),  % spec:9 earlier recipes
    findall(P, member(p(P, _), Req), Ps), sort(Ps, Ss), length(Ss, NQ),  % CODE-ONLY: distinct ids
    I1 is I + 1,
    valid_recipes(Rs, I1, N).

%% init_state(+Config, +Now, -Pool): Pool::new (spec:7; handoff:25 "Config validates
%% initial values within bounds"). Version 0, observed_at = Now, unpaused, no records.
init_state(Cfg, Now, pool(Cfg, Vs, 0, Now, false, [])) :-
    valid_config(Cfg),
    Cfg = config(_, _, Ms, _, _),
    findall(I, member(m(_, _, I), Ms), Vs).

%%% ========================================================
%%% Arithmetic (spec:13, 19, 21, 23)
%%% ========================================================

%% add_vec(+Base, +Delta, +Units, -Out): checked, fails if any component leaves
%% [-1e6, 1e6] (spec:13 "Every update is checked"; NUM-2).
add_vec([], [], _, []).
add_vec([B | Bs], [D | Ds], U, [V | Vs]) :-
    V is B + D * U, bounded(V),
    add_vec(Bs, Ds, U, Vs).

%% sub_vec(+Base, +Delta, +Units, -Out): the checked inverse (spec:41-42).
sub_vec(Bs, Ds, U, Vs) :- findall(N, ( member(D, Ds), N is -D ), Ns), add_vec(Bs, Ns, U, Vs).

%% point_violation(+Metrics, +Values, -PV): PV_i = max(0, min-v) + max(0, v-max).
point_violation([], [], []).
point_violation([m(Lo, Hi, _) | Ms], [V | Vs], [P | Ps]) :-
    P is max(0, Lo - V) + max(0, V - Hi),
    point_violation(Ms, Vs, Ps).

%% interval_violation(+Metrics, +Low, +High, -EV)   (AMBIGUOUS amb-interval-violation)
interval_violation([], [], [], []).
interval_violation([m(Lo, Hi, _) | Ms], [L | Ls], [H | Hs], [E | Es]) :-
    E is max(0, Lo - L) + max(0, H - Hi),
    interval_violation(Ms, Ls, Hs, Es).

violating(Cfg, Values) :-
    Cfg = config(_, _, Ms, _, _),
    point_violation(Ms, Values, PV),
    member(P, PV), P > 0, !.

%% envelope(+Cfg, +Records, +Values, +Extra, +Skip, -Low, -High)
%% spec:21: an interval per metric containing every subset of the outstanding
%% (open) completion effects plus the proposed one. Negative parts go to Low,
%% positive parts to High (spec:21 "Independent positive effects contribute to
%% the high endpoint and negative effects to the low endpoint").
%% Extra = none | extra(Recipe, Units); Skip = none | Id (the record being
%% settled or cancelled is not "other pending", spec:41).
%% Fails (Arithmetic) if an endpoint leaves [-1e6, 1e6]. CODE-ONLY: the code
%% checks after every addition; the partial sums are monotone, so that is the
%% same as checking the final endpoints.
envelope(Cfg, Recs, Values, Extra, Skip, Low, High) :-
    envelope_opts(Cfg, Recs, Values, Extra, Skip, [], Low, High).

%% envelope_opts/8: Opts = [ignore_pending_negative] drops the negative parts
%% of the OPEN records' completions (used only by C-5's RISK-HEADROOM check).
envelope_opts(Cfg, Recs, Values, Extra, Skip, Opts, Low, High) :-
    Cfg = config(_, _, _, _, Rs),
    pending_effects(Recs, 0, Rs, Skip, Effs0),
    (   memberchk(ignore_pending_negative, Opts)
    ->  findall(P, ( member(E, Effs0), maplist(pos_part, E, P) ), Effs1)
    ;   Effs1 = Effs0
    ),
    (   Extra = extra(RI, U)
    ->  nth0(RI, Rs, r(_, _, _, Com, _, _)), scale(Com, U, X), append(Effs1, [X], Effs)
    ;   Effs = Effs1
    ),
    sum_parts(Effs, Values, Low, High),
    maplist(bounded, Low), maplist(bounded, High).

pending_effects([], _, _, _, []).
pending_effects([c(RI, U, _, St) | Cs], Id, Rs, Skip, Out) :-
    Id1 is Id + 1,
    (   open_status(St), Skip \== Id
    ->  nth0(RI, Rs, r(_, _, _, Com, _, _)), scale(Com, U, E), Out = [E | Out1]
    ;   Out = Out1
    ),
    pending_effects(Cs, Id1, Rs, Skip, Out1).

scale(Ds, U, Xs) :- findall(X, ( member(D, Ds), X is D * U ), Xs).
pos_part(X, Y) :- Y is max(0, X).

sum_parts([], V, V, V).
sum_parts([E | Es], V, Low, High) :-
    sum_parts(Es, V, L0, H0),
    add_parts(E, L0, H0, Low, High).
add_parts([], [], [], [], []).
add_parts([D | Ds], [L | Ls], [H | Hs], [L1 | Ls1], [H1 | Hs1]) :-
    L1 is L + min(0, D), H1 is H + max(0, D),
    add_parts(Ds, Ls, Hs, Ls1, Hs1).

%% hard_ok(+Cfg, +Current, +Low, +High): spec:21 "In a healthy state, all intervals
%% must fit. In a disturbed state, no metric's violation amount may exceed its
%% current violation." Current = the pool's values before the call.
hard_ok(Cfg, Current, Low, High) :-
    Cfg = config(_, _, Ms, _, _),
    point_violation(Ms, Current, PV),
    interval_violation(Ms, Low, High, EV),
    \+ ( nth0(I, EV, E), nth0(I, PV, P), E > P ).

%% energy(+Cfg, +Values, -E): spec:31, sum of w * r^2 with r the target
%% deviation |v - t|, excess max(0, v - t) or deficit max(0, t - v).
energy(config(_, _, _, Ts, _), Vs, E) :- energy_(Ts, Vs, 0, E).
energy_([], _, E, E).
energy_([t(K, Tg, W, Sh) | Ts], Vs, E0, E) :-
    nth0(K, Vs, V), residual(Sh, V, Tg, R),
    E1 is E0 + W * R * R,
    energy_(Ts, Vs, E1, E).
residual(target,  V, T, R) :- R is abs(V - T).
residual(excess,  V, T, R) :- R is max(0, V - T).
residual(deficit, V, T, R) :- R is max(0, T - V).

completed_units(Recs, P, N) :-
    findall(U, member(c(P, U, _, completed), Recs), Us), sum_list(Us, N).

%%% ========================================================
%%% step/4
%%% ========================================================

op_guard_kind(submit(_, _, _, _, _, _), submit).
op_guard_kind(dispatch(_, _, _),        dispatch).
op_guard_kind(ack(_, _),                ack).
op_guard_kind(cancel(_, _, _),          cancel).
op_guard_kind(settle(_, _, true),       settle_completed).
op_guard_kind(settle(_, _, false),      settle_cancelled).
op_guard_kind(pause(_, _),              pause).
op_guard_kind(observe(_, _, _),         observe).

%% step(+S0, +Op, -Result, -S1). A rejected or no-op call leaves the state
%% unchanged (spec:25 "On rejection return an error with no state change";
%% handoff:15; spec:43-44 idempotent / ignored).
step(S0, Op, Result, S1) :-
    op_guard_kind(Op, Kind),
    guard_ids(Kind, Ids),
    (   first_stop(Ids, Kind, S0, Op, Outcome)
    ->  S1 = S0,
        (   Outcome = err(E) -> camel_snake(E, Sn), Result = err(Sn)
        ;   Result = ok
        )
    ;   effect(Kind, S0, Op, Result, S1)
    ).

%% classify(+S0, +Op, -Class): stop(err(Error)) | stop(noop) | effect -- which
%% guard decides the call (used by the step properties: TX-NOOP, TX-VER).
classify(S0, Op, Class) :-
    op_guard_kind(Op, Kind),
    guard_ids(Kind, Ids),
    (   first_stop(Ids, Kind, S0, Op, Outcome) -> Class = stop(Outcome) ; Class = effect ).

first_stop([G | Gs], Kind, S, Op, Outcome) :-
    (   holds(Kind, G, S, Op) -> first_stop(Gs, Kind, S, Op, Outcome)
    ;   once(guard(Kind, _, G, Outcome, _))
    ).

%% holds(+Kind, +GuardId, +S, +Op): the guard passes. A guard may assume that
%% every guard before it in guard/5 order passed.

% --- shared
holds(_, version_overflow, S, _) :- pool_version(S, N), u32_max(M), N < M.   % handoff:34
holds(_, found, S, Op) :- op_id(Op, Id), record_of(S, Id, _).               % CODE-ONLY: NotFound

% --- submit (spec:19-23)
holds(submit, paused, S, _) :- pool_paused(S, false).
holds(submit, version, S, submit(_, _, _, V, _, _)) :- pool_version(S, N), V =:= N.
holds(submit, expiry, _, submit(_, _, _, _, Exp, Now)) :-
    constant(expiry_horizon, H, _),
    sat_add64(Now, H, Max),                 % CODE-ONLY: saturating u64 sum
    Exp > Now, Exp =< Max.
holds(submit, freshness, S, submit(_, _, _, _, _, Now)) :- fresh(S, Now).
holds(submit, record_bound, S, _) :-
    pool_records(S, Rs), length(Rs, N), constant(max_records, M, _), N < M.
holds(submit, recipe, S, submit(_, RI, _, _, _, _)) :- pool_config(S, C), recipe_of(C, RI, _).
holds(submit, caller, S, submit(Caller, RI, _, _, _, _)) :- pool_config(S, C), actor_of(C, RI, A), Caller == A.
holds(submit, units, S, submit(_, RI, U, _, _, _)) :-
    pool_config(S, C), recipe_of(C, RI, r(_, _, _, _, MU, _)), U >= 1, U =< MU.
holds(submit, prerequisites, S, submit(_, RI, _, _, _, _)) :-              % spec:19; handoff:19
    pool_config(S, C), recipe_of(C, RI, r(_, _, _, _, _, Req)), pool_records(S, Recs),
    forall(member(p(P, U), Req), ( completed_units(Recs, P, N), N >= U )).
holds(submit, reserve_arith, S, Op) :- submit_next(S, Op, _).
holds(submit, envelope_arith, S, Op) :- submit_envelope(S, Op, _, _).
holds(submit, bounds, S, Op) :-
    submit_envelope(S, Op, Low, High), pool_config(S, C), pool_values(S, V),
    hard_ok(C, V, Low, High).
holds(submit, energy, S, Op) :-
    submit_next(S, Op, Next), pool_config(S, C), pool_values(S, V),
    energy(C, Next, E1), energy(C, V, E0), E1 =< E0.
holds(submit, recovery, S, Op) :-
    pool_config(S, C), pool_values(S, V),
    (   \+ violating(C, V) -> true
    ;   Op = submit(_, RI, U, _, _, _),
        submit_next(S, Op, Next), recipe_of(C, RI, r(_, _, _, Com, _, _)),
        (   add_vec(Next, Com, U, After) -> true
        ;   % CODE-ONLY: the code's add here returns Arithmetic, which cannot
            % happen once the envelope (guard envelope_arith) passed; surfaced loudly.
            throw(unreachable(recovery_add, S, Op))
        ),
        energy(C, After, EA), energy(C, V, E0), EA < E0
    ).

submit_next(S, submit(_, RI, U, _, _, _), Next) :-
    pool_config(S, C), recipe_of(C, RI, r(_, _, Res, _, _, _)), pool_values(S, V),
    add_vec(V, Res, U, Next).
submit_envelope(S, Op, Low, High) :-
    Op = submit(_, RI, U, _, _, _),
    submit_next(S, Op, Next), pool_config(S, C), pool_records(S, Recs),
    envelope(C, Recs, Next, extra(RI, U), none, Low, High).

fresh(S, Now) :-
    S = pool(config(_, MaxAge, _, _, _), _, _, Obs, _, _),
    (   MaxAge =:= 0 -> true
    ;   sat_add64(Obs, MaxAge, Lim), Now =< Lim
    ).

% --- dispatch (spec:37)
holds(dispatch, caller, S, dispatch(Caller, Id, _)) :-
    record_of(S, Id, c(RI, _, _, _)), pool_config(S, C), actor_of(C, RI, A), Caller == A.
holds(dispatch, paused, S, _) :- pool_paused(S, false).
holds(dispatch, reserved, S, dispatch(_, Id, _)) :- record_of(S, Id, c(_, _, _, reserved)).
holds(dispatch, unexpired, S, dispatch(_, Id, Now)) :- record_of(S, Id, c(_, _, Exp, _)), Now < Exp.
holds(dispatch, freshness, S, dispatch(_, _, Now)) :- fresh(S, Now).

% --- acknowledge (spec:38-39, 44)
holds(ack, awaiting, S, ack(Id, _)) :-
    record_of(S, Id, c(_, _, _, St)), memberchk(St, [dispatched, unknown]).
% CODE-ONLY / div-ack-noop-version: an acknowledgment that would not change the
% status is ignored and does not bump version.
holds(ack, changes_status, S, ack(Id, Acc)) :-
    record_of(S, Id, c(_, _, _, St)), ack_next(Acc, Next), St \== Next.
ack_next(true, active).
ack_next(false, unknown).

% --- cancel (spec:41, 43; api:15)
holds(cancel, caller, S, cancel(Caller, Id, _)) :-
    record_of(S, Id, c(RI, _, _, _)), pool_config(S, C),
    actor_of(C, RI, A), owner_of(C, O), ( Caller == A ; Caller == O ), !.
holds(cancel, not_cancelled, S, cancel(_, Id, _)) :- record_of(S, Id, c(_, _, _, St)), St \== cancelled.
holds(cancel, reserved, S, cancel(_, Id, _)) :- record_of(S, Id, c(_, _, _, reserved)).
holds(Kind, release_arith, S, Op) :- release_kind(Kind), op_id(Op, Id), release_next(S, Id, _).
holds(Kind, envelope_arith, S, Op) :-
    terminal_kind(Kind), op_id(Op, Id), terminal_next(Kind, S, Id, Next),
    pool_config(S, C), pool_records(S, Recs),
    envelope(C, Recs, Next, none, Id, _, _).
holds(Kind, bounds, S, Op) :-
    terminal_kind(Kind), op_id(Op, Id), terminal_next(Kind, S, Id, Next),
    pool_config(S, C), pool_records(S, Recs), pool_values(S, V),
    envelope(C, Recs, Next, none, Id, Low, High),
    hard_ok(C, V, Low, High).

% --- settle (spec:40, 42, 43)
holds(Kind, caller, S, settle(Caller, Id, _)) :-
    settle_kind(Kind),
    record_of(S, Id, c(RI, _, _, _)), pool_config(S, C), executor_of(C, RI, X), Caller == X.
holds(Kind, not_same_terminal, S, settle(_, Id, Done)) :-
    settle_kind(Kind),
    record_of(S, Id, c(_, _, _, St)),
    \+ ( Done == true, St == completed ),
    \+ ( Done == false, St == cancelled ).
holds(Kind, in_flight, S, settle(_, Id, _)) :-
    settle_kind(Kind),
    record_of(S, Id, c(_, _, _, St)), memberchk(St, [dispatched, active, unknown]).
holds(settle_completed, complete_arith, S, settle(_, Id, _)) :- complete_next(S, Id, _).

% --- set_paused (spec:54)
holds(pause, owner, S, pause(Caller, _)) :- pool_config(S, C), owner_of(C, O), Caller == O.

% --- observe (spec:54)
holds(observe, owner, S, observe(Caller, _, _)) :- pool_config(S, C), owner_of(C, O), Caller == O.
holds(observe, all_terminal, S, _) :- pool_records(S, Rs), \+ ( member(c(_, _, _, St), Rs), open_status(St) ).
holds(observe, bounded_values, S, observe(_, Vs, _)) :-
    pool_values(S, V0), length(V0, N), length(Vs, N),          % CODE-ONLY: length (amb-observe-length)
    maplist(bounded, Vs).

release_kind(cancel).
release_kind(settle_cancelled).
terminal_kind(cancel).
terminal_kind(settle_cancelled).
terminal_kind(settle_completed).
settle_kind(settle_completed).
settle_kind(settle_cancelled).

op_id(dispatch(_, Id, _), Id).
op_id(ack(Id, _), Id).
op_id(cancel(_, Id, _), Id).
op_id(settle(_, Id, _), Id).

release_next(S, Id, Next) :-
    record_of(S, Id, c(RI, U, _, _)), pool_config(S, C), recipe_of(C, RI, r(_, _, Res, _, _, _)),
    pool_values(S, V), sub_vec(V, Res, U, Next).
complete_next(S, Id, Next) :-
    record_of(S, Id, c(RI, U, _, _)), pool_config(S, C), recipe_of(C, RI, r(_, _, _, Com, _, _)),
    pool_values(S, V), add_vec(V, Com, U, Next).
terminal_next(settle_completed, S, Id, Next) :- !, complete_next(S, Id, Next).
terminal_next(_, S, Id, Next) :- release_next(S, Id, Next).

%%% Effects of calls whose guards all pass

% spec:25 "append a Reserved record, replace values, increment version"
effect(submit, S0, Op, ok(Id), S1) :-
    Op = submit(_, RI, U, _, Exp, _),
    submit_next(S0, Op, Next),
    S0 = pool(C, _, N, Obs, P, Recs),
    length(Recs, Id),
    append(Recs, [c(RI, U, Exp, reserved)], Recs1),
    N1 is N + 1,
    S1 = pool(C, Next, N1, Obs, P, Recs1).
% spec:37 Reserved -> Dispatched (the shell then creates the promise)
effect(dispatch, S0, dispatch(_, Id, _), ok, S1) :- set_status(S0, Id, dispatched, S1).
% spec:38-39; "retain values" (ASYNC-1)
effect(ack, S0, ack(Id, Acc), ok, S1) :- ack_next(Acc, St), set_status(S0, Id, St, S1).
% spec:41-42 checked inverse: subtract the reservation, Cancelled
effect(Kind, S0, Op, ok, S1) :-
    release_kind(Kind), op_id(Op, Id),
    release_next(S0, Id, Next),
    set_status(S0, Id, cancelled, S0a),
    S0a = pool(C, _, N, O, P, R), S1 = pool(C, Next, N, O, P, R).
% spec:40 add completion delta, Completed
effect(settle_completed, S0, settle(_, Id, _), ok, S1) :-
    complete_next(S0, Id, Next),
    set_status(S0, Id, completed, S0a),
    S0a = pool(C, _, N, O, P, R), S1 = pool(C, Next, N, O, P, R).
% spec:54 set_paused increments version (also when the flag does not change: CODE-ONLY)
effect(pause, pool(C, V, N, O, _, R), pause(_, B), ok, pool(C, V, N1, O, B, R)) :- N1 is N + 1.
% spec:54 replaces values, refreshes the snapshot time; handoff:34 advances version
effect(observe, pool(C, _, N, _, P, R), observe(_, Vs, Now), ok, pool(C, Vs, N1, Now, P, R)) :- N1 is N + 1.

set_status(pool(C, V, N, O, P, R0), Id, St, pool(C, V, N1, O, P, R1)) :-
    N1 is N + 1,
    nth0(Id, R0, c(RI, U, E, _), Rest),
    nth0(Id, R1, c(RI, U, E, St), Rest).

%%% ========================================================
%%% Reads (spec:27; api:10, 26-28)
%%% ========================================================

%% admissible(+S, +Caller, +Req): candidate(caller, req, now) is Ok, i.e. every
%% submit guard except version_overflow passes (spec:27 "preview calls the same
%% checker"). Req = req(Recipe, Units, Version, ExpiresAt, Now).
admissible(S, Caller, Req) :- admissible_opts(S, Caller, Req, []).

%% admissible_opts/4 with Opts = [ignore_pending_negative]: the same check with
%% the open records' negative completion parts dropped from the envelope (C-5
%% RISK-HEADROOM compares the two).
admissible_opts(S, Caller, req(RI, U, V, Exp, Now), Opts) :-
    Op = submit(Caller, RI, U, V, Exp, Now),
    guard_ids(submit, Ids),
    forall(( member(G, Ids), G \== version_overflow ), holds_opts(G, S, Op, Opts)).

holds_opts(G, S, Op, Opts) :-
    (   memberchk(ignore_pending_negative, Opts), memberchk(G, [envelope_arith, bounds])
    ->  Op = submit(_, RI, U, _, _, _),
        submit_next(S, Op, Next), pool_config(S, C), pool_records(S, Recs),
        envelope_opts(C, Recs, Next, extra(RI, U), none, Opts, Low, High),
        (   G == bounds -> pool_values(S, V0), hard_ok(C, V0, Low, High) ; true )
    ;   holds(submit, G, S, Op)
    ).

preview_allowed(S, Caller, Req) :- admissible(S, Caller, Req).

%% best_quantity(+S, +Caller, +Req, -Best): spec:27 enumerate units 1..min(units, 100)
%% (CODE-ONLY cap MAX_UNITS), minimise energy of the candidate, ties -> larger units.
%% Best = none | some(Units).
best_quantity(S, Caller, req(RI, U, V, Exp, Now), Best) :-
    model_constant(max_units, MaxU, _), Hi is min(U, MaxU),
    pool_config(S, C),
    findall(E-Neg, ( between(1, Hi, K),
                     admissible(S, Caller, req(RI, K, V, Exp, Now)),
                     submit_next(S, submit(Caller, RI, K, V, Exp, Now), Next),
                     energy(C, Next, E), Neg is -K ), Cands),
    (   Cands == [] -> Best = none
    ;   keysort_first(Cands, _-NegB), K0 is -NegB, Best = some(K0)
    ).

%% keysort_first(+Pairs, -Least): the least E-Neg pair in standard order
%% (smallest energy, then smallest -Units = largest units).
keysort_first([P | Ps], Least) :- keysort_first_(Ps, P, Least).
keysort_first_([], L, L).
keysort_first_([P | Ps], L0, L) :- ( P @< L0 -> keysort_first_(Ps, P, L) ; keysort_first_(Ps, L0, L) ).
