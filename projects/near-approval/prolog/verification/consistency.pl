%% consistency.pl -- Requirement checks C-1..C-10 and C-2t (strategy 5.11, 17.5)
%%
%% c_check(Id, Result) with Result one of
%%   pass(Note)               the check holds
%%   fail(Reason)             the check fails
%%   pending(Decision, Note)  the check needs input that does not exist yet; the
%%                            Decision must be a decision/2 fact (a pending
%%                            result without a recorded decision is a failure)
%%
%% Extracted inputs (generated, not hand-written; strategy section 8). When a file
%% exists, the code-facing part of the check runs against it. Expected terms:
%%   extracted/code_facts.pl:
%%     code_error(Name, Message).          one per ApprovalError variant (as_str)
%%     code_constant(Name, Value).         Name in max_action_len, max_pending_per_key,
%%                                         default_page_size, max_page_size
%%     code_precedence(Op, [Error, ...]).  Op in add_principal, revoke_key,
%%                                         request_action, approve, reject
%%   extracted/tla_facts.pl:
%%     tla_guard_order(Op, [Error, ...]).  from GuardOrder in ApprovalCore.tla
%%   extracted/api_facts.pl:
%%     api_method(Name).                   wasm function exports that are #[near] methods
%%
%% Paths are relative to the prolog/ directory, found from the working directory
%% (run-prolog.sh runs from prolog/tests/).

:- module(consistency, [
    c_check/2,
    c_ids/1,
    prolog_root/1,
    status_toml/2
]).

:- use_module(library(lists)).
:- use_module(library(iso_ext)).
:- use_module(library(between)).
:- use_module(library(pairs)).
:- use_module(library(ordsets)).
:- use_module(library(dcgs)).
:- use_module(library(pio)).
:- use_module(library(files)).
:- use_module(library(format)).
:- use_module('../requirements/approval_req').
:- use_module('../requirements/threat_model').
:- use_module('../requirements/traceability').

:- discontiguous(c_check/2).

c_ids(['C-1', 'C-2', 'C-2t', 'C-3', 'C-4', 'C-5', 'C-6', 'C-7', 'C-8', 'C-9', 'C-10']).

%%% ========================================================
%%% Paths and extracted facts
%%% ========================================================

prolog_root(Root) :-
    (   file_exists("requirements/approval_req.pl") -> Root = "."
    ;   file_exists("../requirements/approval_req.pl") -> Root = ".."
    ;   file_exists("projects/near-approval/prolog/requirements/approval_req.pl")
    ->  Root = "projects/near-approval/prolog"
    ;   throw(error(existence_error(directory, prolog_root), consistency))
    ).

root_path(Rel, Path) :-
    prolog_root(Root),
    append(Root, [/ | Rel], Path).

%% extracted(+File, -Terms): the terms of extracted/File, or fails if it does not exist.
extracted(File, Terms) :-
    append("extracted/", File, Rel),
    root_path(Rel, Path),
    file_exists(Path),
    read_terms(Path, Terms).

read_terms(Path, Terms) :-
    setup_call_cleanup(open(Path, read, In),
                       read_all(In, Terms),
                       close(In)).
read_all(In, Terms) :-
    read(In, T),
    (   T == end_of_file -> Terms = []
    ;   Terms = [T | Ts], read_all(In, Ts)
    ).

%%% ========================================================
%%% C-1 Authority matrix
%%% ========================================================

c_check('C-1', Result) :-
    findall(M, method(M, change, _), Ms0), sort(Ms0, Ms),
    findall(M, ( member(M, Ms), findall(A, method(M, change, A), As), length(As, N), N =\= 1 ), Multi),
    findall(A1-A2-M, ( member(A1, [owner, agent, approver]), member(A2, [owner, agent, approver]),
                       A1 @< A2, method(M, change, A1), method(M, change, A2) ), Overlap),
    % "no key can both request and approve": the requesting and deciding methods have
    % different key roles, and D4 gives each key exactly one role.
    (   method(request_action, change, agent), method(approve, change, approver),
        method(reject, change, approver)
    ->  RoleSplit = []
    ;   RoleSplit = [request_and_decide_share_a_role]
    ),
    % D11: no upgrade, ownership transfer, expiry or threshold entry point.
    findall(M, ( method(M, _, _), forbidden_method(M) ), Forbidden),
    append([Multi, Overlap, RoleSplit, Forbidden], Bad),
    (   Bad == []
    ->  length(Ms, NC),
        Result = pass(change_methods(NC))
    ;   Result = fail(Bad)
    ).

forbidden_method(M) :-
    atom_chars(M, Cs),
    member(Sub, ["upgrade", "migrate", "transfer", "set_owner", "expire", "threshold", "deploy"]),
    append(_, T, Cs), append(Sub, _, T), !.

%%% ========================================================
%%% C-2 Guard table, C-2t across models
%%% ========================================================

c_check('C-2', Result) :-
    findall(E, ( approval_error(E), \+ guard(_, _, E, _) ), NoGuard),
    findall(E, ( guard(_, _, E, _), \+ approval_error(E) ), Undeclared0), sort(Undeclared0, Undeclared),
    findall(Op-N, ( guard(Op, N, E1, _), guard(Op, N, E2, _), E1 \== E2 ), Ambig0), sort(Ambig0, Ambig),
    findall(Op-E, ( guard(Op, N1, E, _), guard(Op, N2, E, _), N1 \== N2 ), Dup0), sort(Dup0, Dup),
    findall(Op, ( core_op(Op), \+ contiguous_orders(Op) ), Gaps),
    append([NoGuard, Undeclared, Ambig, Dup, Gaps], Bad),
    (   Bad \== [] -> Result = fail(spec(Bad))
    ;   extracted("code_facts.pl", Terms)
    ->  precedence_diff(Terms, code_precedence, Diff),
        (   Diff == [] -> Result = pass(spec_and_code_agree) ; Result = fail(code_precedence(Diff)) )
    ;   Result = pending(decision_extraction, "guard table well formed; code_precedence/2 pending extraction (extracted/code_facts.pl)")
    ).

c_check('C-2t', Result) :-
    (   extracted("code_facts.pl", CT), extracted("tla_facts.pl", TT)
    ->  precedence_diff(CT, code_precedence, D1),
        precedence_diff(TT, tla_guard_order, D2),
        append(D1, D2, D),
        (   D == [] -> Result = pass(three_way_agree) ; Result = fail(D) )
    ;   Result = pending(decision_extraction, "needs extracted/code_facts.pl and extracted/tla_facts.pl")
    ).

contiguous_orders(Op) :-
    findall(N, guard(Op, N, _, _), Ns0), sort(Ns0, Ns),
    length(Ns0, Len), numlist(1, Len, Ns).

%% precedence_diff(+Terms, +Functor, -Diff): ops whose extracted order differs.
%% The code's order is observed (kani/src/facts.rs): code_before(Op, E1, E2)
%% says E1 won when both guards held. Guards never seen failing together
%% may come in either order, so when code_before/3 facts are present the
%% spec order need only agree with every observed pair, and use the same
%% guards.
precedence_diff(Terms, F, Diff) :-
    findall(Op-spec(Spec)-got(Got),
            ( core_op(Op), guard_sequence(Op, Spec),
              ( T =.. [F, Op, Got], memberchk(T, Terms) -> \+ agrees(F, Terms, Op, Spec, Got) ; Got = missing ) ),
            Diff).

agrees(_, _, _, Spec, Spec) :- !.
agrees(code_precedence, Terms, Op, Spec, Got) :-
    memberchk(code_before(_, _, _), Terms),
    msort(Spec, S1), msort(Got, S1),
    \+ ( member(code_before(Op, E1, E2), Terms),
          nth0(I1, Spec, E1), nth0(I2, Spec, E2), I1 > I2 ).

%%% ========================================================
%%% C-3 Error messages distinct and substring-free (R-2)
%%% ========================================================

c_check('C-3', Result) :-
    findall(E-M, error_message(E, M), Stated),
    findall(E, ( approval_error(E), \+ error_message(E, _) ), Unstated),
    (   substring_clash(Stated, Clash), Clash \== []
    ->  Result = fail(stated(Clash))
    ;   extracted("code_facts.pl", Terms)
    ->  findall(E-M, member(code_error(E, M), Terms), Code),
        findall(E, ( approval_error(E), \+ memberchk(code_error(E, _), Terms) ), Missing),
        findall(E-stated(M)-code(MC), ( member(E-M, Stated), memberchk(code_error(E, MC), Terms), MC \== M ), Mismatch),
        substring_clash(Code, CodeClash),
        append([Missing, Mismatch, CodeClash], Bad),
        (   Bad == [] -> Result = pass(code_messages_distinct) ; Result = fail(Bad) )
    ;   length(Stated, NS), length(Unstated, NU),
        Result = pending(error_messages, stated_ok_unstated(NS, NU))
    ).

substring_clash(Msgs, Clash) :-
    findall(E1-E2, ( member(E1-M1, Msgs), member(E2-M2, Msgs), E1 \== E2,
                     ( M1 == M2 ; append(_, T, M2), append(M1, _, T) ) ), Clash).

%%% ========================================================
%%% C-4 Events
%%% ========================================================

c_check('C-4', Result) :-
    findall(Ev, emits(_, Ev), Evs0), sort(Evs0, Evs),
    % AMBIGUOUS (decision 'C-4-key_added'): "each event comes from exactly one method"
    % is checked per core operation, since add_agent and add_approver both emit key_added.
    findall(Ev-Ops, ( member(Ev, Evs),
                      findall(Op, ( emits(M, Ev), method_op(M, Op) ), Ops0), sort(Ops0, Ops),
                      length(Ops, N), N =\= 1 ), MultiSource),
    findall(M, ( changes(M, W), W \== none, \+ emits(M, _), \+ accepted_risk(method(M), _) ), Silent),
    findall(M, ( emits(M, _), \+ method(M, change, _) ), EmitsFromNonChange),
    append([MultiSource, Silent, EmitsFromNonChange], Bad),
    (   Bad == [] -> length(Evs, NE), Result = pass(events(NE))
    ;   Result = fail(Bad)
    ).

%%% ========================================================
%%% C-5 Constants
%%% ========================================================

c_check('C-5', Result) :-
    constant(default_page_size, DPG), constant(max_page_size, PG),
    constant(max_pending_per_key, MAXP), constant(max_action_len, N),
    constant(action_len_log_bound, NB),
    constant(worst_case_event_bytes, WC), constant(max_total_log_length, LogMax),
    findall(F, ( member(F-G, [dpg_le_pg-(DPG =< PG), maxp_ge_1-(MAXP >= 1),
                              n_within_res2-(N =< NB), worst_event_fits_log-(WC =< LogMax),
                              n_ge_1-(N >= 1)]),
                 \+ call(G) ), Bad),
    (   Bad \== [] -> Result = fail(Bad)
    ;   extracted("code_facts.pl", Terms)
    ->  findall(C-spec(V)-code(VC),
                ( member(C, [max_action_len, max_pending_per_key, default_page_size, max_page_size]),
                  constant(C, V),
                  ( memberchk(code_constant(C, VC), Terms) -> VC =\= V ; VC = missing ) ), Diff),
        (   Diff == [] -> Result = pass(spec_and_code_agree) ; Result = fail(Diff) )
    ;   Result = pending(decision_extraction, "requirement constants consistent; generated constants pending extraction")
    ).

%%% ========================================================
%%% C-6 API surface (pending M3, decision 'C-6')
%%% ========================================================

c_check('C-6', Result) :-
    (   extracted("api_facts.pl", Terms)
    ->  findall(M, member(api_method(M), Terms), Api0), sort(Api0, Api),
        findall(M, method(M, _, _), Spec0), sort(Spec0, Spec),
        ord_subtract(Api, Spec, Extra), ord_subtract(Spec, Api, Missing),
        (   Extra == [], Missing == [] -> Result = pass(api_equal)
        ;   Result = fail(extra(Extra)-missing(Missing))
        )
    ;   Result = pending('C-6', "pending M3: extracted/api_facts.pl not generated yet")
    ).

%%% ========================================================
%%% C-7 Traceability both ways
%%% ========================================================

c_check('C-7', Result) :-
    findall(R, ( requirement(R, _), \+ verified_by(R, _) ), Unmapped),
    findall(P, ( property(P, _, _), \+ verified_by(_, P), \+ mitigated_by(_, P) ), Orphans),
    findall(R-P, ( verified_by(R, P), \+ property(P, _, _) ), Dangling0), sort(Dangling0, Dangling),
    findall(R, ( verified_by(R, _), \+ requirement(R, _) ), NoReq0), sort(NoReq0, NoReq),
    append([Unmapped, Orphans, Dangling, NoReq], Bad),
    (   Bad == []
    ->  findall(R, requirement(R, _), Rs), length(Rs, NR),
        findall(P, property(P, _, _), Ps), length(Ps, NP),
        Result = pass(requirements(NR)-properties(NP))
    ;   Result = fail(unmapped(Unmapped)-orphans(Orphans)-dangling(Dangling)-unknown_req(NoReq))
    ).

%%% ========================================================
%%% C-8 Threats covered
%%% ========================================================

c_check('C-8', Result) :-
    findall(T, ( threat(T, _, _), \+ mitigated_by(T, _), \+ accepted_risk(T, _) ), Uncovered),
    findall(T-X, ( mitigated_by(T, X), \+ property(X, _, _), \+ assumption(X, _, _) ), Dangling),
    findall(T, ( threat(T, _, Res), Res \== none, \+ accepted_risk(T, _), \+ residual_mitigated(Res) ), Unaccepted),
    append([Uncovered, Dangling, Unaccepted], Bad),
    (   Bad == [] -> findall(T, threat(T, _, _), Ts), length(Ts, N), Result = pass(threats(N))
    ;   Result = fail(Bad)
    ).

% Residuals that are not a risk but a condition already covered by a property.
residual_mitigated("none, if verifiers follow VER-1").

%%% ========================================================
%%% C-9 IDs in status.toml = IDs here
%%% ========================================================

c_check('C-9', Result) :-
    status_toml(Props, Asms),
    findall(Id, member(prop(Id, _, _, _), Props), TP0), sort(TP0, TP),
    findall(Id, ( property(Id, _, _), \+ status_pending_id(Id) ), PP0), sort(PP0, PP),
    ord_subtract(TP, PP, MissingHere), ord_subtract(PP, TP, MissingInToml),
    findall(Id, member(asm(Id, _, _, _), Asms), TA0), sort(TA0, TA),
    findall(Id, assumption(Id, _, _), PA0), sort(PA0, PA),
    ord_subtract(TA, PA, AsmMissingHere), ord_subtract(PA, TA, AsmMissingInToml),
    findall(Id-toml(L1)-here(L2), ( member(asm(Id, L1, _, _), Asms), assumption(Id, _, L2), L1 \== L2 ), LevelDiff),
    findall(Id-toml(L1)-here(L2), ( member(prop(Id, L1, _, _), Props), property(Id, L2, _), L1 \== L2 ), LayerDiff),
    findall(Id, ( status_pending_id(Id), memberchk(prop(Id, _, _, _), Props) ), StalePending),
    Bad = [props_missing_here(MissingHere), props_missing_in_toml(MissingInToml),
           asms_missing_here(AsmMissingHere), asms_missing_in_toml(AsmMissingInToml),
           level_diff(LevelDiff), layer_diff(LayerDiff), pending_but_present(StalePending)],
    (   forall(member(B, Bad), arg(1, B, []))
    ->  findall(Id, status_pending_id(Id), Pend),
        length(TP, NP), length(TA, NA),
        (   Pend == []
        ->  Result = pass(properties(NP)-assumptions(NA))
        ;   Result = pending('C-9-new-ids', not_yet_in_status_toml(Pend))
        )
    ;   findall(B, ( member(B, Bad), \+ empty_arg(B) ), Bad1),
        Result = fail(Bad1)
    ).

empty_arg(T) :- arg(1, T, []).

%%% ========================================================
%%% C-10 verified* properties on weak, unchecked assumptions (warning check)
%%% ========================================================

c_check('C-10', Result) :-
    status_toml(Props, _),
    findall(warn(P, A),
            ( member(prop(P, _, St, PAs), Props), verified_status(St),
              member(A, PAs), assumption(A, _, Lvl),
              level_rank(Lvl, R), level_rank(high, RH), R < RH,
              \+ assumption_checked(A, Props) ),
            Warnings),
    (   Warnings == [] -> Result = pass(no_warnings)
    ;   Result = pass(warnings(Warnings))       % C-10 warns; it does not fail
    ).

verified_status(verified).
verified_status('verified-with-assumptions').

assumption_checked(A, Props) :-
    findall(C, assumption_checked_by(A, C), Cs),
    Cs \== [],
    forall(member(C, Cs), ( member(prop(C, _, St, _), Props), verified_status(St) )).

%%% ========================================================
%%% Minimal status.toml reader (line based; the file uses one inline table per
%%% property line and one [assumptions.ID] table per assumption)
%%% ========================================================

%% status_toml(-Props, -Asms)
%%   Props = [prop(Id, Layer, Status, Assumptions)], Asms = [asm(Id, Level, Status, CheckedBy)]
status_toml(Props, Asms) :-
    prolog_root(Root),
    append(Root, "/../status.toml", Path),
    phrase_from_file(seq(Cs), Path),
    split_lines(Cs, Lines),
    parse_lines(Lines, none, Props, Asms0),
    finish_asms(Asms0, Asms).

split_lines([], []).
split_lines(Cs, [L | Ls]) :-
    Cs \== [],
    (   append(L, ['\n' | Rest], Cs) -> true ; L = Cs, Rest = [] ),
    split_lines(Rest, Ls).

parse_lines([], _, [], []).
parse_lines([L0 | Ls], Sect0, Props, Asms) :-
    strip_left(L0, L),
    (   L = ['[' | _]
    ->  section(L, Sect), Props = Props1, Asms = Asms1
    ;   Sect = Sect0,
        line_item(Sect0, L, Props, Props1, Asms, Asms1)
    ),
    parse_lines(Ls, Sect, Props1, Asms1).

section(L, asm(Id)) :- append("[assumptions.", T, L), append(IdCs, [']' | _], T), !, atom_chars(Id, IdCs).
section(L, props) :- append("[modules.", _, L), append(_, ".properties]", L), !.
section(_, other).

line_item(asm(Id), L, Ps, Ps, [kv(Id, K, V) | As], As) :-
    member(K-Key, [level-"level", status-"status"]),
    quoted_value(Key, L, V), !.
line_item(asm(Id), L, Ps, Ps, [kv(Id, checked_by, V) | As], As) :-
    list_value("checked_by", L, V), !.
line_item(props, L, [prop(Id, Layer, Status, PAs) | Ps], Ps, As, As) :-
    append(IdCs, [' ', '=', ' ', '{' | Rest], L),
    IdCs = [C0 | _], C0 @>= 'A', C0 @=< 'Z', !,
    atom_chars(Id, IdCs),
    ( quoted_value("layer", Rest, Layer) -> true ; Layer = none ),
    ( quoted_value("status", Rest, Status) -> true ; Status = none ),
    ( list_value("assumptions", Rest, PAs) -> true ; PAs = [] ).
line_item(_, _, Ps, Ps, As, As).

finish_asms(KVs, Asms) :-
    findall(Id, member(kv(Id, _, _), KVs), Ids0), sort(Ids0, Ids),
    findall(asm(Id, Lvl, St, Cb),
            ( member(Id, Ids),
              ( memberchk(kv(Id, level, Lvl), KVs) -> true ; Lvl = none ),
              ( memberchk(kv(Id, status, St), KVs) -> true ; St = none ),
              ( memberchk(kv(Id, checked_by, Cb), KVs) -> true ; Cb = [] ) ),
            Asms).

strip_left([C | Cs], L) :- ( C == ' ' ; C == '\t' ), !, strip_left(Cs, L).
strip_left(L, L).

quoted_value(Key, L, V) :-
    append(_, T, L), append(Key, [' ', '=', ' ', '"' | A], T), !,
    append(VCs, ['"' | _], A), !,
    atom_chars(V, VCs).

list_value(Key, L, Items) :-
    append(_, T, L), append(Key, [' ', '=', ' ', '[' | A], T), !,
    append(Inner, [']' | _], A), !,
    quoted_items(Inner, Items).

quoted_items(Cs, Items) :-
    (   append(_, ['"' | A], Cs)
    ->  append(ItemCs, ['"' | Rest], A), !,
        atom_chars(Item, ItemCs),
        Items = [Item | Items1],
        quoted_items(Rest, Items1)
    ;   Items = []
    ).
