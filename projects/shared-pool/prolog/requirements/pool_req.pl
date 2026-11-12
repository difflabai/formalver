%% pool_req.pl -- Requirements of shared-pool-controls, transcribed from the upstream docs
%%
%% PROP: C-1 C-2 C-3 C-4 C-5 C-6
%%
%% Sources (pin a4bb5c3, source-mirror/docs/):
%%   spec.md                    cited as spec:<line>
%%   api.md                     cited as api:<line>
%%   verification-handoff.md    cited as handoff:<line>
%% Every fact carries the line it was transcribed from. Where the docs are
%% silent the fact says so: Basis code_only(Why) means the docs give no
%% condition, name or position, and the code's choice is recorded so that
%% the check can still be exact (and so the gap is visible: C-2 and C-3 count
%% them). doc_condition(Cite) means the docs state the condition but not the
%% error name or the position. Readings the text leaves open are AMBIGUOUS;
%% places where the docs and the code disagree are divergence/4 facts.
%%
%% INDEPENDENCE NOTE (ASM-SPEC). Unlike near-approval's M4, the author of this
%% layer had read the code (the shared brief transcribes it). Doc-backed facts
%% are cited to the doc line that states them; nothing marked doc(_) relies on
%% the code. The code-only facts are the code's choices and are labelled.
%%
%% Exported:
%%   requirement(Id, Cite, Text)
%%   method(Name, Kind, Authority, Cite)        Kind: init | view | change | callback
%%       Authority: self | anyone | actor | executor | actor_or_owner | owner
%%   method_core(Method, CoreFn)                the core transition a method drives
%%   guard(OpKind, Order, GuardId, Outcome, Basis)
%%       Outcome = err(Error) | noop (Ok, nothing changes); the first guard whose
%%       condition fails decides; if none fails the effect applies
%%   guard_sequence(OpKind, [Outcome..]), guard_ids(OpKind, [GuardId..])
%%   op_kind(OpKind)
%%   pool_error(Error, Cite)                    error names the docs use
%%   life(OpClass, Flag, From, Outcome, Basis)  lifecycle table (Outcome to(S) | same | reject)
%%   status(S), terminal(S), open_status(S)
%%   constant(Name, Value, Cite)
%%   fixture(Name, TraceId, Cite), fixture_metric(Fixture, Name, Index, Basis)
%%   fixture_claim(ClaimId, Fixture, Claim, Cite)
%%   known_finding(ClaimId, FindingId)          a claim the code is known to break:
%%                                              C-5 must REPRODUCE the counterexample
%%   finding(Id, Severity, Cite, Text)          the confirmed findings (brief F-1..F-6)
%%   divergence(Id, Cite, DocSays, CodeDoes)    spec-vs-code disagreements (findings)
%%   ambiguity(Id, Cite, Text, Reading)
%%   decision(Id, Text)

:- module(pool_req, [
    requirement/3,
    method/4,
    method_core/2,
    guard/5,
    guard_sequence/2,
    guard_ids/2,
    op_kind/1,
    pool_error/2,
    life/5,
    status/1,
    terminal/1,
    open_status/1,
    constant/3,
    fixture/3,
    fixture_metric/4,
    fixture_claim/4,
    known_finding/2,
    finding/4,
    divergence/4,
    ambiguity/4,
    decision/2,
    camel_snake/2
]).

:- use_module(library(lists)).
:- use_module(library(pairs)).

%%% ========================================================
%%% Requirements (one per doc statement that a check or property relies on)
%%% ========================================================

% spec.md, State and identity
requirement('S-STATE', 'spec:7', "Pool = (config, values, version, observed_at, paused, records).").
requirement('S-CONFIG', 'spec:9', "Config is immutable: one owner, bounded named metrics, potential terms and recipes; each recipe has one exact actor, one exact executor, reservation and completion effects, a maximum quantity and earlier-recipe completion prerequisites (recipe_id, minimum_completed_units); the dependency order is acyclic by construction.").
requirement('S-INIT', 'spec:11', "Both initializers are private to their own deployment account.").
requirement('S-PRED', 'spec:11', "The wrapper authorizes by immediate predecessor account, not a JSON actor field and not signer_account_id; calls through an intermediary are attributed to that intermediary.").
requirement('S-PREVIEW-NOAUTH', 'spec:11', "Preview accepts a proposed actor but conveys no authorization.").
requirement('S-NUM', 'spec:13', "Metric values and coefficients lie in [-1,000,000, 1,000,000]; every update is checked; each term's residual is at most 2,000,000 and weight at most 1,000; up to 64 terms sum to at most 256,000,000,000,000,000, below u64::MAX.").
requirement('S-SERIAL', 'spec:13', "Energy is serialized as a decimal string; all exposed metric integers are within JavaScript's exact range.").
requirement('S-EXPIRY', 'spec:13', "Request expiry is an epoch-seconds value.").
% spec.md, Admission
requirement('S-ADM-ORDER', 'spec:19', "Admission checks paused, version equality, expiry strictly after now and at most one day ahead, observation freshness if configured, record bound, recipe validity, exact caller, quantity range, and completed-unit prerequisites.").
requirement('S-ADM-CANDIDATE', 'spec:19', "Candidate values = values + reservation delta * units, with checked arithmetic.").
requirement('S-ADM-HARD', 'spec:21', "A conservative per-metric interval contains every subset of outstanding completion effects plus the proposed completion; healthy state: all intervals fit the hard bounds; disturbed state: no metric's violation amount exceeds its current violation.").
requirement('S-ADM-ENERGY', 'spec:23', "Require V(candidate) <= V(current); in a state already violating hard bounds also require V(candidate + proposed_completion) < V(current).").
requirement('S-ADM-RECOVERY-SCOPE', 'spec:23', "The recovery rule is an admission rule only; it does not guarantee that execution arrives or recovery completes.").
requirement('S-ADM-EFFECT', 'spec:25', "On success append a Reserved record, replace values, increment version; on rejection return an error with no state change.").
requirement('S-ADM-NOREPLAY', 'spec:25', "Accepted requests cannot replay at the original version; there is no separate client nonce mechanism.").
requirement('S-ADM-WRAPPER', 'spec:25', "The wrapper may emit a rejection event but does not consume a nonce or persist an audit record.").
requirement('S-PREVIEW', 'spec:27', "preview calls the same checker and returns candidate values, score terms and reason; it is advisory.").
requirement('S-BEST', 'spec:27', "best_quantity enumerates positive quantities up to the requested maximum, minimizes energy then favors larger quantity; it only suggests.").
% spec.md, Potential
requirement('S-POTENTIAL', 'spec:31', "Each term references one metric and computes a weighted squared target deviation, excess or deficit; agents cannot supply deltas or invent targets.").
requirement('S-HARD-AXIS', 'spec:33', "Hard constraints are axis-aligned metric bounds.").
% spec.md, Lifecycle
requirement('S-LIFE-DISPATCH', 'spec:37', "Reserved -> Dispatched: exact actor, unpaused, unexpired, fresh risk snapshot; the wrapper creates the promise after the state update.").
requirement('S-LIFE-ACTIVE', 'spec:38', "Dispatched/Unknown -> Active: private acknowledgment says the adapter accepted dispatch.").
requirement('S-LIFE-UNKNOWN', 'spec:39', "Dispatched/Unknown -> Unknown: missing, malformed or failed acknowledgment; retain values.").
requirement('S-LIFE-COMPLETE', 'spec:40', "Dispatched/Active/Unknown -> Completed: the recipe executor attests completion; add completion delta, check remaining completion envelope, increment version; no energy comparison.").
requirement('S-LIFE-CANCEL', 'spec:41', "Reserved -> Cancelled: actor or owner cancels before dispatch; subtract reservation delta and check other pending effects.").
requirement('S-LIFE-NONEXEC', 'spec:42', "Dispatched/Active/Unknown -> Cancelled: executor attests definitive nonexecution; same checked inverse update.").
requirement('S-LIFE-IDEMPOTENT', 'spec:43', "Same completion/cancellation repeated: idempotent; conflicting terminal evidence: reject.").
requirement('S-LIFE-LATEACK', 'spec:44', "Late acknowledgment after terminal settlement: ignored.").
requirement('S-INVERSE', 'spec:46', "A checked inverse can fail if another commitment depends on its contribution; the commitment remains encumbered; resolve dependent work first; no forced administrative release.").
requirement('S-FIXTURE-RELIANCE', 'spec:46', "In the supplied fixtures, physical availability and risk-credit timing prevent ordinary unsafe reliance on unexecuted work.").
requirement('S-NOEXPIRY', 'spec:48', "No automatic expiry of a dispatched request; reconciliation queries the fixed executor by immutable id; Unknown is distinct from cancelled.").
requirement('S-ADAPTER', 'spec:50', "The mock adapter binds id to recipe/quantity, dedupes identical dispatch, rejects a different payload; only the lock executes; only the operator finishes/cancels; it stores terminal evidence before notifying the lock.").
% spec.md, External observations and administration
requirement('S-PAUSE', 'spec:54', "set_paused is owner-only and increments version; pausing blocks new admissions and dispatch, not settlement or reconciliation.").
requirement('S-OBSERVE', 'spec:54', "observe is owner-only and allowed only when every record is terminal; it replaces bounded measured values and refreshes the snapshot timestamp without changing policy or deleting history; it can create a hard-limit violation.").
requirement('S-NOADMIN', 'spec:56', "No policy upgrades, role mutation, arbitrary funds transfer, dynamic plugins, or reset entry point.").
% spec.md, Scenario semantics
requirement('S-GPU', 'spec:60', "GPU/Friday: coverage and occupancy include reserved and completed bookings; completion does not free historical slots; Friday also consumes dispatch slots atomically.").
requirement('S-STOCK', 'spec:62', "Inventory: positions move at reservation; source availability decreases and transit increases at reservation; receipt moves transit into destination availability; incoming position is never available stock; available_depot + available_A + available_B + transit = 12 across ordinary transfer transitions.").
requirement('S-CASH', 'spec:64', "Hiring: reservation consumes funds or earmark and increases coverage plus escrow; acceptance moves escrow to paid; coverage remains after payment; free + earmark + escrow + paid + protected = 10; review needs completed research >= 2 and implementation >= 3; no worker can authorize its own acceptance.").
requirement('S-RISK', 'spec:66', "Risk: positive loss contributions reserve immediately; hedge benefit occurs only on completion; collateral encumbrance remains until a later measured baseline; no pending hedge offsets are netted into new trade capacity.").
% api.md
requirement('A-NONPAYABLE', 'api:3', "All mutating methods are nonpayable.").
requirement('A-METHODS', 'api:5-18', "The method table: names, arguments and authority of new, get_pool, get_commitments, preview, submit, dispatch, reconcile, settle, cancel, set_paused, observe, on_result.").
requirement('A-PAGE', 'api:9', "get_commitments reads a page of at most 50.").
requirement('A-SUBMIT-RESULT', 'api:11', "submit returns {decision,id}; no id on rejection.").
requirement('A-VERSION', 'api:26', "Every successful state transition changes version; terminal duplicate settlement is idempotent.").
requirement('A-EXPIRY-MAX', 'api:26', "Maximum expiry is 24 hours ahead.").
requirement('A-REASONS', 'api:28', "Reasons include Unauthorized, Paused, Stale, Expired, SnapshotExpired, InvalidRecipe, InvalidUnits, Prerequisite, Full, Arithmetic, Bounds, Energy.").
requirement('A-AFTER', 'api:28', "after can be present for a rejected request to explain its prospective score; it is not accepted state.").
requirement('A-EXECUTOR', 'api:34', "execute({id,recipe,units}) -> active | cancelled | unknown, only the lock may call; status({id}) also returns completed; runtime failures and unexpected strings become Unknown in the wrapper.").
% verification-handoff.md obligations (handoff:11-23) and nuances (handoff:29-34)
requirement('H-CFG', 'handoff:11', "Accepted configuration references are valid and all loops/data are bounded.").
requirement('H-NUM', 'handoff:12', "Valid bounded state/terms cannot overflow energy; all delta overflows fail closed.").
requirement('H-AUTH', 'handoff:13', "Only the recipe actor admits/dispatches, executor settles, owner observes/pauses.").
requirement('H-ADM', 'handoff:14', "Accepted reservation has nonincreasing potential; hard-violation envelopes do not worsen.").
requirement('H-ATOM', 'handoff:15', "All rejected core mutations preserve the full state.").
requirement('H-STALE', 'handoff:16', "A request computed at a prior accepted version cannot replay.").
requirement('H-ASYNC', 'handoff:17', "Unknown outcomes retain reservation until authoritative terminal evidence.").
requirement('H-TERM', 'handoff:18', "Terminal repeated evidence is idempotent; conflicting outcome cannot apply.").
requirement('H-DEP', 'handoff:19', "Prerequisite requires completed units, not acknowledgment or partial completion.").
requirement('H-BIND', 'handoff:20', "Each dispatch id fixes actor, recipe, units and executor.").
requirement('H-STOCK', 'handoff:21', "Inventory fixture conserves available + transit and never spends inbound pipeline.").
requirement('H-CASH', 'handoff:22', "Hiring fixture conserves free + earmark + escrow + paid + protected; payment preserves coverage.").
requirement('H-RISK', 'handoff:23', "Pending negative exposure does not grant new risk headroom.").
requirement('H-INTERVAL', 'handoff:30', "Hard checks use intervals over independent subsets of completion effects; they should never underapproximate the modeled independent effects.").
requirement('H-LIVENESS', 'handoff:31', "A rejected checked inverse leaves liability intact; liveness is conditional on resolving dependencies and receiving authoritative evidence.").
requirement('H-NOMONO', 'handoff:33', "Energy is not checked on lifecycle reversal or observation.").
requirement('H-VERSION', 'handoff:34', "Version overflow is an explicit rejection; 256 lifetime records bound growth; pause/observe still advance version.").

%%% ========================================================
%%% Methods and authority (api.md table, spec:11)
%%% ========================================================

method(new,             init,     self,           'api:7 + spec:11').
method(get_pool,        view,     anyone,         'api:8').
method(get_commitments, view,     anyone,         'api:9').
method(preview,         view,     anyone,         'api:10 + spec:11').   % actor is hypothetical
method(submit,          change,   actor,          'api:11').
method(dispatch,        change,   actor,          'api:12 + spec:37').
method(reconcile,       change,   anyone,         'api:13').
method(settle,          change,   executor,       'api:14 + spec:40,42').
method(cancel,          change,   actor_or_owner, 'api:15 + spec:41').
method(set_paused,      change,   owner,          'api:16 + spec:54').
method(observe,         change,   owner,          'api:17 + spec:54').
method(on_result,       callback, self,           'api:18').
% AMBIGUOUS (amb-reconcile-kind): api:13 makes reconcile callable by anyone; it
% changes nothing itself (the private callback applies the result). Recorded as
% kind change with authority anyone; C-1 checks the code grants it no authority.

% The core transition each method drives (api:11-18; spec:37-44). A method may
% drive several (on_result: settle or acknowledge, api:34 + spec:38-42).
method_core(submit,     submit).
method_core(dispatch,   dispatch).
method_core(settle,     settle).
method_core(cancel,     cancel).
method_core(set_paused, set_paused).
method_core(observe,    observe).
method_core(on_result,  settle).
method_core(on_result,  acknowledge).
method_core(preview,    preview).

%%% ========================================================
%%% Errors the docs name (api:28 lists submit's reasons)
%%% ========================================================

pool_error('Unauthorized',    'api:28').
pool_error('Paused',          'api:28').
pool_error('Stale',           'api:28').
pool_error('Expired',         'api:28').
pool_error('SnapshotExpired', 'api:28').
pool_error('InvalidRecipe',   'api:28').
pool_error('InvalidUnits',    'api:28').
pool_error('Prerequisite',    'api:28').
pool_error('Full',            'api:28').
pool_error('Arithmetic',      'api:28').
pool_error('Bounds',          'api:28').
pool_error('Energy',          'api:28').
% The docs name no error for lifecycle calls. InvalidState, NotFound, Pending
% (and InvalidConfig for `new`) are code-only names; see guard/5 below.

%%% ========================================================
%%% Guard tables
%%% ========================================================
%% Op kinds: submit, dispatch, ack (acknowledge), cancel, settle_completed,
%% settle_cancelled (settle(_, _, true|false)), pause (set_paused), observe.

op_kind(submit).
op_kind(dispatch).
op_kind(ack).
op_kind(cancel).
op_kind(settle_completed).
op_kind(settle_cancelled).
op_kind(pause).
op_kind(observe).

% --- submit (spec:17-25, api:26-28)
guard(submit,  1, paused,        err('Paused'),          doc('spec:19 "Check paused"')).
guard(submit,  2, version,       err('Stale'),           doc('spec:19 "version equality"; api:26')).
guard(submit,  3, expiry,        err('Expired'),         doc('spec:19 "expiry strictly after now and at most one day ahead"')).
guard(submit,  4, freshness,     err('SnapshotExpired'), doc('spec:19 "observation freshness if configured"')).
guard(submit,  5, record_bound,  err('Full'),            doc('spec:19 "record bound"; api:8 "up to 256 records"')).
guard(submit,  6, recipe,        err('InvalidRecipe'),   doc('spec:19 "recipe validity"')).
guard(submit,  7, caller,        err('Unauthorized'),    doc('spec:19 "exact caller"; api:11')).
guard(submit,  8, units,         err('InvalidUnits'),    doc('spec:19 "quantity range"')).
guard(submit,  9, prerequisites, err('Prerequisite'),    doc('spec:19 "completed-unit prerequisites"')).
guard(submit, 10, reserve_arith, err('Arithmetic'),      doc('spec:19 "with checked arithmetic"')).
guard(submit, 11, envelope_arith, err('Arithmetic'),     doc_condition('spec:13 "Every update is checked"; spec:21 interval')).
guard(submit, 12, bounds,        err('Bounds'),          doc('spec:21')).
guard(submit, 13, energy,        err('Energy'),          doc('spec:23 "Then require V(candidate) <= V(current)"')).
guard(submit, 14, recovery,      err('Energy'),          doc_condition('spec:23 second sentence; the error name is not stated')).
guard(submit, 15, version_overflow, err('Arithmetic'),   doc_condition('handoff:34 "Version overflow is an explicit rejection"; position code-only (after every admission check)')).

% --- dispatch (spec:37, api:12)
guard(dispatch, 1, found,      err('NotFound'),        code_only('docs name no lookup failure')).
guard(dispatch, 2, caller,     err('Unauthorized'),    doc('spec:37 "exact actor"; api:12')).
guard(dispatch, 3, paused,     err('Paused'),          doc('spec:37 "unpaused"; spec:54')).
guard(dispatch, 4, reserved,   err('InvalidState'),    doc_condition('spec:37 source state Reserved; name and position code-only')).
guard(dispatch, 5, unexpired,  err('Expired'),         doc('spec:37 "unexpired"')).
guard(dispatch, 6, freshness,  err('SnapshotExpired'), doc('spec:37 "fresh risk snapshot"')).
guard(dispatch, 7, version_overflow, err('Arithmetic'), doc_condition('handoff:34')).

% --- acknowledge (spec:38-39, 44; private callback api:18)
guard(ack, 1, found,            err('NotFound'),   code_only('docs name no lookup failure')).
guard(ack, 2, awaiting,         noop,              doc('spec:38-39 sources Dispatched/Unknown; spec:44 late ack ignored (other sources: code-only)')).
guard(ack, 3, changes_status,   noop,              code_only('Unknown->Unknown and a repeated Active are Ok without a version bump: see divergence div-ack-noop-version')).
guard(ack, 4, version_overflow, err('Arithmetic'), doc_condition('handoff:34')).

% --- cancel (spec:41, 43, api:15)
guard(cancel, 1, found,            err('NotFound'),     code_only('docs name no lookup failure')).
guard(cancel, 2, caller,           err('Unauthorized'), doc('spec:41 "actor or owner"; api:15')).
guard(cancel, 3, not_cancelled,    noop,                doc('spec:43 "Same ... cancellation repeated: idempotent"')).
guard(cancel, 4, reserved,         err('Pending'),      doc_condition('api:15 "only undispatched Reserved records"; the name Pending is code-only')).
guard(cancel, 5, release_arith,    err('Arithmetic'),   doc('spec:41 "Subtract reservation delta"; spec:13 checked')).
guard(cancel, 6, envelope_arith,   err('Arithmetic'),   doc_condition('spec:13 "Every update is checked"')).
guard(cancel, 7, bounds,           err('Bounds'),       doc('spec:41 "check other pending effects"; spec:46')).
guard(cancel, 8, version_overflow, err('Arithmetic'),   doc_condition('handoff:34')).

% --- settle (spec:40, 42, 43, api:14)
guard(settle_completed, 1, found,          err('NotFound'),     code_only('docs name no lookup failure')).
guard(settle_completed, 2, caller,         err('Unauthorized'), doc('spec:40 "recipe executor"; api:14')).
guard(settle_completed, 3, not_same_terminal, noop,             doc('spec:43 "Same completion ... repeated: idempotent"')).
guard(settle_completed, 4, in_flight,      err('InvalidState'), doc_condition('spec:40 sources Dispatched/Active/Unknown; spec:43 conflicting terminal: reject; name code-only')).
guard(settle_completed, 5, complete_arith, err('Arithmetic'),   doc('spec:40 "add completion delta"; spec:13 checked')).
guard(settle_completed, 6, envelope_arith, err('Arithmetic'),   doc_condition('spec:13 "Every update is checked"')).
guard(settle_completed, 7, bounds,         err('Bounds'),       doc('spec:40 "check remaining completion envelope"')).
guard(settle_completed, 8, version_overflow, err('Arithmetic'), doc_condition('handoff:34')).

guard(settle_cancelled, 1, found,          err('NotFound'),     code_only('docs name no lookup failure')).
guard(settle_cancelled, 2, caller,         err('Unauthorized'), doc('spec:42 "executor attests"; api:14')).
guard(settle_cancelled, 3, not_same_terminal, noop,             doc('spec:43 "Same ... cancellation repeated: idempotent"')).
guard(settle_cancelled, 4, in_flight,      err('InvalidState'), doc_condition('spec:42 sources Dispatched/Active/Unknown; spec:43 conflicting terminal: reject; name code-only')).
guard(settle_cancelled, 5, release_arith,  err('Arithmetic'),   doc('spec:42 "same checked inverse update"')).
guard(settle_cancelled, 6, envelope_arith, err('Arithmetic'),   doc_condition('spec:13 "Every update is checked"')).
guard(settle_cancelled, 7, bounds,         err('Bounds'),       doc('spec:42 + spec:41 "check other pending effects"')).
guard(settle_cancelled, 8, version_overflow, err('Arithmetic'), doc_condition('handoff:34')).

% --- set_paused (spec:54, api:16)
guard(pause, 1, owner,            err('Unauthorized'), doc('spec:54 "owner-only"; api:16')).
guard(pause, 2, version_overflow, err('Arithmetic'),   doc_condition('handoff:34')).

% --- observe (spec:54, api:17)
guard(observe, 1, owner,            err('Unauthorized'), doc('spec:54 "owner-only"; api:17')).
guard(observe, 2, all_terminal,     err('Pending'),      doc_condition('spec:54 "only when every record is terminal"; api:17; name code-only')).
guard(observe, 3, bounded_values,   err('Bounds'),       doc_condition('spec:54 "replaces bounded measured values"; length check and name code-only')).
guard(observe, 4, version_overflow, err('Arithmetic'),   doc_condition('handoff:34')).
% CODE-ONLY: observe also calls energy(values); with the values bounded (guard 3)
% it cannot fail (NUM-1, spec:13), so it is not a guard here.

%% guard_sequence(+Kind, -Outcomes) / guard_ids(+Kind, -Ids): the specified order.
guard_sequence(Kind, Outcomes) :-
    op_kind(Kind),
    findall(N-O, guard(Kind, N, _, O, _), Ps), keysort(Ps, S), pairs_values(S, Outcomes).
guard_ids(Kind, Ids) :-
    op_kind(Kind),
    findall(N-G, guard(Kind, N, G, _, _), Ps), keysort(Ps, S), pairs_values(S, Ids).

%%% ========================================================
%%% Lifecycle (spec:37-44, api:12-15)
%%% ========================================================
%% life(OpClass, Flag, From, Outcome, Basis): what a call does to the status of
%% the record it names, assuming every non-status guard passes.
%%   Outcome: to(S) the status becomes S (S may equal From: a listed self-loop)
%%            same   Ok and the status (and everything else) is unchanged
%%            reject an error
%%   Flag:    none, or the call's boolean (ack accepted, settle completed)

status(reserved).  status(dispatched).  status(active).
status(unknown).   status(completed).   status(cancelled).
terminal(completed).  terminal(cancelled).
open_status(S) :- status(S), \+ terminal(S).

% dispatch: spec:37 Reserved -> Dispatched; nothing else is listed.
life(dispatch, none, reserved, to(dispatched), doc('spec:37')).
life(dispatch, none, S, reject, doc('spec:37 only Reserved -> Dispatched; api:12')) :-
    status(S), S \== reserved.
% acknowledge
life(ack, true,  dispatched, to(active),  doc('spec:38')).
life(ack, true,  unknown,    to(active),  doc('spec:38')).
life(ack, false, dispatched, to(unknown), doc('spec:39')).
life(ack, false, unknown,    to(unknown), doc('spec:39 (listed as a transition: see div-ack-noop-version)')).
life(ack, F, S, same, doc('spec:44 "Late acknowledgment after terminal settlement: ignored"')) :-
    member(F, [true, false]), terminal(S).
% AMBIGUOUS (amb-ack-other): the docs list no acknowledgment from Reserved or
% Active. on_result runs only after dispatch (api:12-13), so Reserved cannot
% occur through the shell; a repeated "active" from reconcile (api:13) can.
life(ack, F, active,   same, code_only('docs silent: ack of an Active record is ignored')) :- member(F, [true, false]).
life(ack, F, reserved, same, code_only('docs silent: ack of a Reserved record is ignored (unreachable via on_result)')) :- member(F, [true, false]).
% cancel: spec:41, api:15, spec:43
life(cancel, none, reserved,  to(cancelled), doc('spec:41; api:15')).
life(cancel, none, cancelled, same,          doc('spec:43 "Same ... cancellation repeated: idempotent"')).
life(cancel, none, S, reject, doc('api:15 "only undispatched Reserved records"; spec:43 conflicting terminal')) :-
    member(S, [dispatched, active, unknown, completed]).
% settle
life(settle, true,  S, to(completed), doc('spec:40')) :- member(S, [dispatched, active, unknown]).
life(settle, false, S, to(cancelled), doc('spec:42')) :- member(S, [dispatched, active, unknown]).
life(settle, true,  completed, same,  doc('spec:43 idempotent')).
life(settle, false, cancelled, same,  doc('spec:43 idempotent')).
life(settle, true,  cancelled, reject, doc('spec:43 "Conflicting terminal evidence: reject"')).
life(settle, false, completed, reject, doc('spec:43 "Conflicting terminal evidence: reject"')).
life(settle, F, reserved, reject, doc_condition('spec:40,42 list only Dispatched/Active/Unknown sources; api:15 cancel is the pre-dispatch path')) :-
    member(F, [true, false]).

%%% ========================================================
%%% Constants
%%% ========================================================

constant(max_value,         1000000,  'spec:13 "[-1,000,000, 1,000,000]"').
constant(max_residual,      2000000,  'spec:13 "residual of at most 2,000,000"').
constant(max_weight,        1000,     'spec:13 "weight <= 1,000"').
constant(max_terms,         64,       'spec:13 "Up to 64 terms"').
constant(max_energy,        256000000000000000, 'spec:13 "sum to at most 256,000,000,000,000,000"').
constant(u64_max,           18446744073709551615, 'spec:13 "safely below u64::MAX"').
constant(js_exact_max,      9007199254740991, 'spec:13 "JavaScript\'s exact range" (2^53 - 1)').
constant(max_records,       256,      'api:8 "up to 256 records"; handoff:34 "256 lifetime records"').
constant(page_max,          50,       'api:9 "Read page, max 50"').
constant(expiry_horizon,    86400,    'spec:19 "at most one day ahead"; api:26 "Maximum is 24 hours"').
constant(version_max,       4294967295, 'handoff:34 "Version overflow" (the width, u32, is code-only)').
% CODE-ONLY constants (docs silent): MAX_METRICS 32, MAX_RECIPES 32, MAX_UNITS 100,
% name length 128. C-4 lists them as code-only.

%%% ========================================================
%%% Fixtures (spec:58-66, handoff:21-23)
%%% ========================================================
%% The conformance generator emits the fixtures as traces 1-5 in the order of
%% fixtures::NAMES (CODE-ONLY: conformance/src/main.rs, fixtures.rs:47).

fixture(gpu,       1, 'spec:60').
fixture(friday,    2, 'spec:60').
fixture(inventory, 3, 'spec:62; handoff:21').
fixture(hiring,    4, 'spec:64; handoff:22').
fixture(risk,      5, 'spec:66; handoff:23').

% Metric names the docs use -> index in the fixture's metric vector. The docs
% name the metrics; the order is the fixture code's (CODE-ONLY: fixtures.rs).
fixture_metric(inventory, position_depot,  0, code_only('fixtures.rs:137')).
fixture_metric(inventory, position_a,      1, code_only('fixtures.rs:138')).
fixture_metric(inventory, position_b,      2, code_only('fixtures.rs:139')).
fixture_metric(inventory, available_depot, 3, code_only('fixtures.rs:140')).
fixture_metric(inventory, available_a,     4, code_only('fixtures.rs:141')).
fixture_metric(inventory, available_b,     5, code_only('fixtures.rs:142')).
fixture_metric(inventory, transit,         6, code_only('fixtures.rs:143')).
fixture_metric(hiring, coverage_research,       0, code_only('fixtures.rs:177')).
fixture_metric(hiring, coverage_implementation, 1, code_only('fixtures.rs:178')).
fixture_metric(hiring, coverage_review,         2, code_only('fixtures.rs:179')).
fixture_metric(hiring, free,      3, code_only('fixtures.rs:180')).
fixture_metric(hiring, earmark,   4, code_only('fixtures.rs:181')).
fixture_metric(hiring, escrow,    5, code_only('fixtures.rs:182')).
fixture_metric(hiring, paid,      6, code_only('fixtures.rs:183')).
fixture_metric(hiring, protected, 7, code_only('fixtures.rs:184')).
fixture_metric(risk, selloff_loss,    0, code_only('fixtures.rs:219')).
fixture_metric(risk, funding_loss,    1, code_only('fixtures.rs:220')).
fixture_metric(risk, volatility_loss, 2, code_only('fixtures.rs:221')).
fixture_metric(risk, collateral,      3, code_only('fixtures.rs:222')).
fixture_metric(gpu, booking_1, 3, code_only('fixtures.rs:69')).
fixture_metric(gpu, booking_2, 4, code_only('fixtures.rs:80')).
fixture_metric(friday, booking_1, 3, code_only('fixtures.rs:69')).
fixture_metric(friday, booking_2, 4, code_only('fixtures.rs:80')).
fixture_metric(friday, slots_1,   5, code_only('fixtures.rs:94')).
fixture_metric(friday, slots_2,   6, code_only('fixtures.rs:96')).

% fixture_claim(Id, Fixture, Claim, Cite). Claim terms are interpreted by C-5.
fixture_claim('STOCK-SUM', inventory,
    conserved([available_depot, available_a, available_b, transit], 12),
    'spec:62 "available_depot + available_A + available_B + transit = 12 across ordinary transfer transitions"; handoff:21').
fixture_claim('STOCK-RESERVE', inventory,
    reserve_moves([available_depot, available_a, available_b], decrease, transit, increase),
    'spec:62 "Physical source availability decreases and reserved/in-transit quantity increases"').
fixture_claim('STOCK-RECEIPT', inventory,
    complete_moves(transit, decrease, [available_depot, available_a, available_b], increase),
    'spec:62 "Receipt moves transit into destination availability"').
fixture_claim('STOCK-POSITION', inventory,
    no_complete_effect([position_depot, position_a, position_b]),
    'spec:62 "planning positions move at reservation"').
fixture_claim('STOCK-INBOUND', inventory,
    no_reserve_credit([available_depot, available_a, available_b]),
    'spec:62 "Destination incoming position is never available stock"; handoff:21 "never spends inbound pipeline"').
fixture_claim('CASH-SUM', hiring,
    conserved([free, earmark, escrow, paid, protected], 10),
    'spec:64 "free + earmark + escrow + paid + protected = 10"; handoff:22').
fixture_claim('CASH-COVERAGE', hiring,
    no_complete_effect([coverage_research, coverage_implementation, coverage_review]),
    'spec:64 "Coverage remains after payment"; handoff:22 "payment preserves coverage"').
fixture_claim('CASH-ESCROW', hiring,
    complete_moves(escrow, decrease, [paid], increase),
    'spec:64 "Independent acceptance moves escrow to lifetime spending"').
fixture_claim('CASH-PREREQ', hiring,
    requires(review, [research-2, implementation-3]),
    'spec:64 "Review needs completed research units >=2 and implementation units >=3"').
fixture_claim('CASH-SELF', hiring,
    actor_not_executor,
    'spec:64 "No worker can authorize its own acceptance through the wrapper"').
% The same sentence read as a property of the wrapper (any config), not of the
% fixture's account names: the code would have to refuse actor = executor.
fixture_claim('CASH-SELF-ENFORCED', hiring,
    validate_rejects(actor-executor),
    'spec:64 "No worker can authorize its own acceptance through the wrapper"; spec:50 "the independent operator"; spec:64 "Independent acceptance"').
fixture_claim('RISK-SIGN', risk,
    reserve_sign([selloff_loss, funding_loss, volatility_loss], nonneg),
    'spec:66 "Positive loss contributions reserve immediately"').
fixture_claim('RISK-HEDGE', risk,
    complete_sign([selloff_loss, funding_loss, volatility_loss], nonpos),
    'spec:66 "hedge benefit occurs only on completion"').
fixture_claim('RISK-COLLATERAL', risk,
    complete_sign([collateral], nonpos),
    'spec:66 "Collateral encumbrance remains until an explicit later measured baseline"').
fixture_claim('RISK-HEADROOM', risk,
    pending_negative_no_headroom,
    'spec:66 "No pending hedge offsets are netted into new trade capacity"; handoff:23').
fixture_claim('GPU-SLOTS', gpu,
    no_complete_effect_all,
    'spec:60 "completion does not free historical slots"').
fixture_claim('FRIDAY-SLOTS', friday,
    no_complete_effect_all,
    'spec:60 "completion does not free historical slots"').
fixture_claim('FRIDAY-ATOMIC', friday,
    paired_reserve([booking_1-slots_1, booking_2-slots_2]),
    'spec:60 "Friday also consumes dispatch slots atomically"').
% spec:46, last sentence: in the supplied fixtures a release (cancel before
% dispatch, or the executor's settle(false) after it) never fails because
% another commitment relied on the released reservation. Checked by a bounded
% search (consistency.pl release_search: every admissible pair of requests from
% init, the other record Reserved or Completed, both release paths) and on
% every state of the fixture's own trace before its first observe.
fixture_claim('GPU-RELEASE', gpu, release_never_blocked,
    'spec:46 "In the supplied fixtures, physical availability and risk-credit timing prevent ordinary unsafe reliance on unexecuted work"').
fixture_claim('FRIDAY-RELEASE', friday, release_never_blocked,
    'spec:46 "In the supplied fixtures, physical availability and risk-credit timing prevent ordinary unsafe reliance on unexecuted work"').
fixture_claim('STOCK-RELEASE', inventory, release_never_blocked,
    'spec:46 "In the supplied fixtures, physical availability ... prevent ordinary unsafe reliance on unexecuted work"; spec:62').
fixture_claim('CASH-RELEASE', hiring, release_never_blocked,
    'spec:46 "In the supplied fixtures ... prevent ordinary unsafe reliance on unexecuted work"; spec:64').
fixture_claim('RISK-RELEASE', risk, release_never_blocked,
    'spec:46 "In the supplied fixtures, ... risk-credit timing prevent ordinary unsafe reliance on unexecuted work"; spec:66').
% recipe names used by requires/2 claims (fixtures.rs:191-212: CODE-ONLY order)
% are resolved by C-5 through fixture_recipe/3 in consistency.pl.

%% known_finding(ClaimId, FindingId): the code breaks this claim (a confirmed
%% finding). C-5 passes for it only if it REPRODUCES the counterexample; if the
%% counterexample disappears (code or fixture fixed) C-5 fails, so the finding
%% is re-examined instead of silently turning into a pass.
known_finding('RISK-RELEASE', 'F-2').
known_finding('CASH-SELF-ENFORCED', 'F-4').

%%% ========================================================
%%% Findings (brief, find/confirm phase; reproduced on the pinned core)
%%% ========================================================
%% finding(Id, Severity, Cite, Text). Each has a witness in this layer (see
%% RESULTS.md): MC-1, MC-2 (trace 0), C-5, or a step/4 test in test_model.pl.

finding('F-1', high, 'spec:23, 46; handoff:31',
    "Wedge: in a state disturbed by observe the recovery rule admits a hedge whose completion moves the disturbed metric back out; once the reservation brought it inside, settle(true) and settle(false) fail Bounds, cancel fails Pending, observe fails Pending forever.").
finding('F-2', high, 'spec:46, 66; handoff:23, 31',
    "Healthy-state release wedge: in the risk fixture a hedge admitted on the strength of a credit position's reservation blocks the position's release; the executor's honest settle(false) fails Bounds; cancel fails Pending once in flight (Bounds while still Reserved); observe fails Pending. No observe needed. Contradicts spec:46's fixture sentence.").
finding('F-3', low, 'handoff:34; api:8',
    "Slot exhaustion: one actor exhausts the 256 lifetime records with free submit+cancel cycles; Full is permanent (observe does not prune, spec:54).").
finding('F-4', low, 'spec:9, 50, 64',
    "Config::validate accepts actor = executor (or owner), so a principal can attest its own completion; the docs rely on independence.").
finding('F-5', low, 'handoff:34',
    "At version = u32::MAX every transition fails Arithmetic, including settlement of in-flight liabilities and unpausing.").
finding('F-6', low, 'spec:19, 37, 54',
    "With max_age > 0 one long-open record blocks the only snapshot refresh (observe Pending), so admissions and dispatches stop with SnapshotExpired.").

%%% ========================================================
%%% Divergences between the docs and the code (findings)
%%% ========================================================
%% divergence(Id, Cite, DocSays, CodeDoes). Each is also a finding in RESULTS.md;
%% the model follows the code (MC-2 must agree with the real core) and tags the
%% clause with the divergence id.

divergence('div-F1-inverse', 'spec:46; handoff:31',
    "A checked inverse can fail if another commitment depends on its contribution; liveness is conditional on resolving dependencies and receiving authoritative evidence.",
    "F-1: in a state disturbed by observe, a recovery hedge admitted under spec:21-23 can make both settle(completed) and settle(cancelled) fail Bounds with no other commitment open; cancel fails Pending and observe fails Pending forever (conformance trace 0, MC-1 dead state).").
divergence('div-F2-fixture-release', 'spec:46; spec:66; handoff:23',
    "In the supplied fixtures, physical availability and risk-credit timing prevent ordinary unsafe reliance on unexecuted work.",
    "F-2: in the risk fixture, with no observe, a credit position (recipe 0 x1) and a hedge (recipe 3 x7) admitted on the strength of the position's reservation make the position's release fail Bounds (cancel and the executor's settle(false)); the position can only end through settle(true). Found by C-5's release search (20 counterexamples within two records) and by MC-1's reliance universe.").
divergence('div-ack-noop-version', 'spec:39; api:26',
    "spec:39 lists Dispatched/Unknown -> Unknown as a transition and api:26 says every successful state transition changes version (only terminal duplicates are named idempotent).",
    "acknowledge returns Ok without a version bump when the status would not change (Unknown -> Unknown, a repeated Active) and for Reserved or Active records (core lib.rs:376-388; the comment cites reconcile griefing).").
divergence('div-cancel-terminal-name', 'spec:43; api:15',
    "Conflicting terminal evidence is rejected; cancel applies only to undispatched Reserved records.",
    "cancel of a Completed record (and of any dispatched record) fails with Pending, a name that suggests an unresolved commitment (lib.rs:402-404). The rejection itself agrees with the docs; the reason string does not distinguish 'already completed'.").

%%% ========================================================
%%% Ambiguities and decisions
%%% ========================================================

ambiguity('amb-interval-violation', 'spec:21',
    "\"no metric's violation amount may exceed its current violation\": the violation amount of an interval is not defined.",
    "Read as max(0, min - low) + max(0, high - max) against the point violation max(0, min - v) + max(0, v - max) of the current values (the code's reading, lib.rs:224-228).").
ambiguity('amb-freshness-boundary', 'spec:19, spec:37',
    "\"observation freshness if configured\" gives no boundary.",
    "Stale iff max_age > 0 and now > observed_at + max_age, saturating (CODE-ONLY, lib.rs:242-249).").
ambiguity('amb-recovery-name', 'spec:23',
    "The second energy condition has no error name.",
    "Energy (CODE-ONLY, lib.rs:281-285).").
ambiguity('amb-ack-other', 'spec:38-39, 44',
    "Acknowledgment from Reserved or Active is not described.",
    "Ignored: Ok with no change (CODE-ONLY, lib.rs:376-378).").
ambiguity('amb-reconcile-kind', 'api:13',
    "reconcile is open to anyone; whether it is a state change is not said.",
    "It sends a promise and changes nothing; the callback applies the result (shell lib.rs:97-117).").
ambiguity('amb-version-transition', 'api:26',
    "\"Every successful state transition changes version\": whether an Ok call that changes nothing is a 'state transition'.",
    "Two readings; the code bumps version on every Ok that changes some field (and on set_paused to the same value) and on nothing else; see div-ack-noop-version.").
ambiguity('amb-self-executor', 'spec:9, 50, 64',
    "spec:9 gives each recipe 'one exact actor account, one exact executor account' without saying they differ; spec:50 and spec:64 speak of an independent operator and independent acceptance; spec:64 claims no worker can authorize its own acceptance through the wrapper.",
    "The hiring fixture's names satisfy it (CASH-SELF); Config::validate does not enforce it (extracted code_role_checks(validate, []): F-4, CASH-SELF-ENFORCED). The model's valid_config follows the code (CODE-ONLY).").
ambiguity('amb-observe-length', 'spec:54',
    "\"bounded measured values\" does not say what happens to a vector of the wrong length.",
    "Rejected with Bounds (CODE-ONLY, lib.rs:467-469).").

decision('model-follows-code', "Where the docs are silent or disagree, pool_machine.pl follows the code so MC-2 can demand exact agreement with the real core's traces; every such clause is tagged CODE-ONLY or with its divergence id, and divergences are findings, not passes.").
decision('c2-unreachable', "C-2 compares guard orders modulo error sites that cannot fire from an INV state (InvalidConfig in add, NotFound in release, energy's Bounds/Arithmetic, the add in submit's recovery check). Each is listed with its justification in consistency.pl and may appear or not in the compared sequence; every other site must match exactly, in order.").
decision('c5-names', "The conformance generator renames fixture accounts (first actor a1, every later actor a2, executors x1/x2), so actor /= executor is true by construction on trace configs. C-5 checks the self-authorization claim on the fixture's own account names, extracted from fixtures.rs by extract.py.").
decision('tla-leg', "C-2's TLA leg compares tla/SharedPool.tla GuardOrder (extracted/tla_facts.pl) with the code path under the c2-unreachable rule; Noop entries are noop. If the TLA file does not exist, the leg is a recorded gap, not a pass.").

%%% ========================================================
%%% Helpers
%%% ========================================================

%% camel_snake(?Camel, ?Snake): 'SnapshotExpired' <-> snapshot_expired.
camel_snake(Camel, Snake) :-
    atom(Camel), !,
    atom_chars(Camel, Cs),
    to_snake(Cs, first, Ss),
    atom_chars(Snake, Ss).
camel_snake(Camel, Snake) :-
    atom(Snake),
    atom_chars(Snake, Ss),
    to_camel(Ss, up, Cs),
    atom_chars(Camel, Cs).

to_snake([], _, []).
to_snake([C | Cs], Pos, Out) :-
    char_code(C, K),
    (   K >= 0'A, K =< 0'Z
    ->  L is K + 32, char_code(LC, L),
        ( Pos == first -> Out = [LC | Rest] ; Out = ['_', LC | Rest] )
    ;   Out = [C | Rest]
    ),
    to_snake(Cs, rest, Rest).

to_camel([], _, []).
to_camel(['_' | Cs], _, Out) :- !, to_camel(Cs, up, Out).
to_camel([C | Cs], Mode, [D | Out]) :-
    (   Mode == up -> char_code(C, K), U is K - 32, char_code(D, U)
    ;   D = C
    ),
    to_camel(Cs, keep, Out).
