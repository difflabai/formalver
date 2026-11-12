%% threat_model.pl -- Adversaries, threats and trust assumptions for shared-pool-controls
%%
%% PROP: C-6
%%
%% There is no shared-pool strategy.md yet, so the threats are transcribed from
%% the upstream docs (spec.md, api.md, verification-handoff.md at pin a4bb5c3;
%% each cites its line) and the assumptions from the shared brief's ASM-* list.
%% mitigated_by/2 names the property IDs (brief catalogue) that address a
%% threat; C-6 checks that every one of them is a known property and that
%% every threat has a mitigation or a recorded residual.
%%
%%   adversary(Id, Capabilities)
%%   threat(Id, Cite, Threat, Residual)        Residual = none | Text
%%   mitigated_by(Threat, PropertyOrAssumption)
%%   accepted_risk(Threat, Text)
%%   assumption(Id, Text, Level)               Level = high | med | low | policy
%%   assumption_checked_by(Asm, Check)         a property or tool that tests it

:- module(threat_model, [
    adversary/2,
    threat/4,
    mitigated_by/2,
    accepted_risk/2,
    assumption/3,
    assumption_checked_by/2
]).

%%% ========================================================
%%% Adversaries
%%% ========================================================

adversary('ADV-ACTOR', "A recipe actor (or anyone holding its key): calls submit/dispatch/cancel with any arguments, any number of times, in any order; reads the whole state (get_pool).").
adversary('ADV-ANY', "Any NEAR account: calls every public method, including reconcile (api:13) and preview with any proposed actor (spec:11).").
adversary('ADV-RELAY', "A contract or relayer between a key holder and the pool: its calls are attributed to it, not to the signer (spec:11).").
adversary('ADV-EXEC', "The recipe executor account: may attest completion or nonexecution; trusted for the truth of its attestation (ASM-EXEC), not for anything else.").
adversary('ADV-OWNER', "The owner: pause/observe/cancel; trusted for the truth of observations (ASM-OWNER), not assumed powerless (spec:56).").
adversary('ADV-DEPLOY', "Holder of a full-access key on the deployment account: can replace code (spec:56); out of scope (ASM-DEPLOY).").

%%% ========================================================
%%% Threats -> mitigating properties
%%% ========================================================

threat('T-ATTRIB', 'spec:11', "A call is attributed to an actor that did not make it (JSON actor field, signer instead of predecessor, preview identity).", none).
threat('T-INIT', 'spec:11; api:7', "An unrelated caller initializes the pool, or the pool is re-initialized.", none).
threat('T-FORGE', 'api:18; api:34', "Execution evidence is forged through a public callback or a non-executor settle.", none).
threat('T-REPLAY', 'spec:25; handoff:16', "An accepted request is replayed (no nonce).", none).
threat('T-OVERCOMMIT', 'spec:21; handoff:14', "An admission lets some subset of outstanding completions drive a metric past its hard bound, or worsens a disturbed metric.", none).
threat('T-ENERGY', 'spec:23; handoff:14', "An admission increases the potential.", none).
threat('T-OVERFLOW', 'spec:13; handoff:12', "Integer overflow in values, envelopes, energy or version.", "F-5: overflow fails closed, but at version = u32::MAX every transition fails, including settlement of in-flight liabilities and unpausing").
threat('T-PARTIAL', 'spec:25; handoff:15', "A rejected call leaves part of its effect in state.", none).
threat('T-DOUBLE', 'spec:43; handoff:18', "A commitment is settled twice, or both completed and cancelled.", none).
threat('T-UNKNOWN', 'spec:39, 48; handoff:17', "An unknown or failed acknowledgment releases the reservation while the job may have run.", "ASM-EXEC: settle(false) is only as true as the executor").
threat('T-PREREQ', 'spec:64; handoff:19', "Dependent work is admitted before its prerequisites are completed.", none).
threat('T-SELF', 'spec:64; spec:50', "A worker authorizes its own acceptance.", "F-4: Config::validate accepts actor = executor; only the supplied hiring fixture's account names prevent it (CASH-SELF holds, CASH-SELF-ENFORCED is the known finding)").
threat('T-PAUSE', 'spec:54', "Admission or dispatch takes effect while paused; or pausing blocks settlement.", none).
threat('T-OBS', 'spec:54', "observe runs with unresolved commitments, changes policy or deletes history.", "ASM-OWNER: the observed values themselves are trusted").
threat('T-BIND', 'spec:50; handoff:20', "The executor runs a different recipe/quantity than the reservation, or a duplicate dispatch runs twice.", none).
threat('T-RECONCILE', 'api:13; core lib.rs:384', "Anyone calls reconcile repeatedly to churn version (griefing pending requests into Stale).", "Bounded by the core's no-op ack rule; this is also where the docs and code disagree (div-ack-noop-version)").
threat('T-DEPOSIT', 'api:3', "Attached deposits are accepted by a mutating method.", none).
threat('T-GROWTH', 'handoff:34; api:8-9', "Unbounded storage or gas growth.", none).
threat('T-SLOTS', 'handoff:34; api:8; spec:54', "An actor exhausts the 256 lifetime records with free submit+cancel cycles, so nobody can be admitted again.", "F-3: Full is permanent; observe does not prune history (spec:54)").
threat('T-FRESHNESS', 'spec:19, 37, 54', "With max_age > 0, one long-open record (an executor that never settles) blocks the only snapshot refresh, so admissions and dispatches stop.", "F-6: observe needs every record terminal; nothing else refreshes observed_at").
threat('T-WEDGE', 'spec:46; handoff:31', "A commitment can never become terminal and the pool can never be observed again.", "F-1: reachable from a disturbed state through the recovery rule (spec:23) with no other commitment open; no administrative release exists (spec:46). Confirmed by MC-1 and trace 0. F-2: in the healthy risk fixture a hedge relying on a position's reservation blocks the position's release (C-5, MC-1 reliance).").
threat('T-REDEPLOY', 'spec:56', "Code is replaced through a deployment-account full-access key.", "Out of scope (ASM-DEPLOY)").

mitigated_by('T-ATTRIB', 'AUTH-1').  mitigated_by('T-ATTRIB', 'SH-1').  mitigated_by('T-ATTRIB', 'RT-PRED').
mitigated_by('T-ATTRIB', 'C-1').     mitigated_by('T-ATTRIB', 'ASM-PRED').
mitigated_by('T-INIT', 'SH-2').      mitigated_by('T-INIT', 'RT-PRIVATE'). mitigated_by('T-INIT', 'C-1').
mitigated_by('T-INIT', 'ASM-PRIVATE').
mitigated_by('T-FORGE', 'SH-3').     mitigated_by('T-FORGE', 'RT-PRIVATE'). mitigated_by('T-FORGE', 'AUTH-1').
mitigated_by('T-FORGE', 'C-1').      mitigated_by('T-FORGE', 'ASM-CALLBACK').
mitigated_by('T-REPLAY', 'STALE-1'). mitigated_by('T-REPLAY', 'TX-VER'). mitigated_by('T-REPLAY', 'INV-VER').
mitigated_by('T-OVERCOMMIT', 'HARD-STEP'). mitigated_by('T-OVERCOMMIT', 'INV-HARD').
mitigated_by('T-OVERCOMMIT', 'INV-HEALTHY'). mitigated_by('T-OVERCOMMIT', 'TX-SUBMIT').
mitigated_by('T-ENERGY', 'ADM-1').   mitigated_by('T-ENERGY', 'ADM-2').
mitigated_by('T-OVERFLOW', 'NUM-1'). mitigated_by('T-OVERFLOW', 'NUM-2'). mitigated_by('T-OVERFLOW', 'ROB-1').
mitigated_by('T-OVERFLOW', 'C-4').   mitigated_by('T-OVERFLOW', 'ASM-COMPILE').
mitigated_by('T-PARTIAL', 'TX-0').   mitigated_by('T-PARTIAL', 'SH-5'). mitigated_by('T-PARTIAL', 'RT-REVERT').
mitigated_by('T-PARTIAL', 'ASM-ATOMIC').
mitigated_by('T-DOUBLE', 'TERM-1').  mitigated_by('T-DOUBLE', 'LIFE-1'). mitigated_by('T-DOUBLE', 'EX-4').
mitigated_by('T-DOUBLE', 'C-3').
mitigated_by('T-UNKNOWN', 'ASYNC-1'). mitigated_by('T-UNKNOWN', 'RT-CALLBACK'). mitigated_by('T-UNKNOWN', 'SH-3').
mitigated_by('T-UNKNOWN', 'INV-LEDGER').
mitigated_by('T-PREREQ', 'DEP-1').   mitigated_by('T-PREREQ', 'INV-DEP'). mitigated_by('T-PREREQ', 'C-5').
mitigated_by('T-SELF', 'C-5').       mitigated_by('T-SELF', 'AUTH-1').
mitigated_by('T-PAUSE', 'PAUSE-1').  mitigated_by('T-PAUSE', 'C-2').
mitigated_by('T-OBS', 'OBS-1').      mitigated_by('T-OBS', 'INV-WF').
mitigated_by('T-BIND', 'EX-2').      mitigated_by('T-BIND', 'SH-6'). mitigated_by('T-BIND', 'LIFE-1').
mitigated_by('T-BIND', 'EX-1').
mitigated_by('T-RECONCILE', 'SH-7'). mitigated_by('T-RECONCILE', 'TX-NOOP'). mitigated_by('T-RECONCILE', 'C-3').
mitigated_by('T-DEPOSIT', 'SH-10').  mitigated_by('T-DEPOSIT', 'C-1').
mitigated_by('T-GROWTH', 'INV-WF').  mitigated_by('T-GROWTH', 'RES-1'). mitigated_by('T-GROWTH', 'SH-9').
mitigated_by('T-GROWTH', 'C-4').
% T-SLOTS, T-FRESHNESS: properties that bound or witness them (not preventions).
mitigated_by('T-SLOTS', 'INV-WF').    mitigated_by('T-SLOTS', 'TX-SUBMIT').   mitigated_by('T-SLOTS', 'C-4').
mitigated_by('T-FRESHNESS', 'TX-SUBMIT'). mitigated_by('T-FRESHNESS', 'TX-DISPATCH'). mitigated_by('T-FRESHNESS', 'OBS-1').
% T-WEDGE: the properties that detect it (they fail or witness it), not ones that prevent it.
mitigated_by('T-WEDGE', 'LIVE-1').   mitigated_by('T-WEDGE', 'LIVE-2'). mitigated_by('T-WEDGE', 'MC-1').
mitigated_by('T-WEDGE', 'RT-WEDGE'). mitigated_by('T-WEDGE', 'TLA-LIVE-F1'). mitigated_by('T-WEDGE', 'LEAN-WIT').
mitigated_by('T-WEDGE', 'C-5').
mitigated_by('T-REDEPLOY', 'ASM-DEPLOY').

accepted_risk('T-REDEPLOY', "spec:56: deployment upgrade authority is verified separately.").
accepted_risk('T-UNKNOWN', "spec:48: an executed but unacknowledged job remains a liability until authoritative evidence arrives.").
accepted_risk('T-OBS', "spec:54: observe is a trusted external fact assertion and may create a hard-limit violation.").
accepted_risk('T-WEDGE', "Not accepted upstream: spec:46 attributes a failing inverse to a dependent commitment; F-1 has none, and F-2 contradicts spec:46's claim for the supplied fixtures. Reported as findings.").
accepted_risk('T-SLOTS', "Not stated upstream beyond handoff:34 ('256 lifetime records bound ordinary growth'); reported as F-3.").
accepted_risk('T-FRESHNESS', "Not stated upstream; reported as F-6.").

%%% ========================================================
%%% Assumptions (brief ASM-*)
%%% ========================================================

assumption('ASM-PRED', "The predecessor account id is unforgeable.", high).
assumption('ASM-PRIVATE', "#[private] admits exactly predecessor = current account.", high).
assumption('ASM-CALLBACK', "A callback sees the executor's return value or PromiseError.", high).
assumption('ASM-ATOMIC', "A panicking receipt writes nothing.", high).
assumption('ASM-INTERLEAVE', "Other receipts can run between dispatch and on_result; the models treat ack/settle as independent steps.", med).
assumption('ASM-TIME', "The block timestamp is monotone.", high).
assumption('ASM-EXEC', "The executor is honest: settle(false) only on definitive nonexecution.", policy).
assumption('ASM-OWNER', "Owner observations are truthful.", policy).
assumption('ASM-DEPLOY', "No code replacement; the deployment lock is out of scope.", policy).
assumption('ASM-TOOLS', "Scryer Prolog, TLC, Lean, Kani and the extractors are sound for what is used.", med).
assumption('ASM-SPEC', "The specs (and this layer's transcription of the docs) mean what we intend; needs an independent reviewer. The author of this layer had read the code.", low).
assumption('ASM-MODEL', "Kani's small scope (and MC-1's small universe) is representative.", med).
assumption('ASM-LEAN-TLA', "The Lean and TLA+ models transcribe the code's semantics.", med).
assumption('ASM-COMPILE', "The release profile has overflow-checks = true.", high).

assumption_checked_by('ASM-PRED', 'RT-PRED').      assumption_checked_by('ASM-PRED', 'SH-1').
assumption_checked_by('ASM-PRIVATE', 'RT-PRIVATE'). assumption_checked_by('ASM-PRIVATE', 'SH-2').
assumption_checked_by('ASM-CALLBACK', 'RT-CALLBACK').
assumption_checked_by('ASM-ATOMIC', 'RT-REVERT').
assumption_checked_by('ASM-INTERLEAVE', 'RT-RACE').
assumption_checked_by('ASM-TOOLS', 'canaries and mutants in every runner').
assumption_checked_by('ASM-SPEC', 'status.toml [review] spec_reviewer (empty)').
assumption_checked_by('ASM-LEAN-TLA', 'MC-2').     assumption_checked_by('ASM-LEAN-TLA', 'REF-5').
assumption_checked_by('ASM-LEAN-TLA', 'REF-5L').   assumption_checked_by('ASM-LEAN-TLA', 'C-2').
assumption_checked_by('ASM-COMPILE', 'tools/scripts/check-pin.sh').
