------------------------------- MODULE Props -------------------------------
(***************************************************************************)
(* Properties of SharedPool. IDs are the shared-pool catalogue's (brief:   *)
(* "Property catalogue"); each definition is tagged PROP: <ID>.            *)
(***************************************************************************)
EXTENDS SharedPool

\* B_i = PV_i(base): the violation of metric m at the last observe (or new).
B(m) == PV(base, m)
Healthy == \A m \in MIdx : B(m) = 0

-----------------------------------------------------------------------------
(* State invariants                                                        *)

\* PROP: INV-WF. Shapes and bounds of every field (records[j].id = j holds
\* by construction: an id is the record's index). Config never changes is
\* StepCfg below; ValidCfg(cfg) is CFG-1's "init satisfies INV".
InvWF ==
    /\ ValidCfg(cfg)
    /\ DOMAIN values = MIdx /\ \A m \in MIdx : Bounded(values[m])
    /\ version \in Nat /\ observedAt \in Nat /\ paused \in BOOLEAN
    /\ NR <= MaxRecords
    /\ \A k \in 1 .. NR :
        LET c == records[k] IN
        /\ c.recipe \in 0 .. NRcp - 1
        /\ c.units \in 1 .. Rcp(c.recipe).maxUnits
        /\ c.exp \in Nat
        /\ c.status \in Statuses
    /\ DOMAIN base = MIdx /\ k0 \in 0 .. NR /\ steps \in Nat

\* PROP: INV-LEDGER. values = base + sum over records j >= k0 that are not
\* Cancelled of reserve_j * u_j, plus complete_j * u_j for Completed ones.
Contribution(m) ==
    SumTo([k \in 1 .. NR |->
              LET c == records[k] IN
              IF k > k0 /\ c.status # "Cancelled"
              THEN Rcp(c.recipe).reserve[m] * c.units
                   + (IF c.status = "Completed" THEN Rcp(c.recipe).complete[m] * c.units ELSE 0)
              ELSE 0], NR)
InvLedger == \A m \in MIdx : values[m] = base[m] + Contribution(m)

\* PROP: INV-HARD. The envelope of the open records is computable and its
\* violation never exceeds the violation at the last observe.
CheckEnvOk ==
    \A m \in MIdx : Bounded(Low(values, 0, 0, -1, m)) /\ Bounded(High(values, 0, 0, -1, m))
InvHard == CheckEnvOk /\ \A m \in MIdx : EV(values, 0, 0, -1, m) <= B(m)

\* PROP: INV-HEALTHY (corollary of INV-HARD): with B = 0 every subset of the
\* open records' completions lands inside [min, max]. Enumerates subsets,
\* so only MC_Safety checks it.
OpenIds == {j \in 0 .. NR - 1 : Open(Rec(j).status)}
InvHealthy ==
    Healthy =>
        \A S \in SUBSET OpenIds : \A m \in MIdx :
            LET v == values[m] + SetSum(S, [j \in OpenIds |-> RecRcp(j).complete[m] * Rec(j).units])
            IN Mn(m) <= v /\ v <= Mx(m)

\* PROP: INV-DEP. Every record's prerequisites are met by Completed records
\* of lower index.
InvDep ==
    \A j \in 0 .. NR - 1 : \A q \in DOMAIN RecRcp(j).requires :
        LET p == RecRcp(j).requires[q][1]
            u == RecRcp(j).requires[q][2]
        IN SumTo([k \in 1 .. j |->
                     IF records[k].recipe = p /\ records[k].status = "Completed"
                     THEN records[k].units ELSE 0], j) >= u

\* PROP: INV-VER. version = number of effective transitions.
InvVer == version = steps

\* PROP: TERM-1 (error view). A terminal record: the same terminal again is
\* an Ok no-op, the opposite one InvalidState.
Term1 ==
    \A j \in 0 .. NR - 1 :
        LET x == RecRcp(j).executor IN
        /\ Rec(j).status = "Completed" =>
              SettleErr(x, j, TRUE) = "Noop" /\ SettleErr(x, j, FALSE) = "InvalidState"
        /\ Rec(j).status = "Cancelled" =>
              SettleErr(x, j, FALSE) = "Noop" /\ SettleErr(x, j, TRUE) = "InvalidState"

\* PROP: LIVE-1. With B = 0 and version < u32::MAX the executor can
\* complete every in-flight record.
Live1 ==
    (Healthy /\ version < MaxVersion) =>
        \A j \in 0 .. NR - 1 :
            InFlight(Rec(j).status) => SettleErr(RecRcp(j).executor, j, TRUE) = "Ok"

\* Everything but INV-HEALTHY (TraceCheck checks this on every core state).
Inv == InvWF /\ InvLedger /\ InvHard /\ InvDep /\ InvVer /\ Term1 /\ Live1
InvMC == Inv /\ InvHealthy

-----------------------------------------------------------------------------
(* Step properties, checked as [][StepProps]_vars. Every effective step    *)
(* changes version, so no effective step is a stutter of vars. L is the    *)
(* call that made the step.                                                *)

L == last'

\* PROP: INV-WF (config never changes).
StepCfg == cfg' = cfg

\* PROP: TX-VER. Every effective step increments version by exactly 1.
TxVer == version' = version + 1 /\ steps' = steps + 1

\* PROP: LIFE-1. Status graph, terminal absorbing, records append-only with
\* immutable id/recipe/units/expires_at, new records Reserved.
Edges ==
    { <<"Reserved", "Dispatched">>, <<"Reserved", "Cancelled">>,
      <<"Dispatched", "Active">>, <<"Dispatched", "Unknown">>, <<"Unknown", "Active">> }
    \cup { <<s, t>> : s \in {"Dispatched", "Active", "Unknown"}, t \in {"Completed", "Cancelled"} }
Life1 ==
    /\ Len(records') \in {NR, NR + 1}
    /\ \A k \in 1 .. NR :
        /\ records'[k].recipe = records[k].recipe
        /\ records'[k].units = records[k].units
        /\ records'[k].exp = records[k].exp
        /\ records'[k].status = records[k].status
           \/ <<records[k].status, records'[k].status>> \in Edges
    /\ \A k \in NR + 1 .. Len(records') : records'[k].status = "Reserved"

\* PROP: STALE-1. An accepted request carries the current version, and
\* versions strictly increase, so it cannot be accepted again.
Stale1 == (L.op = "submit" => L.v = version) /\ version' > version

\* PROP: AUTH-1. Who may make each effective call.
Auth1 ==
    /\ L.op \in {"submit", "dispatch"} => L.c = Rcp(L.r).actor
    /\ L.op = "cancel" => L.c \in {Rcp(L.r).actor, cfg.owner}
    /\ L.op = "settle" => L.c = Rcp(L.r).executor
    /\ L.op \in {"pause", "observe"} => L.c = cfg.owner

\* PROP: ADM-1. An accepted reservation does not increase energy.
Adm1 == L.op = "submit" => Energy(values') <= Energy(values)

\* PROP: ADM-2. In a violating state, the reservation plus its completion
\* strictly decreases energy.
Adm2 ==
    (L.op = "submit" /\ Violating) =>
        Energy(AddVec(values', Rcp(L.r).complete, L.u)) < Energy(values)

\* PROP: HARD-STEP. Every effective call but observe: no metric's violation
\* grows.
HardStep == L.op # "observe" => \A m \in MIdx : PV(values', m) <= PV(values, m)

\* PROP: DEP-1. An accepted request's prerequisites are met by Completed
\* units.
Dep1 ==
    L.op = "submit" =>
        \A q \in DOMAIN Rcp(L.r).requires :
            DoneUnits(Rcp(L.r).requires[q][1]) >= Rcp(L.r).requires[q][2]

\* PROP: ASYNC-1. acknowledge changes only the record's status (between
\* in-flight statuses), never values: Active and Unknown keep the
\* reservation (INV-LEDGER counts them).
Async1 ==
    L.op = "ack" =>
        /\ values' = values /\ observedAt' = observedAt /\ paused' = paused
        /\ Len(records') = NR
        /\ \A k \in 1 .. NR : k # L.i + 1 => records'[k] = records[k]
        /\ InFlight(records'[L.i + 1].status)

\* PROP: OBS-1. observe only with no open record; config and records kept.
Obs1 ==
    L.op = "observe" =>
        (\A k \in 1 .. NR : ~Open(records[k].status)) /\ records' = records /\ cfg' = cfg

\* PROP: TX-SUBMIT. The time, capacity and unit guards of an effective
\* submit held in the pre-state (the other guards are STALE-1, AUTH-1,
\* DEP-1, ADM-1, ADM-2, HARD-STEP and PAUSE-1).
Fresh(now) == cfg.maxAge = 0 \/ now <= observedAt + cfg.maxAge
TxSubmit ==
    L.op = "submit" =>
        /\ L.now < L.exp /\ L.exp <= L.now + Window /\ Fresh(L.now)
        /\ NR < MaxRecords /\ L.r < NRcp /\ L.u \in 1 .. Rcp(L.r).maxUnits
        /\ records' = Append(records, [recipe |-> L.r, units |-> L.u, exp |-> L.exp, status |-> "Reserved"])

\* PROP: TX-DISPATCH. An effective dispatch: the record was Reserved and
\* unexpired, the snapshot fresh, and only its status changed.
TxDispatch ==
    L.op = "dispatch" =>
        /\ Rec(L.i).status = "Reserved" /\ L.now < Rec(L.i).exp /\ Fresh(L.now)
        /\ records' = [records EXCEPT ![L.i + 1].status = "Dispatched"]
        /\ values' = values

\* PROP: PAUSE-1. Paused: no submit or dispatch takes effect. (That settle,
\* ack, cancel and observe still do is WitStep_Paused*.)
Pause1 == paused => L.op \notin {"submit", "dispatch"}

StepProps ==
    /\ StepCfg /\ TxVer /\ Life1 /\ Stale1 /\ Auth1 /\ Adm1 /\ Adm2
    /\ HardStep /\ Dep1 /\ Async1 /\ Obs1 /\ TxSubmit /\ TxDispatch /\ Pause1
StepProperty == [][StepProps]_vars

-----------------------------------------------------------------------------
(* Non-vacuity (TLA-WIT). Each must be reachable, so the runner checks     *)
(* them as invariants or step properties that must be VIOLATED.            *)

\* A record completed.
Witness_Completed == ~\E j \in 0 .. NR - 1 : Rec(j).status = "Completed"
\* A record with a prerequisite was admitted (prerequisite met).
Witness_Prerequisite == ~\E j \in 0 .. NR - 1 : Len(RecRcp(j).requires) > 0
\* An observe left a metric out of bounds (B # 0).
Witness_Disturbed == Healthy
\* F-1: an in-flight record neither settle can resolve.
Witness_Wedge ==
    ~\E j \in 0 .. NR - 1 :
        /\ InFlight(Rec(j).status)
        /\ SettleErr(RecRcp(j).executor, j, TRUE) = "Bounds"
        /\ SettleErr(RecRcp(j).executor, j, FALSE) = "Bounds"

\* Step witnesses (checked on every transition, VIEW or not).
\* Cancelled after dispatch: settle(false) of an in-flight record.
WitStep_CancelledAfterDispatch ==
    [][~\E k \in 1 .. NR : InFlight(records[k].status) /\ records'[k].status = "Cancelled"]_vars
\* Unknown -> Active (a late positive acknowledgement).
WitStep_UnknownToActive ==
    [][~\E k \in 1 .. NR : records[k].status = "Unknown" /\ records'[k].status = "Active"]_vars
\* Recovery admission: a submit accepted in a violating state.
WitStep_Recovery == [][~(L.op = "submit" /\ Violating)]_vars
\* PAUSE-1's second half: settle, ack, cancel and observe still take effect
\* while paused (one witness each).
PausedStep(op) == paused /\ paused' /\ L.op = op
WitStep_PausedSettle  == [][~PausedStep("settle")]_vars
WitStep_PausedAck     == [][~PausedStep("ack")]_vars
WitStep_PausedCancel  == [][~PausedStep("cancel")]_vars
WitStep_PausedObserve == [][~PausedStep("observe")]_vars

=============================================================================
