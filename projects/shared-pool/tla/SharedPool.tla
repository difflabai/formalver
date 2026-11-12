----------------------------- MODULE SharedPool -----------------------------
(***************************************************************************)
(* pool-core of difflabai/shared-pool-controls as a state machine over     *)
(* every call sequence (near-approval strategy.md section 17 pattern).     *)
(*                                                                         *)
(* Upstream: difflabai/shared-pool-controls crates/core/src/lib.rs         *)
(* Pin:      a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7 (PR #1 head)         *)
(*                                                                         *)
(* The variables are the Pool struct field by field:                       *)
(*                                                                         *)
(*   cfg         Config (owner, max_age_seconds, metrics, terms, recipes). *)
(*               A variable, not a constant, so one TLC run can replay     *)
(*               traces of many configurations (REF-5); no action writes   *)
(*               it (INV-WF, StepCfg).                                      *)
(*   values      Pool.values, a sequence over the metrics (1-based: the    *)
(*               code's metric i is values[i + 1])                         *)
(*   version     Pool.version                                              *)
(*   observedAt  Pool.observed_at                                          *)
(*   paused      Pool.paused                                               *)
(*   records     Pool.records; record id j is records[j + 1], so           *)
(*               records[j].id = j holds by construction (INV-WF)          *)
(*                                                                         *)
(* Names and units of metrics and recipes are not modelled: the core only  *)
(* validates their lengths. Ghost (not in the Pool): base and k0 are the   *)
(* values and the record count at the last observe (or new), steps counts  *)
(* effective transitions (INV-VER), last is the most recent effective call *)
(* (a history variable read only by step properties).                      *)
(*                                                                         *)
(* Each entry point has an error operator giving the first failing guard   *)
(* in the core's order, "Noop" for the core's idempotent Ok(()) paths      *)
(* (TX-NOOP), or "Ok", and an action enabled exactly when it is "Ok". A    *)
(* rejected or idempotent call writes nothing (TX-0), so it is a           *)
(* stuttering step and not part of Next.                                   *)
(*                                                                         *)
(* Numbers are exact integers. The core's i64/u64 arithmetic cannot wrap   *)
(* on these paths (NUM-1, NUM-2: values stay within +-1e6, units <= 100,   *)
(* weights <= 1000), and every bound check is transcribed. Two constants   *)
(* are scaled in the TLC configs (C-5): MaxRecords (MAX_RECORDS = 256) and *)
(* MaxVersion (u32::MAX does not fit TLC's 32-bit integers; the configs    *)
(* use 2^31 - 1, which no run reaches).                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    \* Every account that calls: owner, actors, executors and strangers.
    Accounts,
    \* Argument domains of Next (model checking only; TraceCheck replays
    \* the recorded arguments): block times, expiry offsets added to now,
    \* and the vectors the owner may observe.
    Times,
    ExpOffsets,
    Observations,
    \* MAX_RECORDS (256 in the core).
    MaxRecords,
    \* u32::MAX: bump() fails when version = MaxVersion.
    MaxVersion

MaxValue  == 1000000    \* MAX_VALUE
MaxMetric == 32         \* MAX_METRICS
MaxRecipe == 32         \* MAX_RECIPES
MaxTerm   == 64         \* MAX_TERMS
MaxWeight == 1000       \* MAX_WEIGHT
MaxUnit   == 100        \* MAX_UNITS
Window    == 86400      \* submit: expires_at <= now + 86400

Statuses == {"Reserved", "Dispatched", "Active", "Unknown", "Completed", "Cancelled"}
Shapes   == {"target", "excess", "deficit"}

VARIABLES
    cfg, values, version, observedAt, paused, records,
    base, k0, steps, last

pool  == <<cfg, values, version, observedAt, paused, records>>
vars  == <<cfg, values, version, observedAt, paused, records, base, k0, steps, last>>

-----------------------------------------------------------------------------
(* Arithmetic helpers                                                      *)

Max0(x) == IF x > 0 THEN x ELSE 0
Min0(x) == IF x < 0 THEN x ELSE 0
Abs(x)  == IF x < 0 THEN -x ELSE x
\* bounded(): -MAX_VALUE ..= MAX_VALUE.
Bounded(v) == -MaxValue <= v /\ v <= MaxValue

\* Sum of f[1] .. f[k].
RECURSIVE SumTo(_, _)
SumTo(f, k) == IF k = 0 THEN 0 ELSE f[k] + SumTo(f, k - 1)

RECURSIVE SetSum(_, _)
\* Sum of g[x] over a finite set S.
SetSum(S, g) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN g[x] + SetSum(S \ {x}, g)

-----------------------------------------------------------------------------
(* Shape of the configuration and the records                              *)

NM   == Len(cfg.metrics)
MIdx == 1 .. NM
NR   == Len(records)
NRcp == Len(cfg.recipes)
Rec(i)    == records[i + 1]
Rcp(r)    == cfg.recipes[r + 1]
RecRcp(i) == Rcp(Rec(i).recipe)
Mn(m) == cfg.metrics[m].min
Mx(m) == cfg.metrics[m].max
\* The largest max_units of any recipe (argument domain of Next).
MaxU == LET us == {cfg.recipes[k].maxUnits : k \in 1 .. NRcp} IN CHOOSE u \in us : \A w \in us : w <= u

Open(s)     == s \notin {"Completed", "Cancelled"}
InFlight(s) == s \in {"Dispatched", "Active", "Unknown"}

\* Config::validate (CFG-2), names omitted. requires is a sequence of
\* <<prerequisite recipe, units>>.
ValidCfg(c) ==
    LET n == Len(c.metrics) IN
    /\ n >= 1 /\ n <= MaxMetric
    /\ Len(c.recipes) >= 1 /\ Len(c.recipes) <= MaxRecipe
    /\ Len(c.terms) >= 1 /\ Len(c.terms) <= MaxTerm
    /\ c.maxAge >= 0
    /\ \A m \in 1 .. n:
        LET x == c.metrics[m] IN
        /\ Bounded(x.min) /\ Bounded(x.max) /\ x.min <= x.max
        /\ x.min <= x.init /\ x.init <= x.max
    /\ \A k \in 1 .. Len(c.terms):
        LET t == c.terms[k] IN
        /\ t.metric \in 0 .. n - 1 /\ Bounded(t.target)
        /\ t.weight \in 1 .. MaxWeight /\ t.shape \in Shapes
    /\ \A k \in 1 .. Len(c.recipes):
        LET r == c.recipes[k] IN
        /\ Len(r.reserve) = n /\ Len(r.complete) = n
        /\ r.maxUnits \in 1 .. MaxUnit
        /\ Len(r.requires) <= MaxRecipe
        /\ \A q \in DOMAIN r.requires:
              r.requires[q][1] \in 0 .. k - 2 /\ r.requires[q][2] \in 1 .. MaxUnit
        /\ \A m \in 1 .. n: Bounded(r.reserve[m]) /\ Bounded(r.complete[m])
        /\ \A q1, q2 \in DOMAIN r.requires: q1 # q2 => r.requires[q1][1] # r.requires[q2][1]

-----------------------------------------------------------------------------
(* The core's private functions                                            *)

\* violations(values)[i]: PV_i(v) = max(0, min_i - v_i) + max(0, v_i - max_i).
PV(vals, m) == Max0(Mn(m) - vals[m]) + Max0(vals[m] - Mx(m))
Violating == \E m \in MIdx : PV(values, m) > 0

\* add(base, d, u): the exact result, and whether some component leaves
\* +-MAX_VALUE (Arithmetic). Lengths are equal in every WF state.
AddVec(b, d, u)   == [m \in DOMAIN b |-> b[m] + d[m] * u]
AddFails(b, d, u) == \E m \in DOMAIN b : ~Bounded(b[m] + d[m] * u)
Neg(d) == [m \in DOMAIN d |-> -d[m]]

\* envelope(): sum over the open records other than skip (-1 for None) of
\* the negative (neg) or positive parts of complete * units on metric m.
OpenSum(m, skip, neg) ==
    SumTo([k \in 1 .. NR |->
              LET c == records[k]
                  d == Rcp(c.recipe).complete[m] * c.units
              IN IF Open(c.status) /\ k - 1 # skip
                 THEN (IF neg THEN Min0(d) ELSE Max0(d)) ELSE 0], NR)
\* The extra (recipe er, eu units) of candidate(); eu = 0 means None.
ExtraPart(er, eu, m, neg) ==
    IF eu = 0 THEN 0
    ELSE LET d == Rcp(er).complete[m] * eu IN IF neg THEN Min0(d) ELSE Max0(d)
Low(cand, er, eu, skip, m)  == cand[m] + OpenSum(m, skip, TRUE) + ExtraPart(er, eu, m, TRUE)
High(cand, er, eu, skip, m) == cand[m] + OpenSum(m, skip, FALSE) + ExtraPart(er, eu, m, FALSE)
\* EV_i: the envelope's violation of metric m.
EV(cand, er, eu, skip, m) ==
    Max0(Mn(m) - Low(cand, er, eu, skip, m)) + Max0(High(cand, er, eu, skip, m) - Mx(m))

\* check_bounds(candidate, extra, skip). The envelope's partial sums are
\* monotone from a bounded start, so it fails (Arithmetic) exactly when a
\* final low or high leaves +-MAX_VALUE; then Bounds if some metric's
\* envelope violation exceeds its current violation.
CheckBounds(cand, er, eu, skip) ==
    LET lo == [m \in MIdx |-> Low(cand, er, eu, skip, m)]
        hi == [m \in MIdx |-> High(cand, er, eu, skip, m)]
    IN IF \E m \in MIdx : ~Bounded(lo[m]) \/ ~Bounded(hi[m]) THEN "Arithmetic"
       ELSE IF \E m \in MIdx : Max0(Mn(m) - lo[m]) + Max0(hi[m] - Mx(m)) > PV(values, m)
            THEN "Bounds"
       ELSE "Ok"

\* energy(): sum of weight * r^2 over the terms. Exact (NUM-1).
TermR(vals, t) ==
    LET d == vals[t.metric + 1] - t.target IN
    CASE t.shape = "target"  -> Abs(d)
      [] t.shape = "excess"  -> Max0(d)
      [] t.shape = "deficit" -> Max0(-d)
Energy(vals) ==
    SumTo([k \in 1 .. Len(cfg.terms) |->
              LET r == TermR(vals, cfg.terms[k]) IN cfg.terms[k].weight * r * r],
          Len(cfg.terms))

\* Units of Completed records of recipe p (candidate's prerequisite sum).
DoneUnits(p) ==
    SumTo([k \in 1 .. NR |->
              IF records[k].recipe = p /\ records[k].status = "Completed"
              THEN records[k].units ELSE 0], NR)

\* bump(): version.checked_add(1).
VerErr == IF version >= MaxVersion THEN "Arithmetic" ELSE "Ok"

SnapExpired(now) == cfg.maxAge > 0 /\ now > observedAt + cfg.maxAge

-----------------------------------------------------------------------------
(* Guards, in the core's order. GuardOrder lists each entry point's exits  *)
(* in order: error codes, and "Noop" where an idempotent Ok(()) returns    *)
(* early. Arithmetic appears once per checked operation (add, envelope,    *)
(* version bump). C-2 compares it with the Prolog guard table.             *)

GuardOrder == [
    submit   |-> <<"Paused", "Stale", "Expired", "SnapshotExpired", "Full",
                   "InvalidRecipe", "Unauthorized", "InvalidUnits", "Prerequisite",
                   "Arithmetic", "Arithmetic", "Bounds", "Energy", "Arithmetic",
                   "Energy", "Arithmetic">>,
    dispatch |-> <<"NotFound", "Unauthorized", "Paused", "InvalidState", "Expired",
                   "SnapshotExpired", "Arithmetic">>,
    ack      |-> <<"NotFound", "Noop", "Noop", "Arithmetic">>,
    cancel   |-> <<"NotFound", "Unauthorized", "Noop", "Pending",
                   "Arithmetic", "Arithmetic", "Bounds", "Arithmetic">>,
    settle   |-> <<"NotFound", "Unauthorized", "Noop", "InvalidState",
                   "Arithmetic", "Arithmetic", "Bounds", "Arithmetic">>,
    pause    |-> <<"Unauthorized", "Arithmetic">>,
    observe  |-> <<"Unauthorized", "Pending", "Bounds", "Arithmetic">>
]

\* candidate() then submit's bump.
SubmitErr(c, r, u, v, exp, now) ==
    IF paused THEN "Paused"
    ELSE IF v # version THEN "Stale"
    ELSE IF exp <= now \/ exp > now + Window THEN "Expired"
    ELSE IF SnapExpired(now) THEN "SnapshotExpired"
    ELSE IF NR >= MaxRecords THEN "Full"
    ELSE IF r >= NRcp THEN "InvalidRecipe"
    ELSE IF c # Rcp(r).actor THEN "Unauthorized"
    ELSE IF u = 0 \/ u > Rcp(r).maxUnits THEN "InvalidUnits"
    ELSE IF \E q \in DOMAIN Rcp(r).requires :
                DoneUnits(Rcp(r).requires[q][1]) < Rcp(r).requires[q][2]
         THEN "Prerequisite"
    ELSE IF AddFails(values, Rcp(r).reserve, u) THEN "Arithmetic"
    ELSE LET next == AddVec(values, Rcp(r).reserve, u)
             cb   == CheckBounds(next, r, u, -1)
             e0   == Energy(values)
         IN IF cb # "Ok" THEN cb
            ELSE IF Energy(next) > e0 THEN "Energy"
            ELSE IF Violating /\ AddFails(next, Rcp(r).complete, u) THEN "Arithmetic"
            ELSE IF Violating /\ Energy(AddVec(next, Rcp(r).complete, u)) >= e0
                 THEN "Energy"
            ELSE VerErr

DispatchErr(c, i, now) ==
    IF i >= NR THEN "NotFound"
    ELSE IF c # RecRcp(i).actor THEN "Unauthorized"
    ELSE IF paused THEN "Paused"
    ELSE IF Rec(i).status # "Reserved" THEN "InvalidState"
    ELSE IF now >= Rec(i).exp THEN "Expired"
    ELSE IF SnapExpired(now) THEN "SnapshotExpired"
    ELSE VerErr

AckTo(acc) == IF acc THEN "Active" ELSE "Unknown"

\* acknowledge(id, accepted): no caller in the core (the shell's private
\* callback is the only caller, SH-3).
AckErr(i, acc) ==
    IF i >= NR THEN "NotFound"
    ELSE IF Rec(i).status \notin {"Dispatched", "Unknown"} THEN "Noop"
    ELSE IF Rec(i).status = AckTo(acc) THEN "Noop"
    ELSE VerErr

\* release(id): undo the reservation; the envelope skips the record.
ReleaseErr(i) ==
    LET d == Neg(RecRcp(i).reserve)
        u == Rec(i).units
    IN IF AddFails(values, d, u) THEN "Arithmetic"
       ELSE LET cb == CheckBounds(AddVec(values, d, u), 0, 0, i) IN
            IF cb # "Ok" THEN cb ELSE VerErr

\* cancel(caller, id, now): now is unused by the core.
CancelErr(c, i, now) ==
    IF i >= NR THEN "NotFound"
    ELSE IF c # RecRcp(i).actor /\ c # cfg.owner THEN "Unauthorized"
    ELSE IF Rec(i).status = "Cancelled" THEN "Noop"
    ELSE IF Rec(i).status # "Reserved" THEN "Pending"
    ELSE ReleaseErr(i)

SettleErr(c, i, done) ==
    IF i >= NR THEN "NotFound"
    ELSE IF c # RecRcp(i).executor THEN "Unauthorized"
    ELSE IF (done /\ Rec(i).status = "Completed") \/ (~done /\ Rec(i).status = "Cancelled")
         THEN "Noop"
    ELSE IF ~InFlight(Rec(i).status) THEN "InvalidState"
    ELSE IF ~done THEN ReleaseErr(i)
    ELSE LET d == RecRcp(i).complete
             u == Rec(i).units
         IN IF AddFails(values, d, u) THEN "Arithmetic"
            ELSE LET cb == CheckBounds(AddVec(values, d, u), 0, 0, i) IN
                 IF cb # "Ok" THEN cb ELSE VerErr

PauseErr(c, b) ==
    IF c # cfg.owner THEN "Unauthorized" ELSE VerErr

\* observe: energy(values)? cannot fail for a bounded vector of the right
\* length (NUM-1), so it has no exit here.
ObserveErr(c, vals, now) ==
    IF c # cfg.owner THEN "Unauthorized"
    ELSE IF \E k \in 1 .. NR : Open(records[k].status) THEN "Pending"
    ELSE IF Len(vals) # NM \/ \E k \in DOMAIN vals : ~Bounded(vals[k]) THEN "Bounds"
    ELSE VerErr

-----------------------------------------------------------------------------
(* Actions: the effect of an "Ok" call                                     *)

Initial(c) == [m \in 1 .. Len(c.metrics) |-> c.metrics[m].init]

\* Pool::new(c, t0) for a configuration that validates (CFG-1).
InitFrom(c, t0) ==
    /\ cfg = c
    /\ values = Initial(c)
    /\ version = 0
    /\ observedAt = t0
    /\ paused = FALSE
    /\ records = <<>>
    /\ base = Initial(c)
    /\ k0 = 0
    /\ steps = 0
    /\ last = [op |-> "new", c |-> c.owner, i |-> 0, r |-> 0, u |-> 0, v |-> 0, b |-> FALSE,
               now |-> t0, exp |-> 0]

\* Ghost bookkeeping of an effective call: its arguments (r and u are the
\* record's recipe and units for calls on a record id).
Step(op, c, i, r, u, v, b, now, exp) ==
    /\ steps' = steps + 1
    /\ last' = [op |-> op, c |-> c, i |-> i, r |-> r, u |-> u, v |-> v, b |-> b,
                now |-> now, exp |-> exp]

SetStatus(i, s) == records' = [records EXCEPT ![i + 1].status = s]

Submit(c, r, u, v, exp, now) ==
    /\ SubmitErr(c, r, u, v, exp, now) = "Ok"
    /\ records' = Append(records, [recipe |-> r, units |-> u, exp |-> exp, status |-> "Reserved"])
    /\ values' = AddVec(values, Rcp(r).reserve, u)
    /\ version' = version + 1
    /\ UNCHANGED <<cfg, observedAt, paused, base, k0>>
    /\ Step("submit", c, NR, r, u, v, FALSE, now, exp)

Dispatch(c, i, now) ==
    /\ DispatchErr(c, i, now) = "Ok"
    /\ SetStatus(i, "Dispatched")
    /\ version' = version + 1
    /\ UNCHANGED <<cfg, values, observedAt, paused, base, k0>>
    /\ Step("dispatch", c, i, Rec(i).recipe, Rec(i).units, 0, FALSE, now, 0)

Ack(i, acc) ==
    /\ AckErr(i, acc) = "Ok"
    /\ SetStatus(i, AckTo(acc))
    /\ version' = version + 1
    /\ UNCHANGED <<cfg, values, observedAt, paused, base, k0>>
    /\ Step("ack", cfg.owner, i, Rec(i).recipe, Rec(i).units, 0, acc, 0, 0)

\* release(id)'s effect.
Release(i) ==
    /\ values' = AddVec(values, Neg(RecRcp(i).reserve), Rec(i).units)
    /\ SetStatus(i, "Cancelled")
    /\ version' = version + 1
    /\ UNCHANGED <<cfg, observedAt, paused, base, k0>>

Cancel(c, i, now) ==
    /\ CancelErr(c, i, now) = "Ok"
    /\ Release(i)
    /\ Step("cancel", c, i, Rec(i).recipe, Rec(i).units, 0, FALSE, now, 0)

Settle(c, i, done) ==
    /\ SettleErr(c, i, done) = "Ok"
    /\ IF done
       THEN /\ values' = AddVec(values, RecRcp(i).complete, Rec(i).units)
            /\ SetStatus(i, "Completed")
            /\ version' = version + 1
            /\ UNCHANGED <<cfg, observedAt, paused, base, k0>>
       ELSE Release(i)
    /\ Step("settle", c, i, Rec(i).recipe, Rec(i).units, 0, done, 0, 0)

SetPaused(c, b) ==
    /\ PauseErr(c, b) = "Ok"
    /\ paused' = b
    /\ version' = version + 1
    /\ UNCHANGED <<cfg, values, observedAt, records, base, k0>>
    /\ Step("pause", c, 0, 0, 0, 0, b, 0, 0)

Observe(c, vals, now) ==
    /\ ObserveErr(c, vals, now) = "Ok"
    /\ values' = vals
    /\ observedAt' = now
    /\ version' = version + 1
    /\ base' = vals
    /\ k0' = NR
    /\ UNCHANGED <<cfg, paused, records>>
    /\ Step("observe", c, 0, 0, 0, 0, FALSE, now, 0)

-----------------------------------------------------------------------------
(* Every call any party can make, over the argument domains. Record ids    *)
(* and recipes range one past the end, units one past max_units, request   *)
(* versions over {version, version + 1} (any other value behaves as the    *)
(* latter: the core compares it only for equality), so every guard stays   *)
(* reachable for the step properties.                                      *)

SubmitNext  == \E c \in Accounts, r \in 0 .. NRcp, u \in 0 .. MaxU + 1,
                  v \in {version, version + 1}, now \in Times, d \in ExpOffsets :
                  Submit(c, r, u, v, now + d, now)
DispatchNext == \E c \in Accounts, i \in 0 .. NR, now \in Times : Dispatch(c, i, now)
AckNext     == \E i \in 0 .. NR, b \in BOOLEAN : Ack(i, b)
CancelNext  == \E c \in Accounts, i \in 0 .. NR, now \in Times : Cancel(c, i, now)
SettleNext  == \E c \in Accounts, i \in 0 .. NR, b \in BOOLEAN : Settle(c, i, b)
PauseNext   == \E c \in Accounts, b \in BOOLEAN : SetPaused(c, b)
ObserveNext == \E c \in Accounts, vals \in Observations, now \in Times : Observe(c, vals, now)

Next ==
    \/ SubmitNext \/ DispatchNext \/ AckNext \/ CancelNext
    \/ SettleNext \/ PauseNext \/ ObserveNext

=============================================================================
