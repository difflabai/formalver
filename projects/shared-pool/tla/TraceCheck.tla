---------------------------- MODULE TraceCheck ----------------------------
(***************************************************************************)
(* REF-5, trace validation. build/TraceData.tla holds the conformance      *)
(* traces of the real pool-core (conformance/traces/core.txt, converted by *)
(* trace2tla.py). TLC starts each trace from Pool::new of its config and   *)
(* replays it call by call: a call is accepted only if the model's error   *)
(* operator gives the core's result (an effective "Ok" or an idempotent    *)
(* "Noop" for the core's Ok; submit's id is the record count) and the      *)
(* model's post-state equals the core's. A rejected step has no successor, *)
(* which TLC reports as a deadlock, so CHECK_DEADLOCK is on and a finished *)
(* trace stutters explicitly. Inv (all invariants but the subset-          *)
(* enumerating INV-HEALTHY) and StepProperty are checked on every state    *)
(* and step of the real core as well.                                     *)
(***************************************************************************)
EXTENDS Props, TraceData, TLC

VARIABLES tr, pos

tvars == <<cfg, values, version, observedAt, paused, records, base, k0, steps, last, tr, pos>>

T == Traces[tr]

\* The model state equals a recorded core state (unprimed / primed).
Is(s) ==
    /\ values = s.values /\ version = s.version /\ observedAt = s.observedAt
    /\ paused = s.paused /\ records = s.records
Post(s) ==
    /\ values' = s.values /\ version' = s.version /\ observedAt' = s.observedAt
    /\ paused' = s.paused /\ records' = s.records

TInit ==
    /\ tr \in 1 .. Len(Traces)
    /\ pos = 0
    /\ InitFrom(Traces[tr].cfg, Traces[tr].t0)
    /\ ValidCfg(cfg)
    /\ Is(Traces[tr].init)

ErrOf(e) ==
    CASE e.op = "submit"   -> SubmitErr(e.c, e.r, e.u, e.v, e.exp, e.now)
      [] e.op = "dispatch" -> DispatchErr(e.c, e.i, e.now)
      [] e.op = "ack"      -> AckErr(e.i, e.b)
      [] e.op = "cancel"   -> CancelErr(e.c, e.i, e.now)
      [] e.op = "settle"   -> SettleErr(e.c, e.i, e.b)
      [] e.op = "pause"    -> PauseErr(e.c, e.b)
      [] e.op = "observe"  -> ObserveErr(e.c, e.vals, e.now)

Act(e) ==
    CASE e.op = "submit"   -> Submit(e.c, e.r, e.u, e.v, e.exp, e.now)
      [] e.op = "dispatch" -> Dispatch(e.c, e.i, e.now)
      [] e.op = "ack"      -> Ack(e.i, e.b)
      [] e.op = "cancel"   -> Cancel(e.c, e.i, e.now)
      [] e.op = "settle"   -> Settle(e.c, e.i, e.b)
      [] e.op = "pause"    -> SetPaused(e.c, e.b)
      [] e.op = "observe"  -> Observe(e.c, e.vals, e.now)

\* The model's result agrees with the core's.
Agrees(err, e) ==
    IF e.res = "Ok"
    THEN err \in {"Ok", "Noop"} /\ (e.op = "submit" => e.id = NR)
    ELSE err = e.res

Replay(e) ==
    LET err == ErrOf(e) IN
    /\ Agrees(err, e)
    /\ IF err = "Ok" THEN Act(e) ELSE UNCHANGED vars

TNext ==
    \/ /\ pos < Len(T.steps)
       /\ Replay(T.steps[pos + 1])
       /\ Post(T.steps[pos + 1].post)
       /\ pos' = pos + 1
       /\ UNCHANGED tr
    \/ /\ pos = Len(T.steps)
       /\ UNCHANGED tvars

TSpec == TInit /\ [][TNext]_tvars /\ WF_tvars(TNext)

\* Every trace is replayed to its end (a rejected step is already a
\* deadlock error; this makes the goal explicit).
Done == <>(pos = Len(T.steps))
=============================================================================
