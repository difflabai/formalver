---------------------------- MODULE MC_Liveness ----------------------------
(***************************************************************************)
(* LIVE-2: every dispatched record eventually ends (Completed or           *)
(* Cancelled), under weak fairness of the executor.                        *)
(*                                                                         *)
(*   TLA-LIVE-1  (MC_Liveness.cfg) observes stay inside [min, max], and    *)
(*               the executor is weakly fair to completing each record:    *)
(*               LIVE-2 holds. Progress never relies on a cancellation.    *)
(*               MC_Liveness_Unfair.cfg: without fairness LIVE-2 fails.    *)
(*   TLA-LIVE-F1 (MC_Liveness_F1.cfg) one disturbing observe is allowed,   *)
(*               and the executor is weakly fair to settling each record   *)
(*               either way: LIVE-2 must FAIL (finding F-1).               *)
(*               MC_Liveness_F1Shape.cfg: Live2F1 holds, i.e. every        *)
(*               counterexample is the F-1 wedge: a record that stays in   *)
(*               flight is eventually forever Wedged (both settles fail    *)
(*               Bounds, cancel Pending, observe Pending, B # 0).          *)
(*                                                                         *)
(* Bounds are in the actions, not a CONSTRAINT or VIEW, so TLC's liveness  *)
(* check is sound: submit, pause and observe only while version < VB, and  *)
(* MaxRecords records, so every behaviour has finitely many effective      *)
(* steps (then stutters). Settle, ack, dispatch and cancel are unbounded.  *)
(***************************************************************************)
EXTENDS MCCommon

CONSTANT VB

LNext ==
    \/ version < VB /\ (SubmitNext \/ PauseNext \/ ObserveNext)
    \/ DispatchNext \/ AckNext \/ CancelNext \/ SettleNext

RecIds == 0 .. MaxRecords - 1
InFlightRec(i) == i < NR /\ InFlight(Rec(i).status)
TerminalRec(i) == i < NR /\ ~Open(Rec(i).status)

\* The executor completes record i / settles it either way.
SettleDone(i) == i < NR /\ \E x \in Accounts : Settle(x, i, TRUE)
SettleAny(i)  == i < NR /\ \E x \in Accounts, b \in BOOLEAN : Settle(x, i, b)

LiveSpec   == Init /\ [][LNext]_vars /\ \A i \in RecIds : WF_vars(SettleDone(i))
UnfairSpec == Init /\ [][LNext]_vars
F1Spec     == Init /\ [][LNext]_vars /\ \A i \in RecIds : WF_vars(SettleAny(i))

\* PROP: LIVE-2
Live2 == \A i \in RecIds : [](InFlightRec(i) => <>TerminalRec(i))

\* F-1's shape: neither settle can resolve the record, it cannot be
\* cancelled, the pool cannot be re-observed, and an observe disturbed it.
Wedged(i) ==
    /\ InFlightRec(i)
    /\ SettleErr(RecRcp(i).executor, i, TRUE) = "Bounds"
    /\ SettleErr(RecRcp(i).executor, i, FALSE) = "Bounds"
    /\ CancelErr(cfg.owner, i, 0) = "Pending"
    /\ CancelErr(RecRcp(i).actor, i, 0) = "Pending"
    /\ ObserveErr(cfg.owner, values, 0) = "Pending"
    /\ ~Healthy

\* PROP: LIVE-2 fails only by F-1.
Live2F1 == \A i \in RecIds : (<>[]InFlightRec(i)) => <>[]Wedged(i)
=============================================================================
