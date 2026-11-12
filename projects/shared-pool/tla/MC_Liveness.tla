---------------------------- MODULE MC_Liveness ----------------------------
(***************************************************************************)
(* LIVE-2: every dispatched record eventually ends (Completed or           *)
(* Cancelled), under weak fairness of the executor. What "fairness of the  *)
(* executor" means decides the answer, so each config fixes it:            *)
(*                                                                         *)
(*   TLA-LIVE-1  the completion path (MC_Liveness.cfg, universe MCConfig;  *)
(*               MC_Liveness_F2Done.cfg, universe CreditHedgeConfig):      *)
(*               observes stay inside [min, max] and the executor is       *)
(*               weakly fair to COMPLETING each record (SettleDone):       *)
(*               LIVE-2 holds. This is close to the fairness premise:      *)
(*               LIVE-1 (Props.tla, an invariant) says settle(true) is Ok  *)
(*               for every in-flight record while B = 0, so WF of it ends  *)
(*               the record. The check adds that LIVE-1 holds in every     *)
(*               reachable state and nothing else keeps a record open. It  *)
(*               says nothing about an executor that reports nonexecution  *)
(*               (that is TLA-LIVE-F2).                                    *)
(*               MC_Liveness_Unfair.cfg: without fairness LIVE-2 fails.    *)
(*   TLA-LIVE-F1 (MC_Liveness_F1.cfg) one disturbing observe is allowed,   *)
(*               and the executor is weakly fair to settling each record   *)
(*               either way (SettleAny): LIVE-2 must FAIL (finding F-1).   *)
(*               MC_Liveness_F1Shape.cfg: Live2F1 holds, i.e. every        *)
(*               counterexample is the F-1 wedge: a record that stays in   *)
(*               flight is eventually forever Wedged (both settles fail    *)
(*               Bounds, cancel Pending, observe Pending, B # 0).          *)
(*   TLA-LIVE-F2 (MC_Liveness_F2.cfg, universe CreditHedgeConfig) only     *)
(*               in-bounds observes (B = 0 throughout), the executor is    *)
(*               weakly fair to reporting NONEXECUTION (SettleFalse: the   *)
(*               honest settle(false) of ASM-EXEC) and actors/owner are    *)
(*               weakly fair to cancelling Reserved records: LIVE-2 must   *)
(*               FAIL (finding F-2). MC_Liveness_F2Shape.cfg: Live2F2      *)
(*               holds, i.e. every counterexample is the F-2 wedge: a      *)
(*               record that stays in flight is eventually forever         *)
(*               WedgedRelease (settle(false) Bounds because a completed   *)
(*               sibling relied on its reservation, settle(true) Ok,       *)
(*               cancel Pending, observe Pending, B = 0).                  *)
(*               Weak fairness of SettleAny would not show F-2: in the     *)
(*               wedge settle(true) stays enabled (LIVE-1), so WF forces   *)
(*               it, i.e. the executor escapes only by attesting a         *)
(*               completion that did not happen.                           *)
(*                                                                         *)
(* Bounds are in the actions, not a CONSTRAINT or VIEW, so TLC's liveness  *)
(* check is sound: submit, pause and observe only while version < VB, and  *)
(* MaxRecords records, so every behaviour has finitely many effective      *)
(* steps (then stutters). Settle, ack, dispatch and cancel are unbounded.  *)
(* Scaled (C-5): MaxRecords 2 (real 256), VB 4; 1-2 metrics, 2 recipes.    *)
(***************************************************************************)
EXTENDS MCCommon

CONSTANTS
    VB,
    \* The configuration of the universe (MCConfig or CreditHedgeConfig).
    LCfg

LInit == InitFrom(LCfg, 0)

LNext ==
    \/ version < VB /\ (SubmitNext \/ PauseNext \/ ObserveNext)
    \/ DispatchNext \/ AckNext \/ CancelNext \/ SettleNext

RecIds == 0 .. MaxRecords - 1
InFlightRec(i) == i < NR /\ InFlight(Rec(i).status)
TerminalRec(i) == i < NR /\ ~Open(Rec(i).status)

\* The executor completes record i / reports its nonexecution / settles it
\* either way; some caller cancels it (only a Reserved record can be).
SettleDone(i)  == i < NR /\ \E x \in Accounts : Settle(x, i, TRUE)
SettleFalse(i) == i < NR /\ \E x \in Accounts : Settle(x, i, FALSE)
SettleAny(i)   == i < NR /\ \E x \in Accounts, b \in BOOLEAN : Settle(x, i, b)
CancelAny(i)   == i < NR /\ \E c \in Accounts, now \in Times : Cancel(c, i, now)

\* PROP: TLA-LIVE-1
\* (the completion path)
LiveSpec   == LInit /\ [][LNext]_vars /\ \A i \in RecIds : WF_vars(SettleDone(i))
UnfairSpec == LInit /\ [][LNext]_vars
\* PROP: TLA-LIVE-F1
F1Spec     == LInit /\ [][LNext]_vars /\ \A i \in RecIds : WF_vars(SettleAny(i))
\* PROP: TLA-LIVE-F2
F2Spec     == LInit /\ [][LNext]_vars
                    /\ \A i \in RecIds : WF_vars(SettleFalse(i)) /\ WF_vars(CancelAny(i))

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

\* PROP: TLA-LIVE-F1
\* (LIVE-2 fails only by the F-1 wedge)
Live2F1 == \A i \in RecIds : (<>[]InFlightRec(i)) => <>[]Wedged(i)

\* F-2's shape, with no disturbance (B = 0): the honest nonexecution report
\* fails Bounds because undoing the record's reservation alone takes a
\* metric out of [min, max], and a sibling record has Completed (its
\* completion relied on that reservation); the record cannot be cancelled,
\* the pool cannot be re-observed; only an attestation of completion
\* (settle(true), Ok by LIVE-1) would end it.
WedgedRelease(i) ==
    /\ InFlightRec(i)
    /\ SettleErr(RecRcp(i).executor, i, FALSE) = "Bounds"
    /\ SettleErr(RecRcp(i).executor, i, TRUE) = "Ok"
    /\ CancelErr(cfg.owner, i, 0) = "Pending"
    /\ CancelErr(RecRcp(i).actor, i, 0) = "Pending"
    /\ ObserveErr(cfg.owner, values, 0) = "Pending"
    /\ Healthy
    /\ \E m \in MIdx : PV(AddVec(values, Neg(RecRcp(i).reserve), Rec(i).units), m) > 0
    /\ \E j \in 0 .. NR - 1 : j # i /\ Rec(j).status = "Completed"

\* PROP: TLA-LIVE-F2
\* (LIVE-2 fails only by the F-2 wedge in this universe)
Live2F2 == \A i \in RecIds : (<>[]InFlightRec(i)) => <>[]WedgedRelease(i)
=============================================================================
