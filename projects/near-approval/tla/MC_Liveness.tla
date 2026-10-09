--------------------------- MODULE MC_Liveness ---------------------------
(***************************************************************************)
(* TLA-LIVE-1 (strategy.md section 17.3). The contract has no internal     *)
(* progress: a request leaves Pending only when an approver approves or    *)
(* rejects it, or the owner revokes its agent key. So the liveness         *)
(* property is conditional on the environment:                             *)
(*                                                                         *)
(*   if, from some point on, the request always has an eligible approver   *)
(*   (an Approver key of another account), and approvers are weakly fair   *)
(*   (an approval that stays possible eventually happens), then every      *)
(*   pending request is eventually approved, rejected or void.             *)
(*                                                                         *)
(* Approvable (TLA-LIVE-2, in Inv) is what makes this hold: the core never *)
(* refuses an eligible approver of a pending request. Fairness is on       *)
(* approval only, so progress never depends on a rejection. Bounds are in  *)
(* the actions, not a CONSTRAINT, so that TLC's liveness check is sound,   *)
(* and there is no SYMMETRY or VIEW, for the same reason. MaxReg bounds    *)
(* registrations, and with them the ids.                                   *)
(***************************************************************************)
EXTENDS ApprovalProps, TLC

CONSTANTS a1, a2, k1, k2, MaxReq, MaxReg

MCAccounts == {Owner, a1, a2}
MCKeys == {k1, k2}
ReqIds == 0 .. MaxReq - 1

BNext ==
    \/ \E c \in Accounts, k \in Keys, a \in Accounts, r \in Roles: regs < MaxReg /\ AddPrincipal(c, k, a, r)
    \/ \E c \in Accounts, k \in Keys: RevokeKey(c, k)
    \/ \E p, s \in Accounts, k \in Keys, x \in Actions: NR < MaxReq /\ RequestAction(p, s, k, x)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}, x \in Actions: Approve(p, s, k, i, x)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}: Reject(p, s, k, i)

\* Some approver approves request i, with its action.
ApproveReq(i) == i \in Ids /\ \E s \in Accounts, k \in Keys: Approve(s, s, k, i, Req(i).act)

Eligible(i) == i \in Ids /\ \E k \in Keys: EligibleKey(i, k)

LiveSpec == Init /\ [][BNext]_vars /\ \A i \in ReqIds: WF_vars(ApproveReq(i))
\* The same without fairness: TLA-LIVE-1 must FAIL here (non-vacuity).
UnfairSpec == Init /\ [][BNext]_vars

Live1 == \A i \in ReqIds: (<>[]Eligible(i)) => [](Pending(i) => <>~Pending(i))
=============================================================================
