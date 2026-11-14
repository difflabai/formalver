------------------------------ MODULE MCCommon ------------------------------
(***************************************************************************)
(* The small universes shared by the TLC models.                           *)
(*                                                                         *)
(* MCConfig (the brief's F-1 wedge with its ranges scaled down; MC_Safety  *)
(* and the F-1 / completion-path liveness checks):                         *)
(*   metrics  m0 in [0, 2] (initial 1), m1 in [-2, 2] (initial 1)          *)
(*   terms    t(1, target 0, weight 1)                                     *)
(*   recipes  r0 = hedge:  actor a1, executor x1, reserve [-1, 0],         *)
(*                         complete [1, -1], max_units 1                   *)
(*            r1 = follow: actor a1, executor x1, reserve [1, -1],         *)
(*                         complete [-1, 0], max_units 2, requires r0 x 1  *)
(*   max_age 1 (SnapshotExpired reachable)                                 *)
(*                                                                         *)
(* CreditHedgeConfig (finding F-2, the supplied `risk` fixture's credit    *)
(* position and selloff hedge scaled down; the MC_Liveness_F2 configs):    *)
(*   metrics  m0 "selloff loss" in [0, 2] (initial 1)                      *)
(*   terms    t(0, target 2, weight 1, excess): no energy inside bounds,   *)
(*            as the fixture's excess targets above the initial losses     *)
(*   recipes  r0 = credit: actor a1, executor x1, reserve [1],             *)
(*                         complete [0], max_units 1                       *)
(*                         (fixture: reserve +20 on loss, complete 0)      *)
(*            r1 = hedge:  actor a1, executor x1, reserve [0],             *)
(*                         complete [-2], max_units 1                      *)
(*                         (fixture: complete -10 x 8 units on loss)       *)
(*   max_age 0                                                             *)
(* From m0 = 1 the hedge alone is Bounds (envelope low 1 - 2 < 0); after   *)
(* the credit's reservation (m0 = 2) it is admitted (low 0): the hedge's   *)
(* completion relies on the credit's reservation. Once the hedge has       *)
(* completed (m0 = 0), releasing the credit (m0 = -1) fails Bounds.        *)
(*                                                                         *)
(* Accounts o (owner), a1 (actor), x1 (executor), z (stranger).            *)
(***************************************************************************)
EXTENDS Props, TLC

MCConfig ==
    [owner |-> "o", maxAge |-> 1,
     metrics |-> <<[min |-> 0, max |-> 2, init |-> 1], [min |-> -2, max |-> 2, init |-> 1]>>,
     terms |-> <<[metric |-> 1, target |-> 0, weight |-> 1, shape |-> "target"]>>,
     recipes |->
        <<[actor |-> "a1", executor |-> "x1", reserve |-> <<-1, 0>>, complete |-> <<1, -1>>,
           maxUnits |-> 1, requires |-> <<>>],
          [actor |-> "a1", executor |-> "x1", reserve |-> <<1, -1>>, complete |-> <<-1, 0>>,
           maxUnits |-> 2, requires |-> <<<<0, 1>>>>]>>]

ASSUME ValidCfg(MCConfig)

CreditHedgeConfig ==
    [owner |-> "o", maxAge |-> 0,
     metrics |-> <<[min |-> 0, max |-> 2, init |-> 1]>>,
     terms |-> <<[metric |-> 0, target |-> 2, weight |-> 1, shape |-> "excess"]>>,
     recipes |->
        <<[actor |-> "a1", executor |-> "x1", reserve |-> <<1>>, complete |-> <<0>>,
           maxUnits |-> 1, requires |-> <<>>],
          [actor |-> "a1", executor |-> "x1", reserve |-> <<0>>, complete |-> <<-2>>,
           maxUnits |-> 1, requires |-> <<>>]>>]

ASSUME ValidCfg(CreditHedgeConfig)

\* Every vector over {-1, 0, 2, 3} x {-2, 0, 2}: m0 = -1 and m0 = 3 are out
\* of bounds (a disturbing observe); plus a short vector and one beyond
\* MAX_VALUE (both Bounds).
AllObservations ==
    {<<a, b>> : a \in {-1, 0, 2, 3}, b \in {-2, 0, 2}} \cup {<<0>>, <<1000001, 0>>}
\* Observations inside [min, max] only: B stays 0.
HealthyObservations == {<<a, b>> : a \in {0, 2}, b \in {-2, 0, 2}}
\* Plus the disturbing observe that sets up F-1 (m0 = 3 > max 2).
DisturbingObservations == HealthyObservations \cup {<<3, 2>>}
\* CreditHedgeConfig: every in-bounds vector (B stays 0; no disturbing
\* observe, so F-1 cannot occur).
CreditHedgeObservations == {<<a>> : a \in 0 .. 2}

Init == InitFrom(MCConfig, 0)
=============================================================================
