------------------------------ MODULE MCCommon ------------------------------
(***************************************************************************)
(* The small universe shared by the TLC models.                            *)
(*                                                                         *)
(* Config (the brief's F-1 wedge with its ranges scaled down):             *)
(*   metrics  m0 in [0, 2] (initial 1), m1 in [-2, 2] (initial 1)          *)
(*   terms    t(1, target 0, weight 1)                                      *)
(*   recipes  r0 = hedge:  actor a1, executor x1, reserve [-1, 0],          *)
(*                         complete [1, -1], max_units 1                    *)
(*            r1 = follow: actor a1, executor x1, reserve [1, -1],          *)
(*                         complete [-1, 0], max_units 2, requires r0 x 1   *)
(*   max_age 1 (SnapshotExpired reachable)                                  *)
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

\* Every vector over {-1, 0, 2, 3} x {-2, 0, 2}: m0 = -1 and m0 = 3 are out
\* of bounds (a disturbing observe); plus a short vector and one beyond
\* MAX_VALUE (both Bounds).
AllObservations ==
    {<<a, b>> : a \in {-1, 0, 2, 3}, b \in {-2, 0, 2}} \cup {<<0>>, <<1000001, 0>>}
\* Observations inside [min, max] only: B stays 0.
HealthyObservations == {<<a, b>> : a \in {0, 2}, b \in {-2, 0, 2}}
\* Plus the disturbing observe that sets up F-1 (m0 = 3 > max 2).
DisturbingObservations == HealthyObservations \cup {<<3, 2>>}

Init == InitFrom(MCConfig, 0)
=============================================================================
