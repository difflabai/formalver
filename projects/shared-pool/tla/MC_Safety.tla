----------------------------- MODULE MC_Safety -----------------------------
(***************************************************************************)
(* TLA-SAFE: every reachable state and step of the MCCommon universe.      *)
(* Times {0, 1, 2}, chosen freely per call (a superset of monotone block   *)
(* time, ASM-TIME); expiry offsets {0, 1, 2, 86400, 86401} reach both      *)
(* Expired branches and the window boundary; AllObservations; MaxRecords   *)
(* = 3 (scaled from 256).                                                  *)
(*                                                                         *)
(* VIEW. version and steps grow without bound (pause and observe bump      *)
(* version forever). The model reads version only in `v = version` (Next   *)
(* offers v in {version, version + 1}) and in the bump's overflow check,   *)
(* which no explored state reaches (MaxVersion = 2^31 - 1), and no         *)
(* invariant reads last. So states that differ only in version, steps and  *)
(* last have the same successors up to those fields, and fingerprinting by *)
(* View is a bisimulation quotient for every invariant (INV-VER through    *)
(* version - steps). TLC checks step properties on every transition, also  *)
(* into a state whose view it has seen, so they and the step witnesses     *)
(* see the real last'.                                                     *)
(***************************************************************************)
EXTENDS MCCommon

Spec == Init /\ [][Next]_vars

View == <<values, observedAt, paused, records, base, k0, version - steps>>
=============================================================================
