---------------------------- MODULE MC_Safety ----------------------------
(* TLC model for the safety run (TLA-SAFE): every reachable state with at  *)
(* most MaxReq requests. Accounts and keys are symmetric model values,     *)
(* sound by ASM-IDENT parametricity (A4).                                  *)
EXTENDS ApprovalProps, TLC

CONSTANTS a1, a2, k1, k2, MaxReq

MCAccounts == {Owner, a1, a2}
MCKeys == {k1, k2}
Sym == Permutations({a1, a2}) \cup Permutations(MCKeys)

Bound == NR <= MaxReq

\* The epoch ghost grows without bound, but every property reads it only as
\* "ghost[i].ep = epoch[key of i]", and that comparison evolves the same way
\* from any two states that agree on it (epochs only increase, and a new
\* request takes the current epoch). So fingerprinting states by this view
\* is a bisimulation quotient: no behaviour is lost, and the graph is finite.
GhostView == [i \in Ids |-> [same |-> ghost[i + 1].ep = epoch[Req(i).key],
                              cont |-> ghost[i + 1].cont, apprOk |-> ghost[i + 1].apprOk]]
View == <<principals, requests, log, GhostView>>
=============================================================================
