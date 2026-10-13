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

\* Registration ids grow without bound (every add takes a fresh one), but
\* the core never reads their values: it only copies them. The properties
\* compare them only for equality and order, and a new id is always above
\* every existing one. So two states that agree up to an order-preserving
\* renaming of the ids they hold behave the same, and fingerprinting states
\* by their rank form is a bisimulation quotient for everything the
\* actions and properties read: the graph is finite and no behaviour is
\* lost. regs and the revoked ids no state field refers to are dropped from
\* the view; Inv11/12/14/15, which read them, are also proved inductive by
\* Apalache with nothing dropped (TLA-IND).
Seen ==
    {principals[k].rid : k \in {k \in Keys : principals[k].reg}}
    \cup {Req(i).rid : i \in Ids}
    \cup {Req(i).arid : i \in {i \in Ids : Req(i).appr}}
    \cup {Req(i).rrid : i \in {i \in Ids : Req(i).rj}}
Rank(g) == Cardinality({h \in Seen : h < g})
View ==
    <<[k \in Keys |-> [principals[k] EXCEPT !.rid = Rank(@)]],
      [j \in DOMAIN requests |->
          [requests[j] EXCEPT !.rid = Rank(@), !.arid = Rank(@), !.rrid = Rank(@)]],
      log,
      {Rank(g) : g \in revoked \cap Seen},
      ghost>>
=============================================================================
