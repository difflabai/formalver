---------------------------- MODULE MC_Graph ----------------------------
(***************************************************************************)
(* MC-3 (strategy.md section 17.5): the labelled reachable graph of one    *)
(* small universe, for comparison with the Prolog requirements model by    *)
(* tools/scripts/mc3.py. Two TLC runs over this module:                    *)
(*                                                                         *)
(*   MC_Graph.cfg        every successful call is a step, and the history  *)
(*                       variables prev and lastOp make each TLC state one *)
(*                       edge (store, call, store'); TLC -dump writes them *)
(*   MC_GraphTable.cfg   VIEW store: one state per store, and the Table    *)
(*                       invariant prints the result of every call there,  *)
(*                       the rejected ones included (a rejected call is a  *)
(*                       self-loop labelled with its error)                *)
(*                                                                         *)
(* Bounds are in the actions: a successful call that would grow the store  *)
(* past MaxReq requests or MaxReg registrations is not taken (its table    *)
(* entry still says "Ok"). No SYMMETRY: the graph is the literal one.      *)
(***************************************************************************)
EXTENDS ApprovalCore, TLC

CONSTANTS a1, a2, k1, k2, MaxReq, MaxReg

VARIABLES prev, lastOp

MCAccounts == {Owner, a1, a2}
MCKeys == {k1, k2}

gvars == <<vars, prev, lastOp>>

Step(op, args) == prev' = store /\ lastOp' = <<op, args>>

GInit == Init /\ prev = <<>> /\ lastOp = <<"init", <<>>>>

GNext ==
    \/ \E c \in Accounts, k \in Keys, a \in Accounts, r \in Roles:
         regs < MaxReg /\ AddPrincipal(c, k, a, r) /\ Step("add", <<c, k, a, r>>)
    \/ \E c \in Accounts, k \in Keys:
         RevokeKey(c, k) /\ Step("revoke", <<c, k>>)
    \/ \E p, s \in Accounts, k \in Keys, x \in Actions:
         NR < MaxReq /\ RequestAction(p, s, k, x) /\ Step("request", <<p, s, k, x>>)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}, x \in Actions:
         Approve(p, s, k, i, x) /\ Step("approve", <<p, s, k, i, x>>)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}:
         Reject(p, s, k, i) /\ Step("reject", <<p, s, k, i>>)

GSpec == GInit /\ [][GNext]_gvars

\* The table run: one state per store.
StoreView == store

\* Every call and its result in the current store.
Results ==
    {<<<<"add", c, k, a, r>>, AddErr(c, k)>> : c \in Accounts, k \in Keys, a \in Accounts, r \in Roles}
    \cup {<<<<"revoke", c, k>>, RevokeErr(c, k)>> : c \in Accounts, k \in Keys}
    \cup {<<<<"request", p, s, k, x>>, RequestErr(p, s, k, x)>> :
            p \in Accounts, s \in Accounts, k \in Keys, x \in Actions}
    \cup {<<<<"approve", p, s, k, i, x>>, ApproveErr(p, s, k, i, x)>> :
            p \in Accounts, s \in Accounts, k \in Keys, i \in Ids \cup {NR}, x \in Actions}
    \cup {<<<<"reject", p, s, k, i>>, RejectErr(p, s, k, i)>> :
            p \in Accounts, s \in Accounts, k \in Keys, i \in Ids \cup {NR}}

\* Prints the store and the calls it rejects, with their errors (every call
\* not listed is "Ok"). Always TRUE.
Table == PrintT(<<"TABLE", store, {e \in Results : e[2] # "Ok"}>>)
=============================================================================
