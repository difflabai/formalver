--------------------------- MODULE ApprovalProps ---------------------------
(***************************************************************************)
(* Properties of ApprovalCore. IDs are the strategy.md catalogue's; the    *)
(* TLA+ check of each is listed in strategy.md section 17.3.              *)
(***************************************************************************)
EXTENDS ApprovalCore

\* Written as predicates, not set membership, so Apalache can use TypeOK in
\* the inductive invariant (no infinite sets of records or sequences).
TypeOK ==
    /\ DOMAIN principals = Keys
    /\ \A k \in Keys:
        LET p == principals[k] IN
        /\ p.reg \in BOOLEAN /\ p.acct \in Accounts /\ p.role \in Roles
        /\ p.from >= 0 /\ p.pending >= 0
        /\ ~p.reg => p = NoPrincipal
    /\ \A i \in Ids:
        LET r == Req(i) IN
        /\ r.acct \in Accounts /\ r.key \in Keys /\ r.act \in Payloads
        /\ r.appr \in BOOLEAN /\ r.aidx >= 0 /\ r.aacct \in Accounts /\ r.akey \in Keys
        /\ ~r.appr => (r.aidx = 0 /\ r.aacct = r.acct /\ r.akey = r.key)
    /\ \A j \in DOMAIN log: log[j] >= 0
    /\ DOMAIN epoch = Keys /\ \A k \in Keys: epoch[k] >= 0
    /\ Len(ghost) = NR
    /\ \A i \in Ids: ghost[i + 1].ep \in 0 .. epoch[Req(i).key]

\* INV-2: stored actions are non-empty and short (the type says Payloads).
\* INV-3: log -> request.
Inv3 == \A j \in DOMAIN log: log[j] \in Ids /\ Req(log[j]).appr /\ Req(log[j]).aidx = j - 1
\* INV-4: request -> log.
Inv4 == \A i \in Ids: Req(i).appr => Req(i).aidx \in 0 .. NL - 1 /\ log[Req(i).aidx + 1] = i
\* INV-5: separation of duties.
Inv5 == \A i \in Ids: Req(i).appr => Req(i).aacct # Req(i).acct
\* INV-6: approver key differs from agent key.
Inv6 == \A i \in Ids: Req(i).appr => Req(i).akey # Req(i).key
\* INV-7: registration bound.
Inv7 == \A k \in Keys: principals[k].reg => principals[k].from <= NR
\* INV-8: registration provenance.
Inv8 == \A k \in Keys, i \in Ids:
            (principals[k].reg /\ Req(i).key = k /\ i >= principals[k].from)
                => (Req(i).acct = principals[k].acct /\ principals[k].role = "Agent")
\* INV-9: pending count, and the cap.
Inv9 == \A k \in Keys: principals[k].reg =>
            principals[k].pending = Pend(k) /\ principals[k].pending <= MaxPending
\* LEM-1: no duplicates in the log. LEM-2: log length = approved count.
Lem1 == \A j1, j2 \in DOMAIN log: j1 # j2 => log[j1] # log[j2]
Lem2 == NL = Cardinality({i \in Ids : Req(i).appr})

\* TR-1 provenance, through the ghost. Every approved request was made by an
\* Agent key of its account whose registration was never removed before the
\* approval (the request is made only under such a registration: TX-3), and
\* approved by an Approver key of a different account (INV-5).
Provenance == \A i \in Ids: Req(i).appr => ghost[i + 1].cont /\ ghost[i + 1].apprOk
\* The ghost agrees with Live for unapproved requests: the core's
\* active_from check decides exactly "not revoked since the request".
GhostLive == \A i \in Ids: ~Req(i).appr => ((ghost[i + 1].ep = epoch[Req(i).key]) <=> Live(i))

\* L2 (TLA-LIVE-2), approvability: a pending request can be approved by any
\* approver key of another account, so nothing in the core leaves it stuck.
EligibleKey(i, k) ==
    principals[k].reg /\ principals[k].role = "Approver" /\ principals[k].acct # Req(i).acct
Approvable ==
    \A i \in Ids, k \in Keys: (Pending(i) /\ EligibleKey(i, k)) =>
        ApproveErr(principals[k].acct, principals[k].acct, k, i, Req(i).act) = "Ok"

Inv ==
    /\ TypeOK /\ Inv3 /\ Inv4 /\ Inv5 /\ Inv6 /\ Inv7 /\ Inv8 /\ Inv9
    /\ Lem1 /\ Lem2 /\ Provenance /\ GhostLive /\ Approvable

-----------------------------------------------------------------------------
(* Action properties, checked as [][P]_vars                                *)

\* HIST-1: request content is immutable and never removed.
Hist1 == NR' >= NR /\ \A i \in Ids:
            /\ requests'[i + 1].acct = Req(i).acct /\ requests'[i + 1].key = Req(i).key
            /\ requests'[i + 1].act = Req(i).act
\* HIST-2: approvals are immutable. TR-2: so each request is approved once.
Hist2 == \A i \in Ids: Req(i).appr => requests'[i + 1] = Req(i)
\* HIST-3: the log is append-only.
Hist3 == NL' >= NL /\ SubSeq(log', 1, NL) = log
\* HIST-8 / TR-3, durable revocation: Void is terminal, even across a revoke
\* and re-add of the same key, account and role. Equivalent to
\* \A i: [](Void(i) => []Void(i)) since stuttering preserves Void(i).
Hist8 == \A i \in Ids: Void(i) => Void(i)'
\* HIST-7: the owner can't rewrite history.
Hist7 == (principals' # principals /\ requests' = requests) => log' = log

StepProps == Hist1 /\ Hist2 /\ Hist3 /\ Hist7 /\ Hist8
StepProperty == [][StepProps]_vars

-----------------------------------------------------------------------------
(* Non-vacuity (TR-5): each of these must be reachable, so the checker     *)
(* runs them as invariants that must FAIL (run-tla.sh inverts them).       *)

Witness_Approved == ~\E i \in Ids: Approved(i)
Witness_Void == ~\E i \in Ids: Void(i)
\* Revoked, re-added to the same account and role, and still void.
Witness_Revival == ~\E i \in Ids: Void(i) /\ principals[Req(i).key].reg
                        /\ principals[Req(i).key].acct = Req(i).acct
                        /\ principals[Req(i).key].role = "Agent"
Witness_Cap == ~\E k \in Keys: principals[k].reg /\ principals[k].pending = MaxPending

=============================================================================
