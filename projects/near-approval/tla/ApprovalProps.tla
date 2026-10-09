--------------------------- MODULE ApprovalProps ---------------------------
(***************************************************************************)
(* Properties of ApprovalCore. IDs are the strategy.md catalogue's; the    *)
(* TLA+ check of each is listed in strategy.md section 17.3.               *)
(***************************************************************************)
EXTENDS ApprovalCore

\* Written as predicates, not set membership, so Apalache can use TypeOK in
\* the inductive invariant (no infinite sets of records or sequences).
TypeOK ==
    /\ DOMAIN principals = Keys
    /\ \A k \in Keys:
        LET p == principals[k] IN
        /\ p.reg \in BOOLEAN /\ p.acct \in Accounts /\ p.role \in Roles
        /\ p.rid >= 0 /\ p.from >= 0 /\ p.pending >= 0
        /\ ~p.reg => p = NoPrincipal
    /\ \A i \in Ids:
        LET r == Req(i) IN
        /\ r.acct \in Accounts /\ r.key \in Keys /\ r.rid >= 0 /\ r.act \in Payloads
        /\ r.appr \in BOOLEAN /\ r.aidx >= 0 /\ r.aacct \in Accounts /\ r.akey \in Keys
        /\ r.arid >= 0
        /\ ~r.appr => (r.aidx = 0 /\ r.aacct = r.acct /\ r.akey = r.key /\ r.arid = 0)
        /\ r.rj \in BOOLEAN /\ r.racct \in Accounts /\ r.rkey \in Keys /\ r.rrid >= 0
        /\ ~r.rj => (r.racct = r.acct /\ r.rkey = r.key /\ r.rrid = 0)
    /\ \A j \in DOMAIN log: log[j] >= 0
    /\ regs >= 0 /\ \A g \in revoked: g >= 0
    /\ Len(ghost) = NR

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
\* INV-8: registration provenance, including the registration id.
Inv8 == \A k \in Keys, i \in Ids:
            (principals[k].reg /\ Req(i).key = k /\ i >= principals[k].from)
                => (Req(i).acct = principals[k].acct /\ principals[k].role = "Agent"
                    /\ Req(i).rid = principals[k].rid)
\* INV-9: pending count, and the cap.
Inv9 == \A k \in Keys: principals[k].reg =>
            principals[k].pending = Pend(k) /\ principals[k].pending <= MaxPending
\* INV-11: live registration ids are issued, distinct, and not revoked.
Inv11 == \A k \in Keys: principals[k].reg =>
            /\ principals[k].rid < regs /\ principals[k].rid \notin revoked
            /\ \A k2 \in Keys: (k2 # k /\ principals[k2].reg) => principals[k2].rid # principals[k].rid
\* INV-12: revoked ids were issued. (Write-once is below alpha, which keeps
\* the revocation map's keys only; Kani's HIST-10 checks it on the store.)
Inv12 == \A g \in revoked: g < regs
\* INV-13: at most one decision per request.
Inv13 == \A i \in Ids: ~(Req(i).appr /\ Req(i).rj)
\* INV-14: recorded registration ids were issued.
Inv14 == \A i \in Ids:
            /\ Req(i).rid < regs
            /\ Req(i).appr => Req(i).arid < regs
            /\ Req(i).rj => Req(i).rrid < regs
\* INV-15: registration accounting. Every issued id is live or revoked;
\* with INV-11 and INV-12 (all below regs, live ones distinct and not
\* revoked), exactly one of the two. Counted, so Apalache needs no range.
Inv15 == regs = Cardinality(revoked) + Cardinality({k \in Keys : principals[k].reg})
\* INV-16: registration binding. A recorded id that is live belongs to the
\* key, account and role it was recorded with.
Inv16 == \A k \in Keys, i \in Ids: principals[k].reg =>
            LET p == principals[k] r == Req(i) IN
            /\ r.rid = p.rid => (r.key = k /\ r.acct = p.acct /\ p.role = "Agent")
            /\ (r.appr /\ r.arid = p.rid) => (r.akey = k /\ r.aacct = p.acct /\ p.role = "Approver")
            /\ (r.rj /\ r.rrid = p.rid) => (r.rkey = k /\ r.racct = p.acct /\ p.role = "Approver")
\* Separation of duties and key distinctness for rejections (INV-5, INV-6).
Inv5r == \A i \in Ids: Req(i).rj => Req(i).racct # Req(i).acct /\ Req(i).rkey # Req(i).key
\* LEM-1: no duplicates in the log. LEM-2: log length = approved count.
Lem1 == \A j1, j2 \in DOMAIN log: j1 # j2 => log[j1] # log[j2]
Lem2 == NL = Cardinality({i \in Ids : Req(i).appr})

\* TR-1 provenance, through the ghost. Every decided request was made by an
\* Agent key of its account whose registration was never revoked before the
\* decision (the request is made only under such a registration: TX-3), and
\* decided by an Approver key of a different account (INV-5).
Provenance == \A i \in Ids: Decided(i) => ghost[i + 1].cont /\ ghost[i + 1].decOk
\* The core's active_from check decides exactly "the registration the
\* request was made under is unbroken", which the registration ids record.
RidLive == \A i \in Ids: ~Decided(i) => (Unbroken(i) <=> Live(i))

\* L2 (TLA-LIVE-2), approvability: a pending request can be approved by any
\* approver key of another account, so nothing in the core leaves it stuck.
EligibleKey(i, k) ==
    principals[k].reg /\ principals[k].role = "Approver" /\ principals[k].acct # Req(i).acct
Approvable ==
    \A i \in Ids, k \in Keys: (Pending(i) /\ EligibleKey(i, k)) =>
        /\ ApproveErr(principals[k].acct, principals[k].acct, k, i, Req(i).act) = "Ok"
        /\ RejectErr(principals[k].acct, principals[k].acct, k, i) = "Ok"

Inv ==
    /\ TypeOK /\ Inv3 /\ Inv4 /\ Inv5 /\ Inv6 /\ Inv7 /\ Inv8 /\ Inv9
    /\ Inv11 /\ Inv12 /\ Inv13 /\ Inv14 /\ Inv15 /\ Inv16 /\ Inv5r
    /\ Lem1 /\ Lem2 /\ Provenance /\ RidLive /\ Approvable

-----------------------------------------------------------------------------
(* Action properties, checked as [][P]_vars                                *)

\* HIST-1: request content is immutable and never removed.
Hist1 == NR' >= NR /\ \A i \in Ids:
            /\ requests'[i + 1].acct = Req(i).acct /\ requests'[i + 1].key = Req(i).key
            /\ requests'[i + 1].act = Req(i).act
\* HIST-2: decisions are immutable. TR-2: so each request is decided once.
\* HIST-9 (Rejected is terminal) is the rejection half.
Hist2 == \A i \in Ids: Decided(i) => requests'[i + 1] = Req(i)
\* HIST-3: the log is append-only.
Hist3 == NL' >= NL /\ SubSeq(log', 1, NL) = log
\* HIST-8 / TR-3, durable revocation: Void is terminal, even across a revoke
\* and re-add of the same key, account and role. Equivalent to
\* \A i: [](Void(i) => []Void(i)) since stuttering preserves Void(i).
Hist8 == \A i \in Ids: Void(i) => Void(i)'
\* HIST-7: the owner can't rewrite history.
Hist7 == (principals' # principals /\ requests' = requests) => log' = log

\* HIST-10: the registration counter never decreases, and a revocation is
\* recorded only for a live registration, never removed.
Hist10 == regs' >= regs /\ revoked \subseteq revoked'
            /\ \A g \in revoked' \ revoked: \E k \in Keys: principals[k].reg /\ principals[k].rid = g

StepProps == Hist1 /\ Hist2 /\ Hist3 /\ Hist7 /\ Hist8 /\ Hist10
StepProperty == [][StepProps]_vars

-----------------------------------------------------------------------------
(* Non-vacuity (TR-5): each of these must be reachable, so the checker     *)
(* runs them as invariants that must FAIL (run-tla.sh inverts them).       *)

Witness_Approved == ~\E i \in Ids: Approved(i)
Witness_Rejected == ~\E i \in Ids: Rejected(i)
Witness_Void == ~\E i \in Ids: Void(i)
\* Revoked, re-added to the same account and role, and still void.
Witness_Revival == ~\E i \in Ids: Void(i) /\ principals[Req(i).key].reg
                        /\ principals[Req(i).key].acct = Req(i).acct
                        /\ principals[Req(i).key].role = "Agent"
Witness_Cap == ~\E k \in Keys: principals[k].reg /\ principals[k].pending = MaxPending

=============================================================================
