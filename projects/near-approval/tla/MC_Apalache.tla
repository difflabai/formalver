--------------------------- MODULE MC_Apalache ---------------------------
(***************************************************************************)
(* TLA-IND: Inv is an inductive invariant of ApprovalCore, checked by      *)
(* Apalache (strategy.md section 17.3):                                    *)
(*                                                                         *)
(*   Init => Inv                  (--init=Init    --inv=Inv --length=0)    *)
(*   Inv /\ Next => Inv'          (--init=IndInit --inv=Inv --length=1)    *)
(*                                                                         *)
(* IndInit is any state with at most MaxR requests and log entries (Gen),  *)
(* constrained only by Inv. Integers are unbounded and symbolic: no bound  *)
(* on active_from, pending, approval indices or registration ids.          *)
(* Together the two checks cover every reachable state of any depth whose  *)
(* request array has at most MaxR entries and with at most 3 revocations.  *)
(* MaxPending is scaled to 2 so that the cap is                            *)
(* reachable within MaxR requests (with the real 16 it never binds here;   *)
(* Kani's h_raw_request covers the real cap boundary).                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Apalache

Owner == "o_OF_ACCT"
Accounts == {"o_OF_ACCT", "a1_OF_ACCT", "a2_OF_ACCT"}
Keys == {"k1_OF_KEY", "k2_OF_KEY", "k3_OF_KEY"}
Payloads == {"x", "y"}
Empty == "EMPTY"
TooLong == "TOOLONG"
MaxPending == 2

\* Request array size for the inductive step (the step may append one).
MaxR == 3

VARIABLES
    \* @type: KEY -> { reg: Bool, acct: ACCT, role: Str, rid: Int, from: Int, pending: Int };
    principals,
    \* @type: Seq({ acct: ACCT, key: KEY, rid: Int, act: Str, appr: Bool, aidx: Int, aacct: ACCT, akey: KEY, arid: Int, rj: Bool, racct: ACCT, rkey: KEY, rrid: Int });
    requests,
    \* @type: Seq(Int);
    log,
    \* @type: Int;
    regs,
    \* @type: Set(Int);
    revoked,
    \* @type: Seq({ cont: Bool, decOk: Bool });
    ghost

INSTANCE ApprovalProps

IndInit ==
    /\ principals = Gen(3)
    /\ requests = Gen(MaxR)
    /\ log = Gen(MaxR)
    /\ regs = Gen(1)
    /\ revoked = Gen(3)
    /\ ghost = Gen(MaxR)
    /\ Inv

\* Non-vacuity: IndInit contains full states with an approved, a rejected
\* and a void request and a revocation, so the step is checked from them.
\* Must be VIOLATED.
IndWitness == ~(NR = MaxR /\ revoked # {} /\ \E i \in Ids: Approved(i)
                    /\ \E j \in Ids: Rejected(j) /\ \E h \in Ids: Void(h))
=============================================================================
