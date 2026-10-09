--------------------------- MODULE ApprovalCore ---------------------------
(***************************************************************************)
(* The NEAR approval contract's decision logic, as a state machine over    *)
(* every event sequence (strategy.md section 17).                          *)
(*                                                                         *)
(* Upstream: difflabai/trust-framework contracts/approval/core/src/lib.rs  *)
(* Pin:      3426c92 (trust-framework PR #15)                              *)
(*                                                                         *)
(* This module mirrors approval-core one to one, so that a Kani harness    *)
(* can prove the Rust step refines each action (REF-1..5, kani/src/tla.rs).*)
(* The variables are the image of a store under the abstraction map alpha: *)
(*                                                                         *)
(*   principals  the key registry, total over Keys (reg = FALSE: absent)   *)
(*   requests    the request array; request id i is requests[i+1]          *)
(*   log         the approval log of request ids                           *)
(*   regs        the registration counter G (next registration id)         *)
(*   revoked     the registration ids with a recorded revocation           *)
(*                                                                         *)
(* Block times are not modelled: the core stores them and never branches   *)
(* on them (assumption A7, proved by REF-4), so the revocation map is the  *)
(* set of its keys. Counters are unbounded Nat: the core's LogFull guards  *)
(* fire only at u64::MAX (A6, LEM-3, ROB-1).                               *)
(*                                                                         *)
(* Each entry point has an error operator, the first failing guard in the  *)
(* core's order, and an action enabled exactly when that operator is "Ok". *)
(* A rejected call writes nothing (TX-0), so it is a stuttering step and   *)
(* is not part of Next.                                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    \* @type: ACCT;
    Owner,
    \* Every account, the owner included.
    \* @type: Set(ACCT);
    Accounts,
    \* @type: Set(KEY);
    Keys,
    \* Action payload classes (assumption A5). Payloads holds non-empty
    \* actions of at most 2048 bytes; Empty is ""; TooLong is any longer one.
    \* @type: Set(Str);
    Payloads,
    \* @type: Str;
    Empty,
    \* @type: Str;
    TooLong,
    \* MAX_PENDING_PER_KEY (16 in the core; configs may scale it, see C-5).
    \* @type: Int;
    MaxPending

ASSUME Owner \in Accounts
ASSUME Empty \notin Payloads /\ TooLong \notin Payloads /\ Empty # TooLong
ASSUME MaxPending \in Nat \ {0}

Actions == Payloads \cup {Empty, TooLong}
Roles == {"Agent", "Approver"}

\* The record of a key that is not registered. Its other fields are unused.
NoPrincipal == [reg |-> FALSE, acct |-> Owner, role |-> "Agent", rid |-> 0, from |-> 0, pending |-> 0]

VARIABLES
    \* rid is registration_id.
    \* @type: KEY -> { reg: Bool, acct: ACCT, role: Str, rid: Int, from: Int, pending: Int };
    principals,
    \* rid is the agent's registration id. appr = FALSE while unapproved,
    \* and aidx, aacct, akey, arid are then unused; likewise rj and racct,
    \* rkey, rrid for the rejection.
    \* @type: Seq({ acct: ACCT, key: KEY, rid: Int, act: Str, appr: Bool, aidx: Int, aacct: ACCT, akey: KEY, arid: Int, rj: Bool, racct: ACCT, rkey: KEY, rrid: Int });
    requests,
    \* @type: Seq(Int);
    log,
    \* @type: Int;
    regs,
    \* @type: Set(Int);
    revoked,
    \* Ghost history for provenance (TR-1), not part of the store and not
    \* in alpha. When request i is decided (approved or rejected), cont
    \* records that the agent registration it was made under was still
    \* unbroken, and decOk that the deciding key was registered as Approver
    \* to the deciding account.
    \* @type: Seq({ cont: Bool, decOk: Bool });
    ghost

store == <<principals, requests, log, regs, revoked>>
vars == <<principals, requests, log, regs, revoked, ghost>>

NR == Len(requests)
NL == Len(log)
\* Written as a map over DOMAIN so Apalache needs no symbolic range bound.
Ids == {j - 1 : j \in DOMAIN requests}
Req(i) == requests[i + 1]

-----------------------------------------------------------------------------
(* Guards, in the core's order. GuardOrder lists the error codes each      *)
(* entry point can return, in that order; C-2t checks it against the       *)
(* Prolog requirements (strategy.md section 17.4).                         *)

\* LogFull is listed where the core has it, but no operator returns it:
\* counters are unbounded here (A6).
\* @type: { add: Seq(Str), revoke: Seq(Str), request: Seq(Str), approve: Seq(Str), reject: Seq(Str) };
GuardOrder == [
    add     |-> <<"NotOwner", "KeyAlreadyRegistered", "LogFull">>,
    revoke  |-> <<"NotOwner", "KeyNotRegistered">>,
    request |-> <<"IndirectCall", "UnknownKey", "WrongRole", "KeyAccountMismatch",
                  "EmptyAction", "ActionTooLong", "TooManyPending", "LogFull">>,
    approve |-> <<"IndirectCall", "UnknownKey", "WrongRole", "KeyAccountMismatch",
                  "RequestNotFound", "AlreadyApproved", "AlreadyRejected", "AgentRevoked",
                  "ActionMismatch", "SelfApproval", "LogFull">>,
    reject  |-> <<"IndirectCall", "UnknownKey", "WrongRole", "KeyAccountMismatch",
                  "RequestNotFound", "AlreadyApproved", "AlreadyRejected", "AgentRevoked",
                  "SelfApproval">>
]

AddErr(c, k) ==
    IF c # Owner THEN "NotOwner"
    ELSE IF principals[k].reg THEN "KeyAlreadyRegistered"
    ELSE "Ok"

RevokeErr(c, k) ==
    IF c # Owner THEN "NotOwner"
    ELSE IF ~principals[k].reg THEN "KeyNotRegistered"
    ELSE "Ok"

\* authenticate: pred and signer are the predecessor and signer accounts,
\* k the signing key.
AuthErr(pred, signer, k, role) ==
    IF pred # signer THEN "IndirectCall"
    ELSE IF ~principals[k].reg THEN "UnknownKey"
    ELSE IF principals[k].role # role THEN "WrongRole"
    ELSE IF principals[k].acct # signer THEN "KeyAccountMismatch"
    ELSE "Ok"

RequestErr(pred, signer, k, x) ==
    LET a == AuthErr(pred, signer, k, "Agent") IN
    IF a # "Ok" THEN a
    ELSE IF x = Empty THEN "EmptyAction"
    ELSE IF x = TooLong THEN "ActionTooLong"
    ELSE IF principals[k].pending >= MaxPending THEN "TooManyPending"
    ELSE "Ok"

\* live_agent_registration: the registration request i was made under is
\* still in force.
Live(i) ==
    LET p == principals[Req(i).key] IN
    p.reg /\ p.role = "Agent" /\ p.acct = Req(i).acct /\ p.from <= i

\* decidable_request.
DecideErr(i) ==
    IF i \notin Ids THEN "RequestNotFound"
    ELSE IF Req(i).appr THEN "AlreadyApproved"
    ELSE IF Req(i).rj THEN "AlreadyRejected"
    ELSE IF ~Live(i) THEN "AgentRevoked"
    ELSE "Ok"

ApproveErr(pred, signer, k, i, x) ==
    LET a == AuthErr(pred, signer, k, "Approver")
        d == DecideErr(i)
    IN
    IF a # "Ok" THEN a
    ELSE IF d # "Ok" THEN d
    ELSE IF Req(i).act # x THEN "ActionMismatch"
    ELSE IF signer = Req(i).acct THEN "SelfApproval"
    ELSE "Ok"

RejectErr(pred, signer, k, i) ==
    LET a == AuthErr(pred, signer, k, "Approver")
        d == DecideErr(i)
    IN
    IF a # "Ok" THEN a
    ELSE IF d # "Ok" THEN d
    ELSE IF signer = Req(i).acct THEN "SelfApproval"
    ELSE "Ok"

-----------------------------------------------------------------------------
(* Actions                                                                 *)

Init ==
    /\ principals = [k \in Keys |-> NoPrincipal]
    /\ requests = <<>>
    /\ log = <<>>
    /\ regs = 0
    /\ revoked = {}
    /\ ghost = <<>>

AddPrincipal(c, k, a, r) ==
    /\ AddErr(c, k) = "Ok"
    /\ principals' = [principals EXCEPT ![k] =
                        [reg |-> TRUE, acct |-> a, role |-> r, rid |-> regs,
                         from |-> NR, pending |-> 0]]
    /\ regs' = regs + 1
    /\ UNCHANGED <<requests, log, revoked, ghost>>

RevokeKey(c, k) ==
    /\ RevokeErr(c, k) = "Ok"
    /\ principals' = [principals EXCEPT ![k] = NoPrincipal]
    /\ revoked' = revoked \cup {principals[k].rid}
    /\ UNCHANGED <<requests, log, regs, ghost>>

RequestAction(pred, signer, k, x) ==
    /\ RequestErr(pred, signer, k, x) = "Ok"
    /\ principals' = [principals EXCEPT ![k].pending = @ + 1]
    /\ requests' = Append(requests,
                    [acct |-> signer, key |-> k, rid |-> principals[k].rid, act |-> x,
                     appr |-> FALSE, aidx |-> 0, aacct |-> signer, akey |-> k, arid |-> 0,
                     rj |-> FALSE, racct |-> signer, rkey |-> k, rrid |-> 0])
    /\ ghost' = Append(ghost, [cont |-> FALSE, decOk |-> FALSE])
    /\ UNCHANGED <<log, regs, revoked>>

\* The agent registration request i was made under has not been revoked
\* (registration ids are never reused). Ghost only: the core decides
\* liveness by Live, and RidLive proves the two agree.
Unbroken(i) ==
    LET p == principals[Req(i).key] IN p.reg /\ p.rid = Req(i).rid

\* Common effect of a decision on request i by key k of account signer.
Decide(signer, k, i) ==
    /\ principals' = [principals EXCEPT ![Req(i).key].pending = IF @ > 0 THEN @ - 1 ELSE 0]
    /\ ghost' = [ghost EXCEPT ![i + 1] =
                    [cont |-> Unbroken(i),
                     decOk |-> principals[k].reg /\ principals[k].role = "Approver"
                                   /\ principals[k].acct = signer]]

Approve(pred, signer, k, i, x) ==
    /\ ApproveErr(pred, signer, k, i, x) = "Ok"
    /\ requests' = [requests EXCEPT ![i + 1] =
                    [@ EXCEPT !.appr = TRUE, !.aidx = NL, !.aacct = signer, !.akey = k,
                              !.arid = principals[k].rid]]
    /\ log' = Append(log, i)
    /\ Decide(signer, k, i)
    /\ UNCHANGED <<regs, revoked>>

Reject(pred, signer, k, i) ==
    /\ RejectErr(pred, signer, k, i) = "Ok"
    /\ requests' = [requests EXCEPT ![i + 1] =
                    [@ EXCEPT !.rj = TRUE, !.racct = signer, !.rkey = k,
                              !.rrid = principals[k].rid]]
    /\ Decide(signer, k, i)
    /\ UNCHANGED <<log, regs, revoked>>

\* Every call any party can make, with every argument. Request ids range
\* one past the end so RequestNotFound stays reachable in the error view.
Next ==
    \/ \E c \in Accounts, k \in Keys, a \in Accounts, r \in Roles: AddPrincipal(c, k, a, r)
    \/ \E c \in Accounts, k \in Keys: RevokeKey(c, k)
    \/ \E p, s \in Accounts, k \in Keys, x \in Actions: RequestAction(p, s, k, x)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}, x \in Actions: Approve(p, s, k, i, x)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}: Reject(p, s, k, i)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Request status (request_status)                                         *)

Decided(i)  == Req(i).appr \/ Req(i).rj
Approved(i) == i \in Ids /\ Req(i).appr
Rejected(i) == i \in Ids /\ ~Req(i).appr /\ Req(i).rj
Pending(i)  == i \in Ids /\ ~Decided(i) /\ Live(i)
Void(i)     == i \in Ids /\ ~Decided(i) /\ ~Live(i)

\* Undecided requests made under the registration currently held by k.
Pend(k) == Cardinality({i \in Ids : Req(i).key = k /\ ~Decided(i) /\ i >= principals[k].from})

=============================================================================
