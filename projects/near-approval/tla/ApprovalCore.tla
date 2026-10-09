--------------------------- MODULE ApprovalCore ---------------------------
(***************************************************************************)
(* The NEAR approval contract's decision logic, as a state machine over    *)
(* every event sequence (strategy.md section 17).                          *)
(*                                                                         *)
(* Upstream: difflabai/trust-framework contracts/approval/core/src/lib.rs  *)
(* Pin:      5736251d65c6bc11c20e5f27ddc869db27bd7299                       *)
(*                                                                         *)
(* This module mirrors approval-core one to one, so that a Kani harness    *)
(* can prove the Rust step refines each action (REF-1..5, kani/src/tla.rs).*)
(* The variables are the image of a store under the abstraction map alpha:*)
(*                                                                         *)
(*   principals  the key registry, total over Keys (reg = FALSE: absent)   *)
(*   requests    the request array; request id i is requests[i+1]          *)
(*   log         the approval log of request ids                           *)
(*                                                                         *)
(* Block times are not modelled: the core stores them and never branches   *)
(* on them (assumption A7, proved by REF-4). Counters are unbounded Nat:   *)
(* the core's LogFull guards fire only at u64::MAX (A6, LEM-3, ROB-1).     *)
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
NoPrincipal == [reg |-> FALSE, acct |-> Owner, role |-> "Agent", from |-> 0, pending |-> 0]

VARIABLES
    \* @type: KEY -> { reg: Bool, acct: ACCT, role: Str, from: Int, pending: Int };
    principals,
    \* appr = FALSE while unapproved; aidx, aacct and akey are then unused.
    \* @type: Seq({ acct: ACCT, key: KEY, act: Str, appr: Bool, aidx: Int, aacct: ACCT, akey: KEY });
    requests,
    \* @type: Seq(Int);
    log,
    \* Ghost history for provenance (TR-1), not part of the store and not
    \* in alpha. epoch[k] counts removals of key k. ghost[i+1].ep is the
    \* epoch of the request's key when it was made, so the registration it
    \* was made under is still unbroken iff the epoch is unchanged. At
    \* approval, cont freezes that fact, and apprOk records that the
    \* approver key was registered as Approver to the approving account.
    \* @type: KEY -> Int;
    epoch,
    \* @type: Seq({ ep: Int, cont: Bool, apprOk: Bool });
    ghost

store == <<principals, requests, log>>
vars == <<principals, requests, log, epoch, ghost>>

NR == Len(requests)
NL == Len(log)
\* Written as a map over DOMAIN so Apalache needs no symbolic range bound.
Ids == {j - 1 : j \in DOMAIN requests}
Req(i) == requests[i + 1]

-----------------------------------------------------------------------------
(* Guards, in the core's order. GuardOrder lists the error codes each      *)
(* entry point can return, in that order; C-2t checks it against the       *)
(* Prolog requirements (strategy.md section 17.4).                         *)

\* @type: { add: Seq(Str), revoke: Seq(Str), request: Seq(Str), approve: Seq(Str) };
GuardOrder == [
    add     |-> <<"NotOwner", "KeyAlreadyRegistered">>,
    revoke  |-> <<"NotOwner", "KeyNotRegistered">>,
    request |-> <<"IndirectCall", "UnknownKey", "WrongRole", "KeyAccountMismatch",
                  "EmptyAction", "ActionTooLong", "TooManyPending", "LogFull">>,
    approve |-> <<"IndirectCall", "UnknownKey", "WrongRole", "KeyAccountMismatch",
                  "RequestNotFound", "AlreadyApproved", "AgentRevoked",
                  "ActionMismatch", "SelfApproval", "LogFull">>
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

ApproveErr(pred, signer, k, i, x) ==
    LET a == AuthErr(pred, signer, k, "Approver") IN
    IF a # "Ok" THEN a
    ELSE IF i \notin Ids THEN "RequestNotFound"
    ELSE IF Req(i).appr THEN "AlreadyApproved"
    ELSE IF ~Live(i) THEN "AgentRevoked"
    ELSE IF Req(i).act # x THEN "ActionMismatch"
    ELSE IF signer = Req(i).acct THEN "SelfApproval"
    ELSE "Ok"

-----------------------------------------------------------------------------
(* Actions                                                                 *)

Init ==
    /\ principals = [k \in Keys |-> NoPrincipal]
    /\ requests = <<>>
    /\ log = <<>>
    /\ epoch = [k \in Keys |-> 0]
    /\ ghost = <<>>

AddPrincipal(c, k, a, r) ==
    /\ AddErr(c, k) = "Ok"
    /\ principals' = [principals EXCEPT ![k] =
                        [reg |-> TRUE, acct |-> a, role |-> r, from |-> NR, pending |-> 0]]
    /\ UNCHANGED <<requests, log, epoch, ghost>>

RevokeKey(c, k) ==
    /\ RevokeErr(c, k) = "Ok"
    /\ principals' = [principals EXCEPT ![k] = NoPrincipal]
    /\ epoch' = [epoch EXCEPT ![k] = @ + 1]
    /\ UNCHANGED <<requests, log, ghost>>

RequestAction(pred, signer, k, x) ==
    /\ RequestErr(pred, signer, k, x) = "Ok"
    /\ principals' = [principals EXCEPT ![k].pending = @ + 1]
    /\ requests' = Append(requests,
                    [acct |-> signer, key |-> k, act |-> x,
                     appr |-> FALSE, aidx |-> 0, aacct |-> signer, akey |-> k])
    /\ ghost' = Append(ghost, [ep |-> epoch[k], cont |-> FALSE, apprOk |-> FALSE])
    /\ UNCHANGED <<log, epoch>>

Approve(pred, signer, k, i, x) ==
    /\ ApproveErr(pred, signer, k, i, x) = "Ok"
    /\ requests' = [requests EXCEPT ![i + 1] =
                    [@ EXCEPT !.appr = TRUE, !.aidx = NL, !.aacct = signer, !.akey = k]]
    /\ principals' = [principals EXCEPT ![Req(i).key].pending = IF @ > 0 THEN @ - 1 ELSE 0]
    /\ log' = Append(log, i)
    /\ ghost' = [ghost EXCEPT ![i + 1].cont = (ghost[i + 1].ep = epoch[Req(i).key]),
                              ![i + 1].apprOk = principals[k].reg
                                  /\ principals[k].role = "Approver"
                                  /\ principals[k].acct = signer]
    /\ UNCHANGED epoch

\* Every call any party can make, with every argument. Request ids range
\* one past the end so RequestNotFound stays reachable in the error view.
Next ==
    \/ \E c \in Accounts, k \in Keys, a \in Accounts, r \in Roles: AddPrincipal(c, k, a, r)
    \/ \E c \in Accounts, k \in Keys: RevokeKey(c, k)
    \/ \E p, s \in Accounts, k \in Keys, x \in Actions: RequestAction(p, s, k, x)
    \/ \E p, s \in Accounts, k \in Keys, i \in Ids \cup {NR}, x \in Actions: Approve(p, s, k, i, x)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Request status (request_status)                                        *)

Approved(i) == i \in Ids /\ Req(i).appr
Pending(i)  == i \in Ids /\ ~Req(i).appr /\ Live(i)
Void(i)     == i \in Ids /\ ~Req(i).appr /\ ~Live(i)

\* Unapproved requests made under the registration currently held by k.
Pend(k) == Cardinality({i \in Ids : Req(i).key = k /\ ~Req(i).appr /\ i >= principals[k].from})

=============================================================================
