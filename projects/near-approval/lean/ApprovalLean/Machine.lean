/-
The NEAR approval contract's decision logic: a Lean transcription of
`tla/ApprovalCore.tla` (strategy.md section 18).

Upstream: difflabai/trust-framework contracts/approval/core/src/lib.rs
Pin:      3426c92 (trust-framework PR #15), through ApprovalCore.tla

Each definition carries the name of the TLA+ operator it transcribes. The
differences are representation only, and each is fixed by the abstraction
the export and replay tools (`Text.lean`) apply before comparing with TLC,
Prolog and the core (MC-4, REF-5L):

* `principals` is a finite map, an association list with distinct keys
  holding only registered principals. TLA+'s total function over `Keys`
  is `prin s k`, which answers `noPrincipal` for an absent key (TypeOK's
  `~p.reg => p = NoPrincipal`). Keys are any type: the model has no `Keys`
  constant, so every theorem holds for every key universe, finite or not.
* `revoked` is a list without duplicates, read as the set of its elements.
* Accounts, keys and payloads are type parameters with decidable equality
  (TLA+'s `Accounts`, `Keys`, `Payloads`); `Action P` is `Actions`.
* `MaxPending` and `Owner` are fields of `Cfg`; counters are `Nat`, so
  `LogFull` never fires (assumption A6, as in TLA+).
-/

namespace Approval

inductive Role where
  | agent
  | approver
  deriving DecidableEq, Repr, Inhabited

/-- `Actions == Payloads \cup {Empty, TooLong}`. -/
inductive Action (P : Type) where
  | pay (p : P)
  | empty
  | tooLong
  deriving DecidableEq, Repr

/-- The core's `ApprovalError`, plus `ok`. -/
inductive Err where
  | ok
  | notOwner
  | keyAlreadyRegistered
  | keyNotRegistered
  | indirectCall
  | unknownKey
  | wrongRole
  | keyAccountMismatch
  | emptyAction
  | actionTooLong
  | tooManyPending
  | requestNotFound
  | alreadyApproved
  | alreadyRejected
  | agentRevoked
  | actionMismatch
  | selfApproval
  | logFull
  deriving DecidableEq, Repr, Inhabited

/-- The constants: `Owner` and `MaxPending`. -/
structure Cfg (A : Type) where
  owner : A
  maxPending : Nat

/-- A key's record. `activeFrom` is TLA+'s `from`. -/
structure Principal (A : Type) where
  reg : Bool
  acct : A
  role : Role
  rid : Nat
  activeFrom : Nat
  pending : Nat
  deriving DecidableEq, Repr

/-- One request. `rid` is the agent's registration id; the `a*` fields
record the approval and the `r*` fields the rejection. -/
structure Request (A K P : Type) where
  acct : A
  key : K
  rid : Nat
  act : Action P
  appr : Bool
  aidx : Nat
  aacct : A
  akey : K
  arid : Nat
  rj : Bool
  racct : A
  rkey : K
  rrid : Nat
  deriving DecidableEq, Repr

/-- Ghost history for provenance (TR-1). -/
structure Ghost where
  cont : Bool
  decOk : Bool
  deriving DecidableEq, Repr

structure State (A K P : Type) where
  principals : List (K × Principal A)
  requests : List (Request A K P)
  log : List Nat
  regs : Nat
  revoked : List Nat
  ghost : List Ghost
  deriving Repr

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## The principal map -/

/-- `NoPrincipal`. -/
def noPrincipal (cfg : Cfg A) : Principal A :=
  { reg := false, acct := cfg.owner, role := .agent, rid := 0, activeFrom := 0, pending := 0 }

def plookup (k : K) : List (K × Principal A) → Option (Principal A)
  | [] => none
  | (k', p) :: l => if k' = k then some p else plookup k l

def perase (k : K) : List (K × Principal A) → List (K × Principal A)
  | [] => []
  | (k', p) :: l => if k' = k then perase k l else (k', p) :: perase k l

def pmodify (k : K) (f : Principal A → Principal A) :
    List (K × Principal A) → List (K × Principal A)
  | [] => []
  | (k', p) :: l => if k' = k then (k', f p) :: pmodify k f l else (k', p) :: pmodify k f l

/-- `principals[k]`. -/
def prin (cfg : Cfg A) (s : State A K P) (k : K) : Principal A :=
  (plookup k s.principals).getD (noPrincipal cfg)

/-! ## Requests -/

/-- `NR`. -/
def State.nr (s : State A K P) : Nat := s.requests.length
/-- `NL`. -/
def State.nl (s : State A K P) : Nat := s.log.length

/-- `Req(i)`, defined exactly on `Ids`. -/
def State.req (s : State A K P) (i : Nat) : Option (Request A K P) := s.requests[i]?

/-- `Decided(i)` for a request record. -/
def Request.decided (r : Request A K P) : Bool := r.appr || r.rj

/-! ## Guards, in the core's order -/

/-- `AddErr`. -/
def addErr (cfg : Cfg A) (s : State A K P) (c : A) (k : K) : Err :=
  if c ≠ cfg.owner then .notOwner
  else if (prin cfg s k).reg then .keyAlreadyRegistered
  else .ok

/-- `RevokeErr`. -/
def revokeErr (cfg : Cfg A) (s : State A K P) (c : A) (k : K) : Err :=
  if c ≠ cfg.owner then .notOwner
  else if !(prin cfg s k).reg then .keyNotRegistered
  else .ok

/-- `AuthErr`. -/
def authErr (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K) (role : Role) : Err :=
  if pred ≠ signer then .indirectCall
  else if !(prin cfg s k).reg then .unknownKey
  else if (prin cfg s k).role ≠ role then .wrongRole
  else if (prin cfg s k).acct ≠ signer then .keyAccountMismatch
  else .ok

/-- `RequestErr`. -/
def requestErr (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K) (x : Action P) : Err :=
  let a := authErr cfg s pred signer k .agent
  if a ≠ .ok then a
  else if x = .empty then .emptyAction
  else if x = .tooLong then .actionTooLong
  else if (prin cfg s k).pending ≥ cfg.maxPending then .tooManyPending
  else .ok

/-- `Live(i)` for request `i` with record `r`. -/
def liveR (cfg : Cfg A) (s : State A K P) (i : Nat) (r : Request A K P) : Bool :=
  let p := prin cfg s r.key
  p.reg && p.role == .agent && p.acct == r.acct && decide (p.activeFrom ≤ i)

/-- `Live(i)`; false outside `Ids` (TLA+ never asks there). -/
def live (cfg : Cfg A) (s : State A K P) (i : Nat) : Bool :=
  match s.req i with
  | some r => liveR cfg s i r
  | none => false

/-- `DecideErr` (the core's `decidable_request`). -/
def decideErr (cfg : Cfg A) (s : State A K P) (i : Nat) : Err :=
  match s.req i with
  | none => .requestNotFound
  | some r =>
    if r.appr then .alreadyApproved
    else if r.rj then .alreadyRejected
    else if !liveR cfg s i r then .agentRevoked
    else .ok

/-- `ApproveErr`. -/
def approveErr (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K) (i : Nat)
    (x : Action P) : Err :=
  let a := authErr cfg s pred signer k .approver
  let d := decideErr cfg s i
  if a ≠ .ok then a
  else if d ≠ .ok then d
  else match s.req i with
    | none => .requestNotFound -- unreachable: d = ok
    | some r =>
      if r.act ≠ x then .actionMismatch
      else if signer = r.acct then .selfApproval
      else .ok

/-- `RejectErr`. -/
def rejectErr (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K) (i : Nat) : Err :=
  let a := authErr cfg s pred signer k .approver
  let d := decideErr cfg s i
  if a ≠ .ok then a
  else if d ≠ .ok then d
  else match s.req i with
    | none => .requestNotFound -- unreachable: d = ok
    | some r =>
      if signer = r.acct then .selfApproval
      else .ok

/-! ## Actions -/

/-- `Init`. -/
def init : State A K P :=
  { principals := [], requests := [], log := [], regs := 0, revoked := [], ghost := [] }

/-- Every call any party can make. `approve` and `reject` take any id;
outside `Ids` they fail with `RequestNotFound`, so this has the same
successful steps as TLA+'s `Next`, which ranges ids over `Ids \cup {NR}`. -/
inductive Op (A K P : Type) where
  | add (c : A) (k : K) (a : A) (r : Role)
  | revoke (c : A) (k : K)
  | request (pred signer : A) (k : K) (x : Action P)
  | approve (pred signer : A) (k : K) (i : Nat) (x : Action P)
  | reject (pred signer : A) (k : K) (i : Nat)
  deriving DecidableEq, Repr

/-- The error operator of each entry point. -/
def err (cfg : Cfg A) (s : State A K P) : Op A K P → Err
  | .add c k _ _ => addErr cfg s c k
  | .revoke c k => revokeErr cfg s c k
  | .request p sg k x => requestErr cfg s p sg k x
  | .approve p sg k i x => approveErr cfg s p sg k i x
  | .reject p sg k i => rejectErr cfg s p sg k i

/-- `revoked \cup {g}`. -/
def setInsert (g : Nat) (l : List Nat) : List Nat := if g ∈ l then l else g :: l

/-- `Unbroken(i)` for request record `r`. -/
def unbrokenR (cfg : Cfg A) (s : State A K P) (r : Request A K P) : Bool :=
  (prin cfg s r.key).reg && (prin cfg s r.key).rid == r.rid

/-- The common principal and ghost effect of a decision on request `i`
(record `r`) by key `k` of account `signer`: `Decide(signer, k, i)`. -/
def decidePrincipals (s : State A K P) (r : Request A K P) :
    List (K × Principal A) :=
  -- `[principals EXCEPT ![Req(i).key].pending = IF @ > 0 THEN @ - 1 ELSE 0]`;
  -- the key is registered whenever a decision succeeds (`Live(i)`).
  pmodify r.key (fun p => { p with pending := p.pending - 1 }) s.principals

def decideGhost (cfg : Cfg A) (s : State A K P) (signer : A) (k : K) (i : Nat)
    (r : Request A K P) : List Ghost :=
  s.ghost.set i
    { cont := unbrokenR cfg s r,
      decOk := (prin cfg s k).reg && (prin cfg s k).role == .approver
                 && (prin cfg s k).acct == signer }

/-- Each action's post-state, given that its error operator is `Ok`. -/
def effect (cfg : Cfg A) (s : State A K P) : Op A K P → State A K P
  | .add _ k a r =>
    -- `AddPrincipal`: the key is absent (`AddErr = "Ok"`), so the new
    -- entry goes in front.
    { s with
      principals := (k, { reg := true, acct := a, role := r, rid := s.regs,
                          activeFrom := s.nr, pending := 0 }) :: perase k s.principals,
      regs := s.regs + 1 }
  | .revoke _ k =>
    -- `RevokeKey`
    { s with
      principals := perase k s.principals,
      revoked := setInsert (prin cfg s k).rid s.revoked }
  | .request _ signer k x =>
    -- `RequestAction`
    { s with
      principals := pmodify k (fun p => { p with pending := p.pending + 1 }) s.principals,
      requests := s.requests ++
        [{ acct := signer, key := k, rid := (prin cfg s k).rid, act := x,
           appr := false, aidx := 0, aacct := signer, akey := k, arid := 0,
           rj := false, racct := signer, rkey := k, rrid := 0 }],
      ghost := s.ghost ++ [{ cont := false, decOk := false }] }
  | .approve _ signer k i _ =>
    -- `Approve`
    match s.req i with
    | none => s
    | some r =>
      { s with
        requests := s.requests.set i
          { r with appr := true, aidx := s.nl, aacct := signer, akey := k,
                   arid := (prin cfg s k).rid },
        log := s.log ++ [i],
        principals := decidePrincipals s r,
        ghost := decideGhost cfg s signer k i r }
  | .reject _ signer k i =>
    -- `Reject`
    match s.req i with
    | none => s
    | some r =>
      { s with
        requests := s.requests.set i
          { r with rj := true, racct := signer, rkey := k, rrid := (prin cfg s k).rid },
        principals := decidePrincipals s r,
        ghost := decideGhost cfg s signer k i r }

/-- One call: a rejected call is a stutter (TX-0). -/
def step (cfg : Cfg A) (s : State A K P) (op : Op A K P) : State A K P :=
  if err cfg s op = .ok then effect cfg s op else s

/-- `Next`: the successful calls. -/
def Next (cfg : Cfg A) (s s' : State A K P) : Prop :=
  ∃ op, err cfg s op = .ok ∧ s' = effect cfg s op

/-- A run of calls from `s`. -/
def run (cfg : Cfg A) (s : State A K P) (ops : List (Op A K P)) : State A K P :=
  ops.foldl (step cfg) s

/-- The reachable states. -/
inductive Reach (cfg : Cfg A) : State A K P → Prop where
  | init : Reach cfg init
  | step {s} (op : Op A K P) : Reach cfg s → Reach cfg (step cfg s op)

/-! ## Request status (`request_status`) -/

/-- `Approved(i)`. -/
def approved (s : State A K P) (i : Nat) : Prop := ∃ r, s.req i = some r ∧ r.appr = true
/-- `Rejected(i)`. -/
def rejected (s : State A K P) (i : Nat) : Prop :=
  ∃ r, s.req i = some r ∧ r.appr = false ∧ r.rj = true
/-- `Pending(i)`. -/
def pendingReq (cfg : Cfg A) (s : State A K P) (i : Nat) : Prop :=
  ∃ r, s.req i = some r ∧ r.decided = false ∧ liveR cfg s i r = true
/-- `Void(i)`. -/
def void (cfg : Cfg A) (s : State A K P) (i : Nat) : Prop :=
  ∃ r, s.req i = some r ∧ r.decided = false ∧ liveR cfg s i r = false

/-- Number of indices `i` (counting from `n`) at which `f i l[i]` holds. -/
def countIdx {R : Type} (f : Nat → R → Bool) : List R → Nat → Nat
  | [], _ => 0
  | r :: l, n => (if f n r then 1 else 0) + countIdx f l (n + 1)

/-- `Pend(k)`: undecided requests made under the registration `k` holds. -/
def pend (cfg : Cfg A) (s : State A K P) (k : K) : Nat :=
  countIdx (fun i r => r.key == k && !r.decided && decide ((prin cfg s k).activeFrom ≤ i))
    s.requests 0

end Approval
