/-
The shared text format for stores and calls (kani/src/mc2.rs,
prolog/verification/graph_export.pl, tools/scripts/mc3.py), over the
string universe the tools use: accounts `o, a1, ...`, keys `k0, k1, ...`,
payloads `x` or `t1, t2, ...`, plus `empty` and `too_long`.

Store text is `P|R|L|G|V`:
  P  key,acct,role,rid,from,pending per registered key, sorted, joined by ';'
  R  acct,key,rid,act,AP,RJ per request in id order, joined by ';', with
     AP = - | idx/acct/key/rid and RJ = - | acct/key/rid
  L  request ids in log order, joined by ','
  G  the registration counter
  V  revoked registration ids, sorted, joined by ','
-/
import ApprovalLean.Machine

namespace Approval.Text

open Approval

abbrev S := State String String String
abbrev O := Op String String String

def role : Role → String
  | .agent => "agent"
  | .approver => "approver"

def act : Action String → String
  | .pay p => p
  | .empty => "empty"
  | .tooLong => "too_long"

/-- The core's `ApprovalError` names (its `Debug` format), and `Ok`. -/
def errName : Err → String
  | .ok => "Ok"
  | .notOwner => "NotOwner"
  | .keyAlreadyRegistered => "KeyAlreadyRegistered"
  | .keyNotRegistered => "KeyNotRegistered"
  | .indirectCall => "IndirectCall"
  | .unknownKey => "UnknownKey"
  | .wrongRole => "WrongRole"
  | .keyAccountMismatch => "KeyAccountMismatch"
  | .emptyAction => "EmptyAction"
  | .actionTooLong => "ActionTooLong"
  | .tooManyPending => "TooManyPending"
  | .requestNotFound => "RequestNotFound"
  | .alreadyApproved => "AlreadyApproved"
  | .alreadyRejected => "AlreadyRejected"
  | .agentRevoked => "AgentRevoked"
  | .actionMismatch => "ActionMismatch"
  | .selfApproval => "SelfApproval"
  | .logFull => "LogFull"

def sortStr (l : List String) : List String := l.mergeSort (fun a b => decide (a ≤ b))
def sortNat (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

def joinNat (l : List Nat) : String := ",".intercalate (l.map toString)

def store (s : S) : String :=
  let ps := sortStr <| s.principals.filter (·.2.reg) |>.map fun (k, p) =>
    s!"{k},{p.acct},{role p.role},{p.rid},{p.activeFrom},{p.pending}"
  let rs := s.requests.map fun r =>
    let ap := if r.appr then s!"{r.aidx}/{r.aacct}/{r.akey}/{r.arid}" else "-"
    let rj := if r.rj then s!"{r.racct}/{r.rkey}/{r.rrid}" else "-"
    s!"{r.acct},{r.key},{r.rid},{act r.act},{ap},{rj}"
  s!"{";".intercalate ps}|{";".intercalate rs}|{joinNat s.log}|{s.regs}|{joinNat (sortNat s.revoked)}"

def call : O → String
  | .add c k a r => s!"add,{c},{k},{a},{role r}"
  | .revoke c k => s!"revoke,{c},{k}"
  | .request p sg k x => s!"request,{p},{sg},{k},{act x}"
  | .approve p sg k i x => s!"approve,{p},{sg},{k},{i},{act x}"
  | .reject p sg k i => s!"reject,{p},{sg},{k},{i}"

def parseRole : String → Option Role
  | "agent" => some .agent
  | "approver" => some .approver
  | _ => none

def parseAct : String → Action String
  | "empty" => .empty
  | "too_long" => .tooLong
  | p => .pay p

def parseCall (t : String) : Option O :=
  match t.splitOn "," with
  | ["add", c, k, a, r] => (parseRole r).map (.add c k a)
  | ["revoke", c, k] => some (.revoke c k)
  | ["request", p, sg, k, x] => some (.request p sg k (parseAct x))
  | ["approve", p, sg, k, i, x] => i.toNat?.map fun i => .approve p sg k i (parseAct x)
  | ["reject", p, sg, k, i] => i.toNat?.map fun i => .reject p sg k i
  | _ => none

end Approval.Text
