/-
LINK's text format (kani/src/link.rs): one footprint view, one call, and
`expect`'s error and `protocol`'s calls on that view, per line:

  view \t call \t error \t calls

view is `P|R|NR|NL|G`:
  P   key,acct,role,rid,from,pending per stored principal, joined by ';'
  R   `-`, or the one request the call can read:
      id,acct,key,rid,act,AP,RJ with AP = - | idx/acct/key/rid and
      RJ = - | acct/key/rid
  NR, NL, G  the request, approval and registration counters
The owner is `o`. calls are `protocol`'s calls joined by ';' (empty for
none): `incG`, `insP=<principal>`, `rmP=<key>`, `pushR=<request>`,
`replR=<request>`, `pushA=<id>`, `insRev=<rid>`, with times dropped (the
model has none, A7). Call text is `Text.call`'s.
-/
import ApprovalLean.Delta
import ApprovalLean.Text

namespace Approval.DeltaText

open Approval Approval.Text

abbrev R := Rd String String String
abbrev CP := CPrin String
abbrev CR := CReq String String String
abbrev CC := Call String String String

def prinText (k : String) (p : CP) : String :=
  s!"{k},{p.acct},{role p.role},{p.rid},{p.activeFrom},{p.pending}"

def reqText (r : CR) : String :=
  let ap := match r.appr with
    | some d => s!"{d.idx}/{d.acct}/{d.key}/{d.rid}"
    | none => "-"
  let rj := match r.rej with
    | some d => s!"{d.acct}/{d.key}/{d.rid}"
    | none => "-"
  s!"{r.id},{r.acct},{r.key},{r.rid},{act r.act},{ap},{rj}"

def callText : CC → String
  | .incG => "incG"
  | .insP k p => s!"insP={prinText k p}"
  | .rmP k => s!"rmP={k}"
  | .pushR r => s!"pushR={reqText r}"
  | .replR r => s!"replR={reqText r}"
  | .pushA i => s!"pushA={i}"
  | .insRev g => s!"insRev={g}"

def parsePrin (t : String) : Option (String × CP) :=
  match t.splitOn "," with
  | [k, a, r, rid, af, pend] => do
    pure (k, { acct := a, role := ← parseRole r, rid := ← rid.toNat?,
               activeFrom := ← af.toNat?, pending := ← pend.toNat? })
  | _ => none

def parseDec (t : String) (withIdx : Bool) : Option (Option (CDec String String)) :=
  if t = "-" then some none
  else match withIdx, t.splitOn "/" with
    | true, [i, a, k, rid] => do pure (some { idx := ← i.toNat?, acct := a, key := k, rid := ← rid.toNat? })
    | false, [a, k, rid] => do pure (some { idx := 0, acct := a, key := k, rid := ← rid.toNat? })
    | _, _ => none

def parseReq (t : String) : Option CR :=
  match t.splitOn "," with
  | [i, a, k, rid, x, ap, rj] => do
    pure { id := ← i.toNat?, acct := a, key := k, rid := ← rid.toNat?, act := parseAct x,
           appr := ← parseDec ap true, rej := ← parseDec rj false }
  | _ => none

def lookupP (k : String) : List (String × CP) → Option CP
  | [] => none
  | (k', p) :: l => if k' = k then some p else lookupP k l

def parseView (t : String) : Option R :=
  match t.splitOn "|" with
  | [ps, rq, nr, nl, g] => do
    let prins ← (if ps.isEmpty then [] else ps.splitOn ";").mapM parsePrin
    let req ← if rq = "-" then pure none else (parseReq rq).map some
    pure { owner := "o", prin := fun k => lookupP k prins,
           req := fun i => req.bind fun r => if r.id = i then some r else none,
           nr := ← nr.toNat?, nl := ← nl.toNat?, regs := ← g.toNat? }
  | _ => none

end Approval.DeltaText
