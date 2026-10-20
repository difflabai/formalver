/-
LINK's domain, mechanised (strategy.md section 18.6.1, ident-link-proposal.md).

LINK (kani/src/link.rs) checks the Rust `expect`/`protocol` against `cstep`
on the finite set of footprint views `allCls.map rep`. This file proves that
the set is enough for `cstep`: every view `v` of any accounts `A`, keys `K`,
payloads `P` and any counters has a class `cls v op` in `allCls`, and

  cstep cfg v op = tOut (sub v op) (cstep cfg' (rep c).rd (rep c).op)

where `c = cls v op`, `rep c` is the representative view LINK runs, and
`tOut (sub v op)` carries its result back to `v`: identities, payloads and
counters are substituted value by value from a table built from `v`
(`sub`), each counter also at `±1` (saturating). `LEAN-COVER`, `cover`.

The Rust side proves the same equation for `expect`/`protocol`
(`kani/src/norm.rs`, `h_link_t_*`) with a line-by-line transcription of
`cls`, `rep`, `sub` and `tOut`; LINK checks the two agree on every `rep c`.
Together: `expect`/`protocol` = `cstep` on every view. That the two
transcriptions of `cls`/`rep`/`sub`/`tOut` agree is ASM-NU; LINK's view-set
check (`approval-lean link`) holds the `rep` half of it to exact equality.

The footprint (LEAN-FRAME) is a corollary: `cls`, `sub` and `rep` read `v`
only at the call key, the request at `i`, its key and the counters the
operation uses, so `cstep` agrees on views that agree there (`frame`).
Renaming (LEAN-REN) is another: `cls` and `sub` see identities only through
`=`, so `cstep` commutes with every injective renaming (`rename`).

Requests at `i` are assumed to have id `i` (INV-1) and a payload action
(INV-2), as on every reachable store (`WFv`).
-/
import ApprovalLean.Delta
import ApprovalLean.Props

namespace Approval.Ident

open Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## Representative views -/

/-- A footprint view as LINK writes it: the stored principals (in order),
the one request the call can read, and the three counters. The owner is
`o`. -/
structure DView where
  prins : List (String × CPrin String)
  req : Option (CReq String String String)
  nr : Nat
  nl : Nat
  regs : Nat
  deriving DecidableEq, Repr

def lookupS (k : String) : List (String × CPrin String) → Option (CPrin String)
  | [] => none
  | (k', p) :: l => if k' = k then some p else lookupS k l

/-- The getters of a view (as `DeltaText.parseView` builds them). -/
def DView.rd (d : DView) : Rd String String String :=
  { owner := "o", prin := fun k => lookupS k d.prins,
    req := fun i => d.req.bind fun r => if r.id = i then some r else none,
    nr := d.nr, nl := d.nl, regs := d.regs }

/-- The configuration LINK runs `cstep` under. -/
def cfgL : Cfg String := { owner := "o", maxPending := 16 }

/-! Representative values. Distinct, at least 2 apart and away from the
constants `0`, `15`, `16`, `maxU - 1`, `maxU`, so the value table `sub`
builds is unambiguous on every output. -/

def gRep : Nat := 1000
def nrRep : Nat := 2000
def rid0 : Nat := 3000
def rid1 : Nat := 3100
def af0 : Nat := 4000
def pendRep : Nat := 5000
def afLe : Nat := 6000
def idRep : Nat := 7000
def afGt : Nat := 8000
def ridR : Nat := 9000
def nlRep : Nat := 10000

/-! ## Classes -/

/-- What an operation can observe of the action argument: its kind and,
for approve, whether it equals the request's. -/
inductive XCls where
  | eq
  | pay
  | empty
  | tooLong
  deriving DecidableEq, Repr

/-- The call key's principal (approve, reject): role, and whether its
account is the signer. -/
structure BCls where
  role : Role
  acctEq : Bool
  deriving DecidableEq, Repr

/-- The request's agent principal: role, account equal to the request's,
`activeFrom ≤ id`, `pending = 0`. -/
structure GCls where
  role : Role
  acctEq : Bool
  afLe : Bool
  pend0 : Bool
  deriving DecidableEq, Repr

/-- The request: approved, rejected, account equal to the signer. -/
structure RCls where
  appr : Bool
  rej : Bool
  acctEq : Bool
  deriving DecidableEq, Repr

/-- The request principal of `request_action`: role, account equal to the
signer, `pending ≥ cap`. -/
structure PCls where
  role : Role
  acctEq : Bool
  full : Bool
  deriving DecidableEq, Repr

inductive Cls where
  /-- `aRel`: 0 the owner, 1 the caller, 2 neither. -/
  | add (callerOwner : Bool) (aRel : Nat) (r : Role) (present : Bool) (regsMax : Bool)
  | revoke (callerOwner : Bool) (present : Bool)
  | request (predEq : Bool) (p : Option PCls) (x : XCls) (nrMax : Bool)
  | approve (predEq : Bool) (b : Option BCls) (kEq : Bool) (g : Option GCls) (r : Option RCls)
      (x : XCls) (nlMax : Bool)
  | reject (predEq : Bool) (b : Option BCls) (kEq : Bool) (g : Option GCls) (r : Option RCls)
  deriving DecidableEq, Repr

/-! ### Enumeration -/

def bools : List Bool := [false, true]
def roles : List Role := [.agent, .approver]

def opts {α : Type} (l : List α) : List (Option α) := none :: l.map some

def allB : List BCls := roles.flatMap fun r => bools.map fun a => ⟨r, a⟩
def allG : List GCls :=
  roles.flatMap fun r => bools.flatMap fun a => bools.flatMap fun f => bools.map fun p => ⟨r, a, f, p⟩
def allR : List RCls :=
  bools.flatMap fun ap => bools.flatMap fun rj => bools.map fun a => ⟨ap, rj, a⟩
def allP : List PCls := roles.flatMap fun r => bools.flatMap fun a => bools.map fun f => ⟨r, a, f⟩

def allCls : List Cls :=
  (bools.flatMap fun co => [0, 1, 2].flatMap fun ar => roles.flatMap fun r =>
      bools.flatMap fun pr => bools.map fun gm => Cls.add co ar r pr gm) ++
  (bools.flatMap fun co => bools.map fun pr => Cls.revoke co pr) ++
  (bools.flatMap fun pe => (opts allP).flatMap fun p =>
      [XCls.empty, .tooLong, .pay].flatMap fun x => bools.map fun m => Cls.request pe p x m) ++
  (bools.flatMap fun pe => (opts allB).flatMap fun b => bools.flatMap fun ke =>
      (if ke then [none] else opts allG).flatMap fun g => (opts allR).flatMap fun r =>
      (if r.isSome then [XCls.eq, .pay, .empty, .tooLong] else [XCls.pay, .empty, .tooLong]).flatMap
        fun x => bools.map fun m => Cls.approve pe b ke g r x m) ++
  (bools.flatMap fun pe => (opts allB).flatMap fun b => bools.flatMap fun ke =>
      (if ke then [none] else opts allG).flatMap fun g => (opts allR).map fun r =>
      Cls.reject pe b ke g r)

/-! ### The class of a view -/

/-- The kind of an action argument, `eq` when it equals `r`'s. -/
def xcls (x : Action P) (r : Option (CReq A K P)) : XCls :=
  if r.map (·.act) = some x then .eq
  else match x with
    | .pay _ => .pay
    | .empty => .empty
    | .tooLong => .tooLong

def bcls (signer : A) (b : CPrin A) : BCls := ⟨b.role, decide (b.acct = signer)⟩

def gcls (r : CReq A K P) (g : CPrin A) : GCls :=
  ⟨g.role, decide (g.acct = r.acct), decide (g.activeFrom ≤ r.id), decide (g.pending = 0)⟩

def rcls (signer : A) (r : CReq A K P) : RCls :=
  ⟨r.appr.isSome, r.rej.isSome, decide (r.acct = signer)⟩

/-- `kEq`: the request's key is the call key. `g` is read only when it is
not. -/
def kEqOf (k : K) (r : Option (CReq A K P)) : Bool := r.any fun r => decide (r.key = k)

def gOf (v : Rd A K P) (k : K) (r : Option (CReq A K P)) : Option GCls :=
  match r with
  | some r => if r.key = k then none else (v.prin r.key).map (gcls r)
  | none => none

def cls (cfg : Cfg A) (v : Rd A K P) : Op A K P → Cls
  | .add c k a r =>
    .add (decide (c = v.owner)) (if a = v.owner then 0 else if a = c then 1 else 2) r
      (v.prin k).isSome (decide (v.regs = maxU))
  | .revoke c k => .revoke (decide (c = v.owner)) (v.prin k).isSome
  | .request pred signer k x =>
    .request (decide (pred = signer))
      ((v.prin k).map fun p => ⟨p.role, decide (p.acct = signer), decide (p.pending ≥ cfg.maxPending)⟩)
      (xcls x (none : Option (CReq A K P))) (decide (v.nr = maxU))
  | .approve pred signer k i x =>
    .approve (decide (pred = signer)) ((v.prin k).map (bcls signer)) (kEqOf k (v.req i))
      (gOf v k (v.req i)) ((v.req i).map (rcls signer)) (xcls x (v.req i)) (decide (v.nl = maxU))
  | .reject pred signer k i =>
    .reject (decide (pred = signer)) ((v.prin k).map (bcls signer)) (kEqOf k (v.req i))
      (gOf v k (v.req i)) ((v.req i).map (rcls signer))

/-! ### The representative of a class -/

def accts : List String := ["o", "a1", "a2"]

def acctOf (b : Bool) : String := if b then "a1" else "a2"

def xRep : XCls → Action String
  | .eq => .pay "t1"
  | .pay => .pay "t2"
  | .empty => .empty
  | .tooLong => .tooLong

/-- The principal stored for add and revoke. -/
def pFix : CPrin String := { acct := "a2", role := .agent, rid := rid0, activeFrom := af0, pending := 0 }

def bRep (b : BCls) : CPrin String :=
  { acct := acctOf b.acctEq, role := b.role, rid := rid0, activeFrom := af0, pending := 0 }

def gRepP (racct : String) (g : GCls) : CPrin String :=
  { acct := if g.acctEq then racct else "o", role := g.role, rid := rid1,
    activeFrom := if g.afLe then afLe else afGt, pending := if g.pend0 then 0 else pendRep }

def decFix (idx : Nat) : CDec String String := { idx, acct := "a2", key := "k3", rid := 13 }

def rRep (kEq : Bool) (r : RCls) : CReq String String String :=
  { id := idRep, acct := acctOf r.acctEq, key := if kEq then "k0" else "k1", rid := ridR,
    act := .pay "t1", appr := if r.appr then some (decFix 4) else none,
    rej := if r.rej then some (decFix 0) else none }

/-- The decision views (approve, reject): the call key `k0` holds `b`; the
request's key is `k0` too when `kEq`, else `k1`, holding `g`. -/
def decView (b : Option BCls) (kEq : Bool) (g : Option GCls) (r : Option RCls) (nl : Nat) : DView :=
  let racct := (r.map fun r => acctOf r.acctEq).getD "a2"
  { prins := (b.map fun b => [("k0", bRep b)]).getD [] ++
      (if kEq then [] else (g.map fun g => [("k1", gRepP racct g)]).getD []),
    req := r.map (rRep kEq), nr := idRep + 1, nl, regs := gRep }

def rep : Cls → DView × Op String String String
  | .add co ar r pr gm =>
    ({ prins := if pr then [("k0", pFix)] else [], req := none, nr := nrRep, nl := nlRep,
       regs := if gm then maxU else gRep },
     .add (if co then "o" else "a1") "k0" (accts.getD ar "a2") r)
  | .revoke co pr =>
    ({ prins := if pr then [("k0", pFix)] else [], req := none, nr := nrRep, nl := nlRep,
       regs := gRep },
     .revoke (if co then "o" else "a1") "k0")
  | .request pe p x m =>
    ({ prins := (p.map fun p => [("k0", { acct := acctOf p.acctEq, role := p.role, rid := rid0,
                                          activeFrom := af0, pending := if p.full then 16 else 15 })]).getD [],
       req := none, nr := if m then maxU else nrRep, nl := nlRep, regs := gRep },
     .request (acctOf pe) "a1" "k0" (xRep x))
  | .approve pe b ke g r x m =>
    (decView b ke g r (if m then maxU else nlRep), .approve (acctOf pe) "a1" "k0" idRep (xRep x))
  | .reject pe b ke g r =>
    (decView b ke g r nlRep, .reject (acctOf pe) "a1" "k0" idRep)

/-! ## Transport back to `v` -/

/-- First match in a table, else the default. -/
def tab {α β : Type} [DecidableEq α] (l : List (α × β)) (d : β) (x : α) : β :=
  match l.find? (fun e => decide (e.1 = x)) with
  | some e => e.2
  | none => d

/-- `x + 1`, saturating at `u64::MAX` as in the Rust transcription. -/
def inc (x : Nat) : Nat := min (x + 1) maxU

/-- The counter table: a representative `d` stands for `v`, `d + 1` for
`v + 1` and `d - 1` for `v - 1`; anything else is itself. -/
def num : List (Nat × Nat) → Nat → Nat
  | [], x => x
  | (d, v) :: l, x => if x = d then v else if x = inc d then inc v else if x = d - 1 then v - 1 else num l x

structure Sub (A K P : Type) where
  acct : List (String × A)
  key : List (String × K)
  num : List (Nat × Nat)
  pay : List (String × P)
  dA : A
  dK : K

namespace Sub

variable (σ : Sub A K P)

def a (x : String) : A := tab σ.acct σ.dA x
def k (x : String) : K := tab σ.key σ.dK x
def n (x : Nat) : Nat := Approval.Ident.num σ.num x

def act : Action String → Action P
  | .pay p => match σ.pay.find? (fun e => decide (e.1 = p)) with
    | some e => .pay e.2
    | none => .empty
  | .empty => .empty
  | .tooLong => .tooLong

def prin (p : CPrin String) : CPrin A :=
  { acct := σ.a p.acct, role := p.role, rid := σ.n p.rid, activeFrom := σ.n p.activeFrom,
    pending := σ.n p.pending }

def dec (d : CDec String String) : CDec A K :=
  { idx := σ.n d.idx, acct := σ.a d.acct, key := σ.k d.key, rid := σ.n d.rid }

def req (r : CReq String String String) : CReq A K P :=
  { id := σ.n r.id, acct := σ.a r.acct, key := σ.k r.key, rid := σ.n r.rid, act := σ.act r.act,
    appr := r.appr.map σ.dec, rej := r.rej.map σ.dec }

def call : Call String String String → Call A K P
  | .incG => .incG
  | .insP k p => .insP (σ.k k) (σ.prin p)
  | .rmP k => .rmP (σ.k k)
  | .pushR r => .pushR (σ.req r)
  | .replR r => .replR (σ.req r)
  | .pushA i => .pushA (σ.n i)
  | .insRev g => .insRev (σ.n g)

def out (o : Err × List (Call String String String)) : Err × List (Call A K P) :=
  (o.1, o.2.map σ.call)

end Sub

/-- The rows a principal contributes to the counter table. -/
def pRows (rid af pend : Nat) (p : CPrin A) : List (Nat × Nat) :=
  [(rid, p.rid), (af, p.activeFrom), (pend, p.pending)]

def payRows (s : String) : Action P → List (String × P)
  | .pay p => [(s, p)]
  | _ => []

/-- The table carrying `rep (cls cfg v op)`'s results back to `v`. -/
def sub (cfg : Cfg A) (v : Rd A K P) : Op A K P → Sub A K P
  | .add c k a _ =>
    { acct := [("o", v.owner), ("a1", c), ("a2", a)], key := [("k0", k)],
      num := [(if v.regs = maxU then maxU else gRep, v.regs), (nrRep, v.nr)], pay := [],
      dA := a, dK := k }
  | .revoke c k =>
    { acct := [("o", v.owner), ("a1", c)], key := [("k0", k)],
      num := ((v.prin k).map fun p => [(rid0, p.rid)]).getD [], pay := [], dA := c, dK := k }
  | .request pred signer k x =>
    { acct := [("a1", signer), ("a2", pred)] ++ ((v.prin k).map fun p => [("a2", p.acct)]).getD [],
      key := [("k0", k)],
      num := ((v.prin k).map fun p =>
                pRows rid0 af0 (if p.pending ≥ cfg.maxPending then 16 else 15) p).getD [] ++
             [(if v.nr = maxU then maxU else nrRep, v.nr)],
      pay := payRows "t2" x, dA := signer, dK := k }
  | .approve pred signer k i x =>
    let r := v.req i
    { acct := decAccts v signer pred k r, key := decKeys k r,
      num := decNums v k i r ++ [(if v.nl = maxU then maxU else nlRep, v.nl)],
      pay := ((r.map fun r => payRows "t1" r.act).getD []) ++ payRows "t2" x, dA := signer, dK := k }
  | .reject pred signer k i =>
    let r := v.req i
    { acct := decAccts v signer pred k r, key := decKeys k r, num := decNums v k i r,
      pay := (r.map fun r => payRows "t1" r.act).getD [], dA := signer, dK := k }
where
  decAccts (v : Rd A K P) (signer pred : A) (k : K) (r : Option (CReq A K P)) : List (String × A) :=
    [("a1", signer)] ++ (r.map fun r => [("a2", r.acct)]).getD [] ++
      (match r with
       | some r => if r.key = k then [] else ((v.prin r.key).map fun g => [("o", g.acct)]).getD []
       | none => []) ++
      [("a2", pred)] ++ ((v.prin k).map fun b => [("a2", b.acct)]).getD []
  decKeys (k : K) (r : Option (CReq A K P)) : List (String × K) :=
    [("k0", k)] ++ (r.map fun r => [("k1", r.key)]).getD []
  decNums (v : Rd A K P) (k : K) (i : Nat) (r : Option (CReq A K P)) : List (Nat × Nat) :=
    ((v.prin k).map fun b => [(rid0, b.rid)]).getD [] ++
      (match r with
       | some r =>
         (if r.key = k then [] else
           ((v.prin r.key).map fun g =>
              pRows rid1 (if g.activeFrom ≤ r.id then afLe else afGt)
                (if g.pending = 0 then 0 else pendRep) g).getD []) ++
         [(idRep, i), (ridR, r.rid)]
       | none => [(idRep, i)])

/-! ## The theorem -/

/-- INV-1 and INV-2 at the request a decision reads. -/
def WFv (v : Rd A K P) : Op A K P → Prop
  | .approve _ _ _ i _ | .reject _ _ _ i =>
    ∀ r, v.req i = some r → r.id = i ∧ ∃ p, r.act = .pay p
  | _ => True


theorem cover_add (cfg : Cfg A) (v : Rd A K P) (c : A) (k : K) (a : A) (r : Role) :
    cstep cfg v (.add c k a r) =
      (sub cfg v (.add c k a r)).out
        (cstep cfgL (rep (cls cfg v (.add c k a r))).1.rd (rep (cls cfg v (.add c k a r))).2) := by
  by_cases h1 : c = v.owner <;> by_cases h2 : a = v.owner <;> by_cases h3 : a = c <;>
    cases h4 : v.prin k <;> by_cases h5 : v.regs = maxU <;> simp only [maxU] at h5 <;>
    simp [cls, rep, sub, cstep, DView.rd, lookupS, Sub.out, Sub.call, Sub.prin, Sub.a, Sub.k, Sub.n,
      tab, num, accts, h1, h2, h3, h4, h5, pFix, gRep, nrRep, inc, cfgL, maxU]

theorem cover_revoke (cfg : Cfg A) (v : Rd A K P) (c : A) (k : K) :
    cstep cfg v (.revoke c k) =
      (sub cfg v (.revoke c k)).out
        (cstep cfgL (rep (cls cfg v (.revoke c k))).1.rd (rep (cls cfg v (.revoke c k))).2) := by
  by_cases h1 : c = v.owner <;> cases h4 : v.prin k <;>
    simp [cls, rep, sub, cstep, DView.rd, lookupS, Sub.out, Sub.call, Sub.prin, Sub.a, Sub.k, Sub.n,
      tab, num, h1, h4, pFix, rid0]

theorem cover_request (cfg : Cfg A) (hc : cfg.maxPending = 16) (v : Rd A K P) (pred signer : A)
    (k : K) (x : Action P) :
    cstep cfg v (.request pred signer k x) =
      (sub cfg v (.request pred signer k x)).out
        (cstep cfgL (rep (cls cfg v (.request pred signer k x))).1.rd
          (rep (cls cfg v (.request pred signer k x))).2) := by
  by_cases h1 : pred = signer
  · cases h4 : v.prin k with
    | none => simp [cls, rep, sub, cstep, cauth, DView.rd, lookupS, Sub.out, h1, h4, acctOf]
    | some p =>
      by_cases h5 : v.nr = maxU <;> simp only [maxU] at h5 <;>
      by_cases h6 : p.role = .agent <;> by_cases h7 : p.acct = signer <;>
      by_cases h8 : p.pending ≥ 16 <;> cases x <;>
      simp [cls, rep, sub, cstep, cauth, DView.rd, lookupS, Sub.out, Sub.call, Sub.prin, Sub.a,
        Sub.k, Sub.n, Sub.req, Sub.act, tab, num, h1, h4, h5, h6, h7, h8, hc, acctOf, xcls, xRep,
        pRows, payRows, rid0, af0, nrRep, inc, cfgL, maxU] <;> omega
  · simp [cls, rep, sub, cstep, cauth, DView.rd, Sub.out, h1, acctOf]

/-- Unfold one side-by-side step of `cstep` on `v` and on its
representative, with the hypotheses in context. -/
syntax "ident_simp" : tactic
macro_rules
  | `(tactic| ident_simp) => `(tactic| simp [*, cls, rep, sub, sub.decAccts, sub.decKeys, sub.decNums, cstep, cauth, cdecidable,
      DView.rd, decView, lookupS, Sub.out, Sub.call, Sub.prin, Sub.a, Sub.k, Sub.n, Sub.req, Sub.act,
      Sub.dec, tab, num, acctOf, xcls, xRep, bcls, gcls, rcls, kEqOf, gOf, bRep, gRepP, rRep, decFix,
      pRows, payRows, rid0, rid1, afLe, afGt, idRep, ridR, nlRep, pendRep, gRep, inc, cfgL, maxU])

syntax "ident_simp_all" : tactic
macro_rules
  | `(tactic| ident_simp_all) => `(tactic| simp_all [-Nat.not_le, cls, rep, sub, sub.decAccts, sub.decKeys, sub.decNums, cstep, cauth, cdecidable,
      DView.rd, decView, lookupS, Sub.out, Sub.call, Sub.prin, Sub.a, Sub.k, Sub.n, Sub.req, Sub.act,
      Sub.dec, tab, num, acctOf, xcls, xRep, bcls, gcls, rcls, kEqOf, gOf, bRep, gRepP, rRep, decFix,
      pRows, payRows, rid0, rid1, afLe, afGt, idRep, ridR, nlRep, pendRep, gRep, inc, cfgL, maxU])

theorem cover_approve (cfg : Cfg A) (v : Rd A K P) (pred signer : A) (k : K) (i : Nat)
    (x : Action P) (hw : WFv v (.approve pred signer k i x)) :
    cstep cfg v (.approve pred signer k i x) =
      (sub cfg v (.approve pred signer k i x)).out
        (cstep cfgL (rep (cls cfg v (.approve pred signer k i x))).1.rd
          (rep (cls cfg v (.approve pred signer k i x))).2) := by
  have hw' := hw
  simp only [WFv] at hw'
  clear hw
  cases hr : v.req i with
  | none =>
    by_cases h1 : pred = signer <;> cases hb : v.prin k <;> ident_simp
    all_goals (rename_i b; by_cases h2 : b.role = .approver <;> by_cases h3 : b.acct = signer <;>
      cases b.role <;> ident_simp)
  | some r =>
  obtain ⟨hid, p, hp⟩ := hw' r hr
  clear hw'
  subst hid
  by_cases hk : r.key = k
  · subst hk
    by_cases h1 : pred = signer <;> cases hb : v.prin r.key <;> ident_simp
    all_goals (rename_i b; by_cases h2 : b.role = .approver <;> by_cases h3 : b.acct = signer <;>
      cases ha : r.appr <;> cases hj : r.rej <;> cases hrole : b.role <;> ident_simp)
  have hk' : k ≠ r.key := fun h => hk h.symm
  by_cases h1 : pred = signer
  rotate_left
  · cases hg : v.prin r.key <;> ident_simp
  cases hb : v.prin k with
  | none => cases hg : v.prin r.key <;> ident_simp
  | some b =>
  by_cases h2 : b.role = .approver
  rotate_left
  · have hag : b.role = .agent := by cases h : b.role <;> simp_all
    cases hg : v.prin r.key <;> ident_simp
  by_cases h3 : b.acct = signer
  rotate_left
  · cases hg : v.prin r.key <;> ident_simp
  cases ha : r.appr with
  | some _ => cases hg : v.prin r.key <;> ident_simp
  | none =>
  cases hj : r.rej with
  | some _ => cases hg : v.prin r.key <;> ident_simp
  | none =>
  cases hg : v.prin r.key with
  | none => ident_simp
  | some g =>
  by_cases hdec : g.role = .agent ∧ g.acct = r.acct ∧ g.activeFrom ≤ r.id
  rotate_left
  · by_cases g2 : g.acct = r.acct <;> by_cases g3 : g.activeFrom ≤ r.id <;>
      by_cases h5 : r.acct = signer <;> cases hgr : g.role <;>
      (try exact absurd ⟨by assumption, by assumption, by assumption⟩ hdec) <;> ident_simp_all
  obtain ⟨g1, g2, g3⟩ := hdec
  by_cases h4 : r.act = x
  rotate_left
  · cases x <;> ident_simp_all
  subst h4
  by_cases h5 : r.acct = signer
  · ident_simp
  have h5' : signer ≠ r.acct := fun h => h5 h.symm
  by_cases h6 : v.nl = maxU <;> simp only [maxU] at h6 <;> by_cases g4 : g.pending = 0 <;> ident_simp

theorem cover_reject (cfg : Cfg A) (v : Rd A K P) (pred signer : A) (k : K) (i : Nat)
    (hw : WFv v (.reject pred signer k i)) :
    cstep cfg v (.reject pred signer k i) =
      (sub cfg v (.reject pred signer k i)).out
        (cstep cfgL (rep (cls cfg v (.reject pred signer k i))).1.rd
          (rep (cls cfg v (.reject pred signer k i))).2) := by
  have hw' := hw
  simp only [WFv] at hw'
  clear hw
  cases hr : v.req i with
  | none =>
    by_cases h1 : pred = signer <;> cases hb : v.prin k <;> ident_simp
    all_goals (rename_i b; by_cases h2 : b.role = .approver <;> by_cases h3 : b.acct = signer <;>
      cases b.role <;> ident_simp)
  | some r =>
  obtain ⟨hid, p, hp⟩ := hw' r hr
  clear hw'
  subst hid
  by_cases hk : r.key = k
  · subst hk
    by_cases h1 : pred = signer <;> cases hb : v.prin r.key <;> ident_simp
    all_goals (rename_i b; by_cases h2 : b.role = .approver <;> by_cases h3 : b.acct = signer <;>
      cases ha : r.appr <;> cases hj : r.rej <;> cases hrole : b.role <;> ident_simp)
  have hk' : k ≠ r.key := fun h => hk h.symm
  by_cases h1 : pred = signer
  rotate_left
  · cases hg : v.prin r.key <;> ident_simp
  cases hb : v.prin k with
  | none => cases hg : v.prin r.key <;> ident_simp
  | some b =>
  by_cases h2 : b.role = .approver
  rotate_left
  · have hag : b.role = .agent := by cases h : b.role <;> simp_all
    cases hg : v.prin r.key <;> ident_simp
  by_cases h3 : b.acct = signer
  rotate_left
  · cases hg : v.prin r.key <;> ident_simp
  cases ha : r.appr with
  | some _ => cases hg : v.prin r.key <;> ident_simp
  | none =>
  cases hj : r.rej with
  | some _ => cases hg : v.prin r.key <;> ident_simp
  | none =>
  cases hg : v.prin r.key with
  | none => ident_simp
  | some g =>
  by_cases hdec : g.role = .agent ∧ g.acct = r.acct ∧ g.activeFrom ≤ r.id
  rotate_left
  · by_cases g2 : g.acct = r.acct <;> by_cases g3 : g.activeFrom ≤ r.id <;>
      by_cases h5 : r.acct = signer <;> cases hgr : g.role <;>
      (try exact absurd ⟨by assumption, by assumption, by assumption⟩ hdec) <;> ident_simp_all
  obtain ⟨g1, g2, g3⟩ := hdec
  by_cases h5 : r.acct = signer
  · ident_simp
  have h5' : signer ≠ r.acct := fun h => h5 h.symm
  by_cases g4 : g.pending = 0 <;> ident_simp

/-! ### Every class is enumerated -/

theorem mem_bools (b : Bool) : b ∈ bools := by cases b <;> simp [bools]
theorem mem_roles (r : Role) : r ∈ roles := by cases r <;> simp [roles]

theorem mem_fm {α β : Type} {l : List α} {f : α → List β} {a : α} {b : β} (ha : a ∈ l)
    (hb : b ∈ f a) : b ∈ l.flatMap f := List.mem_flatMap.2 ⟨a, ha, hb⟩

theorem mem_opts {α : Type} {l : List α} : ∀ {o : Option α}, (∀ a, o = some a → a ∈ l) → o ∈ opts l
  | none, _ => by simp [opts]
  | some a, h => by simp [opts, h a rfl]

theorem mem_allB (b : BCls) : b ∈ allB :=
  mem_fm (mem_roles b.role) (List.mem_map.2 ⟨b.acctEq, mem_bools _, rfl⟩)
theorem mem_allG (g : GCls) : g ∈ allG :=
  mem_fm (mem_roles g.role) (mem_fm (mem_bools g.acctEq) (mem_fm (mem_bools g.afLe)
    (List.mem_map.2 ⟨g.pend0, mem_bools _, rfl⟩)))
theorem mem_allR (r : RCls) : r ∈ allR :=
  mem_fm (mem_bools r.appr) (mem_fm (mem_bools r.rej) (List.mem_map.2 ⟨r.acctEq, mem_bools _, rfl⟩))
theorem mem_allP (p : PCls) : p ∈ allP :=
  mem_fm (mem_roles p.role) (mem_fm (mem_bools p.acctEq) (List.mem_map.2 ⟨p.full, mem_bools _, rfl⟩))

/-- The decision classes: `g` is `none` when the request's key is the
call key, and the action is `eq` only when there is a request. -/
theorem dec_shape (v : Rd A K P) (signer : A) (k : K) (i : Nat) (x : Action P) :
    gOf v k (v.req i) ∈ (if kEqOf k (v.req i) then [none] else opts allG) ∧
    xcls x (v.req i) ∈ (if ((v.req i).map (rcls signer)).isSome then [XCls.eq, .pay, .empty, .tooLong]
                        else [XCls.pay, .empty, .tooLong]) := by
  cases hr : v.req i with
  | none => cases x <;> simp [gOf, kEqOf, xcls, opts]
  | some r =>
    constructor
    · by_cases hk : r.key = k
      · simp [gOf, kEqOf, hk]
      · simp only [gOf, kEqOf, hk, ite_false, Option.any_some, decide_false]
        exact mem_opts fun g _ => mem_allG g
    · simp only [Option.map_some, Option.isSome_some, ite_true]
      cases xcls x (some r) <;> simp

theorem cls_mem (cfg : Cfg A) (v : Rd A K P) (op : Op A K P) : cls cfg v op ∈ allCls := by
  simp only [allCls, List.mem_append]
  cases op with
  | add c k a r =>
    refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
    refine mem_fm (mem_bools _) (mem_fm (a := if a = v.owner then 0 else if a = c then 1 else 2) ?_
      (mem_fm (mem_roles r) (mem_fm (mem_bools _) (List.mem_map.2 ⟨_, mem_bools _, rfl⟩))))
    split
    · simp
    · split <;> simp
  | revoke c k =>
    exact Or.inl (Or.inl (Or.inl (Or.inr (mem_fm (mem_bools _) (List.mem_map.2 ⟨_, mem_bools _, rfl⟩)))))
  | request pred signer k x =>
    refine Or.inl (Or.inl (Or.inr ?_))
    refine mem_fm (mem_bools _) (mem_fm (mem_opts fun p _ => mem_allP p) (mem_fm ?_
      (List.mem_map.2 ⟨_, mem_bools _, rfl⟩)))
    cases x <;> simp [xcls]
  | approve pred signer k i x =>
    refine Or.inl (Or.inr ?_)
    have ⟨hg, hx⟩ := dec_shape v signer k i x
    exact mem_fm (mem_bools _) (mem_fm (mem_opts fun b _ => mem_allB b) (mem_fm (mem_bools _)
      (mem_fm hg (mem_fm (mem_opts fun r _ => mem_allR r) (mem_fm hx
        (List.mem_map.2 ⟨_, mem_bools _, rfl⟩))))))
  | reject pred signer k i =>
    refine Or.inr ?_
    have ⟨hg, _⟩ := dec_shape v signer k i (.empty : Action P)
    exact mem_fm (mem_bools _) (mem_fm (mem_opts fun b _ => mem_allB b) (mem_fm (mem_bools _)
      (mem_fm hg (List.mem_map.2 ⟨_, mem_opts fun r _ => mem_allR r, rfl⟩))))

/-! ### LEAN-COVER -/

/-- LINK's domain is complete for `cstep`: every view's class is one LINK
runs, and `cstep` on the view is `cstep` on the class's representative,
carried back by the view's table. -/
theorem cover (cfg : Cfg A) (hc : cfg.maxPending = 16) (v : Rd A K P) (op : Op A K P)
    (hw : WFv v op) :
    cls cfg v op ∈ allCls ∧
    cstep cfg v op =
      (sub cfg v op).out (cstep cfgL (rep (cls cfg v op)).1.rd (rep (cls cfg v op)).2) := by
  refine ⟨cls_mem cfg v op, ?_⟩
  cases op with
  | add c k a r => exact cover_add cfg v c k a r
  | revoke c k => exact cover_revoke cfg v c k
  | request pred signer k x => exact cover_request cfg hc v pred signer k x
  | approve pred signer k i x => exact cover_approve cfg v pred signer k i x hw
  | reject pred signer k i => exact cover_reject cfg v pred signer k i hw

/-! ## Corollaries -/

/-! ### LEAN-FRAME: `cstep` reads only the footprint -/

/-- `v` and `w` agree on what `op` can read: the owner, the call key's
principal, the request at `i` and its key's principal, and the counters. -/
def Agree (v w : Rd A K P) : Op A K P → Prop
  | .add _ k _ _ => w.owner = v.owner ∧ w.prin k = v.prin k ∧ w.regs = v.regs ∧ w.nr = v.nr
  | .revoke _ k => w.owner = v.owner ∧ w.prin k = v.prin k
  | .request _ _ k _ => w.prin k = v.prin k ∧ w.nr = v.nr
  | .approve _ _ k i _ => w.prin k = v.prin k ∧ w.req i = v.req i ∧ w.nl = v.nl ∧
      ∀ r, v.req i = some r → w.prin r.key = v.prin r.key
  | .reject _ _ k i => w.prin k = v.prin k ∧ w.req i = v.req i ∧
      ∀ r, v.req i = some r → w.prin r.key = v.prin r.key

theorem frame (cfg : Cfg A) (v w : Rd A K P) (op : Op A K P) (h : Agree v w op) :
    cstep cfg w op = cstep cfg v op := by
  cases op with
  | add c k a r => obtain ⟨h1, h2, h3, h4⟩ := h; simp [cstep, h1, h2, h3, h4]
  | revoke c k => obtain ⟨h1, h2⟩ := h; simp [cstep, h1, h2]
  | request pred signer k x => obtain ⟨h1, h2⟩ := h; simp [cstep, cauth, h1, h2]
  | approve pred signer k i x =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    cases hr : v.req i with
    | none => simp [cstep, cauth, cdecidable, h1, h2, h3, hr]
    | some r => simp [cstep, cauth, cdecidable, h1, h2, h3, hr, h4 r hr]
  | reject pred signer k i =>
    obtain ⟨h1, h2, h4⟩ := h
    cases hr : v.req i with
    | none => simp [cstep, cauth, cdecidable, h1, h2, hr]
    | some r => simp [cstep, cauth, cdecidable, h1, h2, hr, h4 r hr]

/-! ### LEAN-REN: `cstep` commutes with injective renaming -/

/-- Injective renamings of accounts, keys and payloads. -/
structure Ren (A K P A' K' P' : Type) where
  a : A → A'
  k : K → K'
  p : P → P'
  ia : ∀ x y, a x = a y → x = y
  ik : ∀ x y, k x = k y → x = y
  ip : ∀ x y, p x = p y → x = y

namespace Ren

variable {A' K' P' : Type} [DecidableEq A'] [DecidableEq K'] [DecidableEq P']
variable (ρ : Ren A K P A' K' P')

theorem a_eq (x y : A) : ρ.a x = ρ.a y ↔ x = y := ⟨ρ.ia x y, fun h => h ▸ rfl⟩
theorem k_eq (x y : K) : ρ.k x = ρ.k y ↔ x = y := ⟨ρ.ik x y, fun h => h ▸ rfl⟩

def act : Action P → Action P'
  | .pay x => .pay (ρ.p x)
  | .empty => .empty
  | .tooLong => .tooLong

theorem act_eq (x y : Action P) : ρ.act x = ρ.act y ↔ x = y := by
  cases x <;> cases y <;> simp [act] <;> exact ⟨ρ.ip _ _, fun h => h ▸ rfl⟩

@[simp] theorem act_empty (x : Action P) : ρ.act x = .empty ↔ x = .empty := by cases x <;> simp [act]
@[simp] theorem act_tooLong (x : Action P) : ρ.act x = .tooLong ↔ x = .tooLong := by
  cases x <;> simp [act]

def prin (q : CPrin A) : CPrin A' :=
  { acct := ρ.a q.acct, role := q.role, rid := q.rid, activeFrom := q.activeFrom, pending := q.pending }
def dec (d : CDec A K) : CDec A' K' := { idx := d.idx, acct := ρ.a d.acct, key := ρ.k d.key, rid := d.rid }
def req (r : CReq A K P) : CReq A' K' P' :=
  { id := r.id, acct := ρ.a r.acct, key := ρ.k r.key, rid := r.rid, act := ρ.act r.act,
    appr := r.appr.map ρ.dec, rej := r.rej.map ρ.dec }

def call : Call A K P → Call A' K' P'
  | .incG => .incG
  | .insP k q => .insP (ρ.k k) (ρ.prin q)
  | .rmP k => .rmP (ρ.k k)
  | .pushR r => .pushR (ρ.req r)
  | .replR r => .replR (ρ.req r)
  | .pushA i => .pushA i
  | .insRev g => .insRev g

def op : Op A K P → Op A' K' P'
  | .add c k a r => .add (ρ.a c) (ρ.k k) (ρ.a a) r
  | .revoke c k => .revoke (ρ.a c) (ρ.k k)
  | .request pr sg k x => .request (ρ.a pr) (ρ.a sg) (ρ.k k) (ρ.act x)
  | .approve pr sg k i x => .approve (ρ.a pr) (ρ.a sg) (ρ.k k) i (ρ.act x)
  | .reject pr sg k i => .reject (ρ.a pr) (ρ.a sg) (ρ.k k) i

/-- `w` is `v` renamed by `ρ` (keys outside `ρ`'s image are not read). -/
structure Rel (v : Rd A K P) (w : Rd A' K' P') : Prop where
  owner : w.owner = ρ.a v.owner
  prin : ∀ k, w.prin (ρ.k k) = (v.prin k).map ρ.prin
  req : ∀ i, w.req i = (v.req i).map ρ.req
  nr : w.nr = v.nr
  nl : w.nl = v.nl
  regs : w.regs = v.regs

end Ren

syntax "ren_simp" : tactic
macro_rules
  | `(tactic| ren_simp) => `(tactic| simp [*, cstep, cauth, cdecidable, Ren.op, Ren.call, Ren.prin,
      Ren.req, Ren.dec])

theorem rename {A' K' P' : Type} [DecidableEq A'] [DecidableEq K'] [DecidableEq P']
    (ρ : Ren A K P A' K' P') (cfg : Cfg A) (cfg' : Cfg A') (hc : cfg'.maxPending = cfg.maxPending)
    (v : Rd A K P) (w : Rd A' K' P') (hv : ρ.Rel v w) (op : Op A K P) :
    cstep cfg' w (ρ.op op) = ((cstep cfg v op).1, (cstep cfg v op).2.map ρ.call) := by
  have ha := ρ.a_eq
  have hk := ρ.k_eq
  have hx := ρ.act_eq
  obtain ⟨hvo, hvp, hvq, hvnr, hvnl, hvg⟩ := hv
  cases op with
  | add c k a r =>
    by_cases h1 : c = v.owner <;> cases h : v.prin k <;> by_cases h3 : v.regs = maxU <;> ren_simp
  | revoke c k => by_cases h1 : c = v.owner <;> cases h : v.prin k <;> ren_simp
  | request pred signer k x =>
    by_cases h1 : pred = signer <;> cases h : v.prin k <;> ren_simp
    rename_i q
    by_cases h2 : q.role = .agent <;> by_cases h3 : q.acct = signer <;> cases x <;>
      by_cases h4 : cfg.maxPending ≤ q.pending <;> by_cases h5 : v.nr = maxU <;> ren_simp
  | approve pred signer k i x =>
    by_cases h1 : pred = signer
    rotate_left
    · ren_simp
    cases h : v.prin k with
    | none => ren_simp
    | some b =>
    by_cases h2 : b.role = .approver
    rotate_left
    · ren_simp
    by_cases h3 : b.acct = signer
    rotate_left
    · ren_simp
    cases hr : v.req i with
    | none => ren_simp
    | some r =>
    cases ha' : r.appr <;> cases hj : r.rej <;> cases hg : v.prin r.key <;> try ren_simp
    rename_i g
    by_cases g1 : g.role = .agent ∧ g.acct = r.acct ∧ g.activeFrom ≤ r.id
    rotate_left
    · ren_simp
    by_cases h4 : r.act = x <;> by_cases h5 : signer = r.acct <;> by_cases h6 : v.nl = maxU <;> ren_simp
  | reject pred signer k i =>
    by_cases h1 : pred = signer
    rotate_left
    · ren_simp
    cases h : v.prin k with
    | none => ren_simp
    | some b =>
    by_cases h2 : b.role = .approver
    rotate_left
    · ren_simp
    by_cases h3 : b.acct = signer
    rotate_left
    · ren_simp
    cases hr : v.req i with
    | none => ren_simp
    | some r =>
    cases ha' : r.appr <;> cases hj : r.rej <;> cases hg : v.prin r.key <;> try ren_simp
    rename_i g
    by_cases g1 : g.role = .agent ∧ g.acct = r.acct ∧ g.activeFrom ≤ r.id
    rotate_left
    · ren_simp
    by_cases h5 : signer = r.acct <;> ren_simp

/-! ### `WFv` holds on every store the chain reaches -/

/-- A concrete store with INV-1 (`WF`, LEAN-DELTA's premise) whose
abstraction has INV-2 (`TypeOK.act`, part of `Inv`, so on every reachable
state by `reach_inv`) meets `cover`'s premise for every operation. -/
theorem wfv_of_store (s : CStore A K P) (g : List Ghost) (hW : WF s) (hT : TypeOK (α s g))
    (op : Op A K P) : WFv s.rd op := by
  have key : ∀ i r, s.rd.req i = some r → r.id = i ∧ ∃ p, r.act = .pay p := by
    intro i r hr
    refine ⟨hW.ids i r hr, ?_⟩
    have h := hT.act i (toR r) (by rw [req_α]; simp [CStore.rd] at hr; simp [hr])
    simpa [toR] using h
  cases op with
  | approve _ _ _ i _ => exact key i
  | reject _ _ _ i => exact key i
  | _ => trivial

end Approval.Ident
