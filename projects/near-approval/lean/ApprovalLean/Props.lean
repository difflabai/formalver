/-
Properties of the machine: a transcription of `tla/ApprovalProps.tla`.
IDs are the strategy.md catalogue's. Quantifiers over `Keys` range over
every key (an absent key reads as `noPrincipal`); quantifiers over `Ids`
range over `i` with `s.req i = some r`.
-/
import ApprovalLean.Machine

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## The invariant -/

/-- `TypeOK`, as far as the Lean types don't already give it, plus the
representation invariants of the map and set encodings: the principal map
has distinct keys and holds only registered principals, and `revoked` has
no duplicates. -/
structure TypeOK (s : State A K P) : Prop where
  pkeys : (s.principals.map Prod.fst).Nodup
  preg : ∀ e ∈ s.principals, e.2.reg = true
  /-- INV-2: stored actions are payloads. -/
  act : ∀ i r, s.req i = some r → ∃ x, r.act = .pay x
  unappr : ∀ i r, s.req i = some r → r.appr = false →
    r.aidx = 0 ∧ r.aacct = r.acct ∧ r.akey = r.key ∧ r.arid = 0
  unrj : ∀ i r, s.req i = some r → r.rj = false →
    r.racct = r.acct ∧ r.rkey = r.key ∧ r.rrid = 0
  revNodup : s.revoked.Nodup
  ghostLen : s.ghost.length = s.nr

/-- INV-3: log → request. -/
def Inv3 (s : State A K P) : Prop :=
  ∀ j (hj : j < s.nl), ∃ r, s.req s.log[j] = some r ∧ r.appr = true ∧ r.aidx = j

/-- INV-4: request → log. -/
def Inv4 (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.appr = true → ∃ h : r.aidx < s.nl, s.log[r.aidx] = i

/-- INV-5: separation of duties. -/
def Inv5 (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.appr = true → r.aacct ≠ r.acct

/-- INV-6: approver key differs from agent key. -/
def Inv6 (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.appr = true → r.akey ≠ r.key

/-- INV-7: registration bound. -/
def Inv7 (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ k, (prin cfg s k).reg = true → (prin cfg s k).activeFrom ≤ s.nr

/-- INV-8: registration provenance, including the registration id. -/
def Inv8 (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ k i r, s.req i = some r → (prin cfg s k).reg = true → r.key = k →
    (prin cfg s k).activeFrom ≤ i →
    r.acct = (prin cfg s k).acct ∧ (prin cfg s k).role = .agent ∧ r.rid = (prin cfg s k).rid

/-- INV-9: pending count, and the cap. -/
def Inv9 (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ k, (prin cfg s k).reg = true →
    (prin cfg s k).pending = pend cfg s k ∧ (prin cfg s k).pending ≤ cfg.maxPending

/-- INV-11: live registration ids are issued, distinct, and not revoked. -/
def Inv11 (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ k, (prin cfg s k).reg = true →
    (prin cfg s k).rid < s.regs ∧ (prin cfg s k).rid ∉ s.revoked ∧
    ∀ k2, k2 ≠ k → (prin cfg s k2).reg = true → (prin cfg s k2).rid ≠ (prin cfg s k).rid

/-- INV-12: revoked ids were issued. -/
def Inv12 (s : State A K P) : Prop := ∀ g ∈ s.revoked, g < s.regs

/-- INV-13: at most one decision per request. -/
def Inv13 (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → ¬(r.appr = true ∧ r.rj = true)

/-- INV-14: recorded registration ids were issued. -/
def Inv14 (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r →
    r.rid < s.regs ∧ (r.appr = true → r.arid < s.regs) ∧ (r.rj = true → r.rrid < s.regs)

/-- INV-15: registration accounting, `regs = |revoked| + |{k : reg}|`. The
principal map holds exactly the registered keys, without duplicates
(`TypeOK`), so its length is the second count. -/
def Inv15 (s : State A K P) : Prop := s.regs = s.revoked.length + s.principals.length

/-- INV-16: registration binding. -/
def Inv16 (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ k i r, (prin cfg s k).reg = true → s.req i = some r →
    (r.rid = (prin cfg s k).rid →
      r.key = k ∧ r.acct = (prin cfg s k).acct ∧ (prin cfg s k).role = .agent) ∧
    (r.appr = true → r.arid = (prin cfg s k).rid →
      r.akey = k ∧ r.aacct = (prin cfg s k).acct ∧ (prin cfg s k).role = .approver) ∧
    (r.rj = true → r.rrid = (prin cfg s k).rid →
      r.rkey = k ∧ r.racct = (prin cfg s k).acct ∧ (prin cfg s k).role = .approver)

/-- INV-5 and INV-6 for rejections. -/
def Inv5r (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.rj = true → r.racct ≠ r.acct ∧ r.rkey ≠ r.key

/-- LEM-1: no duplicates in the log. -/
def Lem1 (s : State A K P) : Prop := s.log.Nodup

/-- LEM-2: log length = approved count. -/
def Lem2 (s : State A K P) : Prop :=
  s.nl = countIdx (fun _ r => r.appr) s.requests 0

/-- TR-1 provenance, through the ghost. -/
def Provenance (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.decided = true →
    ∃ g, s.ghost[i]? = some g ∧ g.cont = true ∧ g.decOk = true

/-- The core's `active_from` check decides exactly "the registration the
request was made under is unbroken". -/
def RidLive (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.decided = false → (unbrokenR cfg s r = liveR cfg s i r)

/-- `EligibleKey(i, k)`. -/
def EligibleKey (cfg : Cfg A) (s : State A K P) (r : Request A K P) (k : K) : Prop :=
  (prin cfg s k).reg = true ∧ (prin cfg s k).role = .approver ∧ (prin cfg s k).acct ≠ r.acct

/-- TLA-LIVE-2 (`Approvable`): a pending request can be approved and
rejected by every Approver key of another account. -/
def Approvable (cfg : Cfg A) (s : State A K P) : Prop :=
  ∀ i r k, s.req i = some r → r.decided = false → liveR cfg s i r = true →
    EligibleKey cfg s r k →
    approveErr cfg s (prin cfg s k).acct (prin cfg s k).acct k i r.act = .ok ∧
    rejectErr cfg s (prin cfg s k).acct (prin cfg s k).acct k i = .ok

/-- `Inv`. -/
structure Inv (cfg : Cfg A) (s : State A K P) : Prop where
  typeOK : TypeOK s
  inv3 : Inv3 s
  inv4 : Inv4 s
  inv5 : Inv5 s
  inv6 : Inv6 s
  inv7 : Inv7 cfg s
  inv8 : Inv8 cfg s
  inv9 : Inv9 cfg s
  inv11 : Inv11 cfg s
  inv12 : Inv12 s
  inv13 : Inv13 s
  inv14 : Inv14 s
  inv15 : Inv15 s
  inv16 : Inv16 cfg s
  inv5r : Inv5r s
  lem1 : Lem1 s
  lem2 : Lem2 s
  provenance : Provenance s
  ridLive : RidLive cfg s
  approvable : Approvable cfg s

/-! ## Action properties, over a step `s → s'` -/

/-- HIST-1: request content is immutable and never removed. -/
def Hist1 (s s' : State A K P) : Prop :=
  s.nr ≤ s'.nr ∧ ∀ i r, s.req i = some r →
    ∃ r', s'.req i = some r' ∧ r'.acct = r.acct ∧ r'.key = r.key ∧ r'.act = r.act

/-- HIST-2 (and HIST-9): decisions are immutable. -/
def Hist2 (s s' : State A K P) : Prop :=
  ∀ i r, s.req i = some r → r.decided = true → s'.req i = some r

/-- HIST-3: the log is append-only. -/
def Hist3 (s s' : State A K P) : Prop :=
  s.nl ≤ s'.nl ∧ s'.log.take s.nl = s.log

/-- HIST-8 / TR-3: Void is terminal. -/
def Hist8 (cfg : Cfg A) (s s' : State A K P) : Prop :=
  ∀ i, void cfg s i → void cfg s' i

/-- HIST-7: the owner can't rewrite history. Principals compare as the
TLA+ function `prin`. -/
def Hist7 (cfg : Cfg A) (s s' : State A K P) : Prop :=
  (prin cfg s' ≠ prin cfg s ∧ s'.requests = s.requests) → s'.log = s.log

/-- HIST-10: the registration counter never decreases, and a revocation is
recorded only for a live registration, never removed. -/
def Hist10 (cfg : Cfg A) (s s' : State A K P) : Prop :=
  s.regs ≤ s'.regs ∧ (∀ g ∈ s.revoked, g ∈ s'.revoked) ∧
    ∀ g ∈ s'.revoked, g ∉ s.revoked → ∃ k, (prin cfg s k).reg = true ∧ (prin cfg s k).rid = g

/-- `StepProps`. -/
structure StepProps (cfg : Cfg A) (s s' : State A K P) : Prop where
  hist1 : Hist1 s s'
  hist2 : Hist2 s s'
  hist3 : Hist3 s s'
  hist7 : Hist7 cfg s s'
  hist8 : Hist8 cfg s s'
  hist10 : Hist10 cfg s s'

end Approval
