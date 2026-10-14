/- LEAN-IND, inductive step for `Reject`: `Inv /\ Reject => Inv'`, for states of any size. -/
import ApprovalLean.Lemmas
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

namespace InvReject

variable {cfg : Cfg A} {s : State A K P} {p sg : A} {k : K} {i : Nat} {r : Request A K P}

/-- The record of request `i` after `Reject`. -/
private def rreq (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (r : Request A K P) :
    Request A K P :=
  { r with rj := true, racct := sg, rkey := k, rrid := (prin cfg s k).rid }

/-- The ghost record `Reject` writes at index `i`. -/
private def rghost (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (r : Request A K P) :
    Ghost :=
  { cont := unbrokenR cfg s r,
    decOk := (prin cfg s k).reg && (prin cfg s k).role == .approver
               && (prin cfg s k).acct == sg }

/-- The post-state of `Reject` on request `i` with record `r`. -/
private def post (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (i : Nat)
    (r : Request A K P) : State A K P :=
  { s with
    requests := s.requests.set i (rreq cfg s sg k r),
    principals := decidePrincipals s r,
    ghost := s.ghost.set i (rghost cfg s sg k r) }

/-- The facts a successful `Reject` guard gives. -/
private structure Facts (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (i : Nat)
    (r : Request A K P) : Prop where
  hr : s.req i = some r
  kreg : (prin cfg s k).reg = true
  krole : (prin cfg s k).role = .approver
  kacct : (prin cfg s k).acct = sg
  unappr : r.appr = false
  unrj : r.rj = false
  live : liveR cfg s i r = true
  self : sg ≠ r.acct

/-! ### The guard -/

omit [DecidableEq P] in
private theorem guard (hok : rejectErr cfg s p sg k i = .ok) :
    ∃ r, s.req i = some r ∧ (prin cfg s k).reg = true ∧ (prin cfg s k).role = .approver ∧
      (prin cfg s k).acct = sg ∧ r.appr = false ∧ r.rj = false ∧ liveR cfg s i r = true ∧
      sg ≠ r.acct := by
  unfold rejectErr authErr decideErr at hok
  by_cases h1 : p = sg <;> simp [h1] at hok
  by_cases h2 : (prin cfg s k).reg = true <;> simp [h2] at hok
  by_cases h3 : (prin cfg s k).role = .approver <;> simp [h3] at hok
  by_cases h4 : (prin cfg s k).acct = sg <;> simp [h4] at hok
  cases hr : s.req i with
  | none => simp [hr] at hok
  | some r =>
    simp [hr] at hok
    refine ⟨r, rfl, h2, h3, h4, ?_⟩
    by_cases h5 : r.appr = true <;> simp [h5] at hok
    by_cases h6 : r.rj = true <;> simp [h6] at hok
    by_cases h7 : liveR cfg s i r = true <;> simp [h7] at hok
    by_cases h8 : sg = r.acct <;> simp [h8] at hok
    simp_all

omit [DecidableEq P] in
private theorem e_eq (hr : s.req i = some r) :
    effect cfg s (.reject p sg k i) = post cfg s sg k i r := by
  simp only [effect, hr]; rfl

/-! ### Derived facts -/

section Derived
variable (hF : Facts cfg s sg k i r)
include hF

private theorem hi : i < s.nr := req_lt hF.hr

private theorem rget : s.requests[i]'(hi hF) = r := (req_eq_some hF.hr).2

omit [DecidableEq P] in
private theorem live' : (prin cfg s r.key).reg = true ∧ (prin cfg s r.key).role = .agent ∧
    (prin cfg s r.key).acct = r.acct ∧ (prin cfg s r.key).activeFrom ≤ i := by
  have h := hF.live
  simp only [liveR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

omit [DecidableEq P] in
private theorem k_ne : k ≠ r.key := by
  intro he
  have h1 := hF.krole
  have h2 := (live' hF).2.1
  rw [he] at h1
  rw [h1] at h2
  cases h2

end Derived

/-! ### The post-state, field by field -/

omit [DecidableEq P] in
private theorem post_requests : (post cfg s sg k i r).requests =
    s.requests.set i (rreq cfg s sg k r) := rfl
omit [DecidableEq P] in
private theorem post_principals : (post cfg s sg k i r).principals =
    pmodify r.key (fun q => { q with pending := q.pending - 1 }) s.principals := rfl
omit [DecidableEq P] in
private theorem post_log : (post cfg s sg k i r).log = s.log := rfl
omit [DecidableEq P] in
private theorem post_regs : (post cfg s sg k i r).regs = s.regs := rfl
omit [DecidableEq P] in
private theorem post_revoked : (post cfg s sg k i r).revoked = s.revoked := rfl
omit [DecidableEq P] in
private theorem post_ghost : (post cfg s sg k i r).ghost =
    s.ghost.set i (rghost cfg s sg k r) := rfl
omit [DecidableEq P] in
private theorem post_nr : (post cfg s sg k i r).nr = s.nr := by
  simp [State.nr, post_requests]
omit [DecidableEq P] in
private theorem post_nl : (post cfg s sg k i r).nl = s.nl := rfl

private theorem post_req_self (hF : Facts cfg s sg k i r) :
    (post cfg s sg k i r).req i = some (rreq cfg s sg k r) := by
  simp only [State.req, post_requests]
  exact List.getElem?_set_self (hi hF)

omit [DecidableEq P] in
private theorem post_req_ne {j : Nat} (h : j ≠ i) :
    (post cfg s sg k i r).req j = s.req j := by
  simp only [State.req, post_requests]
  exact List.getElem?_set_ne (Ne.symm h)

private theorem post_req_cases (hF : Facts cfg s sg k i r) {j : Nat} {r' : Request A K P}
    (h : (post cfg s sg k i r).req j = some r') :
    (j = i ∧ r' = rreq cfg s sg k r) ∨ (j ≠ i ∧ s.req j = some r') := by
  by_cases hj : j = i
  · subst hj
    rw [post_req_self hF] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [post_req_ne hj] at h
    exact Or.inr ⟨hj, h⟩

/-! ### Principals after the step -/

private theorem prin_eq (hT : TypeOK s) (hF : Facts cfg s sg k i r) (k' : K) :
    prin cfg (post cfg s sg k i r) k' =
      { prin cfg s k' with
        pending := if k' = r.key then (prin cfg s k').pending - 1
                   else (prin cfg s k').pending } := by
  rw [prin_def, post_principals, plookup_pmodify]
  by_cases h : k' = r.key
  · subst h
    rw [ite_eq_left rfl, prin_of_reg cfg hT (live' hF).1]
    simp
  · rw [ite_eq_right h, ite_eq_right h]
    simp [prin_def]

section Fields
variable (hT : TypeOK s) (hF : Facts cfg s sg k i r) (k' : K)
include hT hF

private theorem p_reg : (prin cfg (post cfg s sg k i r) k').reg = (prin cfg s k').reg := by
  rw [prin_eq hT hF]
private theorem p_acct : (prin cfg (post cfg s sg k i r) k').acct = (prin cfg s k').acct := by
  rw [prin_eq hT hF]
private theorem p_role : (prin cfg (post cfg s sg k i r) k').role = (prin cfg s k').role := by
  rw [prin_eq hT hF]
private theorem p_rid : (prin cfg (post cfg s sg k i r) k').rid = (prin cfg s k').rid := by
  rw [prin_eq hT hF]
private theorem p_from : (prin cfg (post cfg s sg k i r) k').activeFrom =
    (prin cfg s k').activeFrom := by
  rw [prin_eq hT hF]
private theorem p_pending : (prin cfg (post cfg s sg k i r) k').pending =
    if k' = r.key then (prin cfg s k').pending - 1 else (prin cfg s k').pending := by
  rw [prin_eq hT hF]

end Fields

private theorem liveR_eq (hT : TypeOK s) (hF : Facts cfg s sg k i r) (j : Nat)
    (r' : Request A K P) :
    liveR cfg (post cfg s sg k i r) j r' = liveR cfg s j r' := by
  simp only [liveR, p_reg hT hF, p_role hT hF, p_acct hT hF, p_from hT hF]

private theorem unbrokenR_eq (hT : TypeOK s) (hF : Facts cfg s sg k i r)
    (r' : Request A K P) :
    unbrokenR cfg (post cfg s sg k i r) r' = unbrokenR cfg s r' := by
  simp only [unbrokenR, p_reg hT hF, p_rid hT hF]

/-! ### The invariant, conjunct by conjunct -/

section Conj
variable (hI : Inv cfg s) (hF : Facts cfg s sg k i r)
include hI hF

private theorem typeOK : TypeOK (post cfg s sg k i r) := by
  have hT := hI.typeOK
  refine ⟨?_, ?_, ?_, ?_, ?_, hT.revNodup, ?_⟩
  · rw [post_principals, pmodify_keys]; exact hT.pkeys
  · intro e he
    rw [post_principals] at he
    obtain ⟨e0, he0, -, h | h⟩ := mem_pmodify he
    · rw [h]; exact hT.preg e0 he0
    · rw [h]; exact hT.preg e0 he0
  · intro j r' h
    rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
    · exact hT.act j r hF.hr
    · exact hT.act j r' h
  · intro j r' h hap
    rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
    · exact hT.unappr j r hF.hr hF.unappr
    · exact hT.unappr j r' h hap
  · intro j r' h hrj
    rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
    · simp [rreq] at hrj
    · exact hT.unrj j r' h hrj
  · simp only [post_ghost, List.length_set, post_nr]; exact hT.ghostLen

private theorem inv3 : Inv3 (post cfg s sg k i r) := by
  intro j hj
  have hj' : j < s.nl := hj
  obtain ⟨r0, h0, ha, hidx⟩ := hI.inv3 j hj'
  have hne : s.log[j] ≠ i := by
    intro he
    rw [he, hF.hr] at h0
    cases h0
    rw [hF.unappr] at ha
    cases ha
  refine ⟨r0, ?_, ha, hidx⟩
  show (post cfg s sg k i r).req (s.log[j]'hj') = some r0
  rw [post_req_ne hne]; exact h0

private theorem inv4 : Inv4 (post cfg s sg k i r) := by
  intro j r' h hap
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · simp [rreq, hF.unappr] at hap
  · exact hI.inv4 j r' h hap

private theorem inv5 : Inv5 (post cfg s sg k i r) := by
  intro j r' h hap
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · simp [rreq, hF.unappr] at hap
  · exact hI.inv5 j r' h hap

private theorem inv6 : Inv6 (post cfg s sg k i r) := by
  intro j r' h hap
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · simp [rreq, hF.unappr] at hap
  · exact hI.inv6 j r' h hap

private theorem inv7 : Inv7 cfg (post cfg s sg k i r) := by
  intro k' hreg
  rw [p_reg hI.typeOK hF] at hreg
  rw [p_from hI.typeOK hF, post_nr]
  exact hI.inv7 k' hreg

private theorem inv8 : Inv8 cfg (post cfg s sg k i r) := by
  intro k' j r' h hreg hkey hfrom
  have hT := hI.typeOK
  rw [p_reg hT hF] at hreg
  rw [p_from hT hF] at hfrom
  rw [p_acct hT hF, p_role hT hF, p_rid hT hF]
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact hI.inv8 k' j r hF.hr hreg hkey hfrom
  · exact hI.inv8 k' j r' h hreg hkey hfrom

private theorem pend_post (k' : K) :
    pend cfg (post cfg s sg k i r) k' =
      countIdx (fun j (q : Request A K P) => q.key == k' && !q.decided &&
          decide ((prin cfg s k').activeFrom ≤ j))
        (s.requests.set i (rreq cfg s sg k r)) 0 := by
  simp only [pend, p_from hI.typeOK hF, post_requests]

private theorem inv9 : Inv9 cfg (post cfg s sg k i r) := by
  intro k' hreg
  have hT := hI.typeOK
  rw [p_reg hT hF] at hreg
  obtain ⟨hp, hmax⟩ := hI.inv9 k' hreg
  rw [p_pending hT hF, pend_post hI hF]
  have hc := countIdx_set (fun j (q : Request A K P) => q.key == k' && !q.decided &&
          decide ((prin cfg s k').activeFrom ≤ j)) s.requests 0 i (rreq cfg s sg k r) (hi hF)
  rw [rget hF] at hc
  have hd : (rreq cfg s sg k r).decided = true := by simp [rreq, Request.decided]
  have hrd : r.decided = false := by simp [Request.decided, hF.unappr, hF.unrj]
  unfold pend at hp
  by_cases hk : k' = r.key
  · subst hk
    have hfr := (live' hF).2.2.2
    simp [hd, hrd, hfr] at hc
    simp only [↓reduceIte]
    omega
  · have hk' : (r.key == k') = false := by simp [Ne.symm hk]
    simp [hd, hrd, hk'] at hc
    simp only [hk, ↓reduceIte]
    omega

private theorem inv11 : Inv11 cfg (post cfg s sg k i r) := by
  intro k' hreg
  have hT := hI.typeOK
  rw [p_reg hT hF] at hreg
  rw [p_rid hT hF, post_regs, post_revoked]
  obtain ⟨h1, h2, h3⟩ := hI.inv11 k' hreg
  refine ⟨h1, h2, ?_⟩
  intro k2 hne hreg2
  rw [p_reg hT hF] at hreg2
  rw [p_rid hT hF]
  exact h3 k2 hne hreg2

omit hF in
private theorem inv12 : Inv12 (post cfg s sg k i r) := hI.inv12

private theorem inv13 : Inv13 (post cfg s sg k i r) := by
  intro j r' h
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · simp [rreq, hF.unappr]
  · exact hI.inv13 j r' h

private theorem inv14 : Inv14 (post cfg s sg k i r) := by
  intro j r' h
  rw [post_regs]
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · refine ⟨(hI.inv14 j r hF.hr).1, ?_, fun _ => (hI.inv11 k hF.kreg).1⟩
    simp [rreq, hF.unappr]
  · exact hI.inv14 j r' h

omit hF in
private theorem inv15 : Inv15 (post cfg s sg k i r) := by
  unfold Inv15
  rw [post_regs, post_revoked, post_principals, pmodify_length]
  exact hI.inv15

private theorem inv16 : Inv16 cfg (post cfg s sg k i r) := by
  intro k' j r' hreg h
  have hT := hI.typeOK
  rw [p_reg hT hF] at hreg
  rw [p_rid hT hF, p_acct hT hF, p_role hT hF]
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · obtain ⟨h1, -, -⟩ := hI.inv16 k' j r hreg hF.hr
    refine ⟨h1, ?_, ?_⟩
    · intro hap; simp [rreq, hF.unappr] at hap
    · intro _ hrid
      have hkk : k' = k := by
        by_cases hne : k' = k
        · exact hne
        · exact absurd hrid.symm ((hI.inv11 k hF.kreg).2.2 k' hne hreg)
      subst hkk
      exact ⟨rfl, hF.kacct.symm, hF.krole⟩
  · exact hI.inv16 k' j r' hreg h

private theorem inv5r : Inv5r (post cfg s sg k i r) := by
  intro j r' h hrj
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · show sg ≠ r.acct ∧ k ≠ r.key
    exact ⟨hF.self, k_ne hF⟩
  · exact hI.inv5r j r' h hrj

omit hF in
private theorem lem1 : Lem1 (post cfg s sg k i r) := hI.lem1

private theorem lem2 : Lem2 (post cfg s sg k i r) := by
  unfold Lem2
  rw [post_nl, post_requests, hI.lem2]
  have hc := countIdx_set (fun _ (q : Request A K P) => q.appr) s.requests 0 i
    (rreq cfg s sg k r) (hi hF)
  rw [rget hF] at hc
  have h1 : (rreq cfg s sg k r).appr = false := hF.unappr
  simp only [h1, hF.unappr, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc
  exact hc.symm

private theorem provenance : Provenance (post cfg s sg k i r) := by
  intro j r' h hd
  have hT := hI.typeOK
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨hne, h⟩
  · refine ⟨rghost cfg s sg k r, ?_, ?_, ?_⟩
    · rw [post_ghost]
      apply List.getElem?_set_self
      rw [hT.ghostLen]; exact hi hF
    · have hrd : r.decided = false := by simp [Request.decided, hF.unappr, hF.unrj]
      show unbrokenR cfg s r = true
      rw [hI.ridLive j r hF.hr hrd]; exact hF.live
    · simp [rghost, hF.kreg, hF.krole, hF.kacct]
  · rw [post_ghost, List.getElem?_set_ne (Ne.symm hne)]
    exact hI.provenance j r' h hd

private theorem ridLive : RidLive cfg (post cfg s sg k i r) := by
  intro j r' h hd
  have hT := hI.typeOK
  rcases post_req_cases hF h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · simp [rreq, Request.decided] at hd
  · rw [liveR_eq hT hF, unbrokenR_eq hT hF]
    exact hI.ridLive j r' h hd

end Conj

end InvReject

theorem inv_reject {cfg : Cfg A} {s : State A K P} {p sg : A} {k : K} {i : Nat}
    (hI : Inv cfg s) (hok : rejectErr cfg s p sg k i = .ok) :
    Inv cfg (effect cfg s (.reject p sg k i)) := by
  obtain ⟨r, hr, h2, h3, h4, h5, h6, h7, h8⟩ := InvReject.guard hok
  have hF : InvReject.Facts cfg s sg k i r := ⟨hr, h2, h3, h4, h5, h6, h7, h8⟩
  rw [InvReject.e_eq hr]
  exact
    { typeOK := InvReject.typeOK hI hF
      inv3 := InvReject.inv3 hI hF
      inv4 := InvReject.inv4 hI hF
      inv5 := InvReject.inv5 hI hF
      inv6 := InvReject.inv6 hI hF
      inv7 := InvReject.inv7 hI hF
      inv8 := InvReject.inv8 hI hF
      inv9 := InvReject.inv9 hI hF
      inv11 := InvReject.inv11 hI hF
      inv12 := InvReject.inv12 hI
      inv13 := InvReject.inv13 hI hF
      inv14 := InvReject.inv14 hI hF
      inv15 := InvReject.inv15 hI
      inv16 := InvReject.inv16 hI hF
      inv5r := InvReject.inv5r hI hF
      lem1 := InvReject.lem1 hI
      lem2 := InvReject.lem2 hI hF
      provenance := InvReject.provenance hI hF
      ridLive := InvReject.ridLive hI hF
      approvable := approvable_all cfg _ }

end Approval
