/- LEAN-IND, inductive step for `RequestAction`: `Inv /\ RequestAction => Inv'`, for states of any size. -/
import ApprovalLean.Lemmas
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

namespace InvRequest

variable {cfg : Cfg A} {s : State A K P} {p sg : A} {k : K} {x : Action P}

/-- The request record `RequestAction` appends. -/
private def nreq (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (x : Action P) :
    Request A K P :=
  { acct := sg, key := k, rid := (prin cfg s k).rid, act := x,
    appr := false, aidx := 0, aacct := sg, akey := k, arid := 0,
    rj := false, racct := sg, rkey := k, rrid := 0 }

/-! ### The effect, field by field -/

omit [DecidableEq P] in
private theorem e_principals : (effect cfg s (.request p sg k x)).principals =
    pmodify k (fun q => { q with pending := q.pending + 1 }) s.principals := rfl
omit [DecidableEq P] in
private theorem e_requests : (effect cfg s (.request p sg k x)).requests =
    s.requests ++ [nreq cfg s sg k x] := rfl
omit [DecidableEq P] in
private theorem e_log : (effect cfg s (.request p sg k x)).log = s.log := rfl
omit [DecidableEq P] in
private theorem e_regs : (effect cfg s (.request p sg k x)).regs = s.regs := rfl
omit [DecidableEq P] in
private theorem e_revoked : (effect cfg s (.request p sg k x)).revoked = s.revoked := rfl
omit [DecidableEq P] in
private theorem e_ghost : (effect cfg s (.request p sg k x)).ghost =
    s.ghost ++ [{ cont := false, decOk := false }] := rfl

omit [DecidableEq P] in
private theorem e_nr : (effect cfg s (.request p sg k x)).nr = s.nr + 1 := by
  simp [State.nr, e_requests]

omit [DecidableEq P] in
private theorem e_nl : (effect cfg s (.request p sg k x)).nl = s.nl := rfl

/-- The requests after the step: the old ones, then the new one at index `nr`. -/
private theorem e_req (i : Nat) : (effect cfg s (.request p sg k x)).req i =
    if i < s.nr then s.req i else if i = s.nr then some (nreq cfg s sg k x) else none := by
  simp only [State.req, e_requests]
  rw [req_append]
  by_cases h : i < s.nr
  · simp [h, State.req]
  · simp only [h, ↓reduceIte]
    by_cases h2 : i = s.nr
    · subst h2; simp
    · have : i - s.nr ≠ 0 := by omega
      simp only [h2, ↓reduceIte]
      rw [List.getElem?_eq_none]
      simp; omega

private theorem e_req_old {i : Nat} {r : Request A K P} (h : s.req i = some r) :
    (effect cfg s (.request p sg k x)).req i = some r := by
  rw [e_req, ite_eq_left (req_lt h), h]

private theorem e_req_cases {i : Nat} {r : Request A K P}
    (h : (effect cfg s (.request p sg k x)).req i = some r) :
    s.req i = some r ∨ (i = s.nr ∧ r = nreq cfg s sg k x) := by
  rw [e_req] at h
  by_cases h1 : i < s.nr
  · rw [ite_eq_left h1] at h; exact Or.inl h
  · rw [ite_eq_right h1] at h
    by_cases h2 : i = s.nr
    · rw [ite_eq_left h2] at h
      exact Or.inr ⟨h2, (Option.some.inj h).symm⟩
    · rw [ite_eq_right h2] at h; cases h

/-! ### Principals after the step -/

private theorem prin_eq (hT : TypeOK s) (hreg : (prin cfg s k).reg = true) (k' : K) :
    prin cfg (effect cfg s (.request p sg k x)) k' =
      { prin cfg s k' with
        pending := (prin cfg s k').pending + if k' = k then 1 else 0 } := by
  rw [prin_def, e_principals, plookup_pmodify]
  by_cases h : k' = k
  · subst h
    rw [ite_eq_left rfl, prin_of_reg cfg hT hreg]
    simp
  · rw [ite_eq_right h, ite_eq_right h]
    simp [prin_def]

section Fields
variable (hT : TypeOK s) (hreg : (prin cfg s k).reg = true) (k' : K)
include hT hreg

private theorem p_reg : (prin cfg (effect cfg s (.request p sg k x)) k').reg =
    (prin cfg s k').reg := by rw [prin_eq hT hreg]
private theorem p_acct : (prin cfg (effect cfg s (.request p sg k x)) k').acct =
    (prin cfg s k').acct := by rw [prin_eq hT hreg]
private theorem p_role : (prin cfg (effect cfg s (.request p sg k x)) k').role =
    (prin cfg s k').role := by rw [prin_eq hT hreg]
private theorem p_rid : (prin cfg (effect cfg s (.request p sg k x)) k').rid =
    (prin cfg s k').rid := by rw [prin_eq hT hreg]
private theorem p_from : (prin cfg (effect cfg s (.request p sg k x)) k').activeFrom =
    (prin cfg s k').activeFrom := by rw [prin_eq hT hreg]
private theorem p_pending : (prin cfg (effect cfg s (.request p sg k x)) k').pending =
    (prin cfg s k').pending + if k' = k then 1 else 0 := by rw [prin_eq hT hreg]

end Fields

private theorem liveR_eq (hT : TypeOK s) (hreg : (prin cfg s k).reg = true) (i : Nat)
    (r : Request A K P) :
    liveR cfg (effect cfg s (.request p sg k x)) i r = liveR cfg s i r := by
  simp only [liveR, p_reg hT hreg, p_role hT hreg, p_acct hT hreg, p_from hT hreg]

private theorem unbrokenR_eq (hT : TypeOK s) (hreg : (prin cfg s k).reg = true)
    (r : Request A K P) :
    unbrokenR cfg (effect cfg s (.request p sg k x)) r = unbrokenR cfg s r := by
  simp only [unbrokenR, p_reg hT hreg, p_rid hT hreg]

/-! ### The guard -/

private theorem guard (hok : requestErr cfg s p sg k x = .ok) :
    (prin cfg s k).reg = true ∧ (prin cfg s k).role = .agent ∧ (prin cfg s k).acct = sg ∧
      (∃ y, x = .pay y) ∧ (prin cfg s k).pending < cfg.maxPending := by
  unfold requestErr authErr at hok
  by_cases h1 : p = sg <;> simp [h1] at hok
  by_cases h2 : (prin cfg s k).reg = true <;> simp [h2] at hok
  by_cases h3 : (prin cfg s k).role = .agent <;> simp [h3] at hok
  by_cases h4 : (prin cfg s k).acct = sg <;> simp [h4] at hok
  cases x with
  | pay y =>
    simp at hok
    exact ⟨h2, h3, h4, ⟨y, rfl⟩, by omega⟩
  | empty => simp at hok
  | tooLong => simp at hok

/-! ### Each conjunct -/

private theorem pend_eq (hI : Inv cfg s) (hreg : (prin cfg s k).reg = true) (k' : K) :
    pend cfg (effect cfg s (.request p sg k x)) k' = pend cfg s k' + if k' = k then 1 else 0 := by
  unfold pend
  rw [p_from hI.typeOK hreg, e_requests, countIdx_append]
  congr 1
  by_cases h : k' = k
  · subst h
    have := hI.inv7 k' hreg
    simp [nreq, Request.decided, State.nr] at this ⊢
    omega
  · simp [nreq, h, Ne.symm h]

private theorem typeOK (hI : Inv cfg s) (hok : requestErr cfg s p sg k x = .ok) :
    TypeOK (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  obtain ⟨-, -, -, ⟨y, hy⟩, -⟩ := guard hok
  refine ⟨?_, ?_, ?_, ?_, ?_, hT.revNodup, ?_⟩
  · rw [e_principals, pmodify_keys]; exact hT.pkeys
  · intro e he
    rw [e_principals] at he
    obtain ⟨e0, he0, -, h | h⟩ := mem_pmodify he
    · rw [h]; exact hT.preg e0 he0
    · rw [h]; exact hT.preg e0 he0
  · intro i r hr
    rcases e_req_cases hr with hr | ⟨-, rfl⟩
    · exact hT.act i r hr
    · exact ⟨y, hy⟩
  · intro i r hr ha
    rcases e_req_cases hr with hr | ⟨-, rfl⟩
    · exact hT.unappr i r hr ha
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i r hr hj
    rcases e_req_cases hr with hr | ⟨-, rfl⟩
    · exact hT.unrj i r hr hj
    · exact ⟨rfl, rfl, rfl⟩
  · rw [e_ghost, e_nr, List.length_append, hT.ghostLen]; rfl

private theorem inv3 (hI : Inv cfg s) : Inv3 (effect cfg s (.request p sg k x)) := by
  intro j hj
  obtain ⟨r, hr, h1, h2⟩ := hI.inv3 j hj
  exact ⟨r, e_req_old hr, h1, h2⟩

private theorem inv4 (hI : Inv cfg s) : Inv4 (effect cfg s (.request p sg k x)) := by
  intro i r hr ha
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv4 i r hr ha
  · simp [nreq] at ha

private theorem inv5 (hI : Inv cfg s) : Inv5 (effect cfg s (.request p sg k x)) := by
  intro i r hr ha
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv5 i r hr ha
  · simp [nreq] at ha

private theorem inv6 (hI : Inv cfg s) : Inv6 (effect cfg s (.request p sg k x)) := by
  intro i r hr ha
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv6 i r hr ha
  · simp [nreq] at ha

private theorem inv7 (hI : Inv cfg s) (hreg : (prin cfg s k).reg = true) :
    Inv7 cfg (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  intro k' hreg'
  rw [p_reg hT hreg] at hreg'
  rw [p_from hT hreg, e_nr]
  have := hI.inv7 k' hreg'
  omega

private theorem inv8 (hI : Inv cfg s) (hok : requestErr cfg s p sg k x = .ok) :
    Inv8 cfg (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  obtain ⟨hreg, hrole, hacct, -, -⟩ := guard hok
  intro k' i r hr hreg' hkey hfrom
  rw [p_reg hT hreg] at hreg'
  rw [p_from hT hreg] at hfrom
  rw [p_acct hT hreg, p_role hT hreg, p_rid hT hreg]
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv8 k' i r hr hreg' hkey hfrom
  · have : k = k' := hkey
    subst this
    exact ⟨hacct.symm, hrole, rfl⟩

private theorem inv9 (hI : Inv cfg s) (hok : requestErr cfg s p sg k x = .ok) :
    Inv9 cfg (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  obtain ⟨hreg, -, -, -, hcap⟩ := guard hok
  intro k' hreg'
  rw [p_reg hT hreg] at hreg'
  rw [p_pending hT hreg, pend_eq hI hreg]
  obtain ⟨h1, h2⟩ := hI.inv9 k' hreg'
  by_cases h : k' = k
  · subst h; simp only [↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

private theorem inv11 (hI : Inv cfg s) (hreg : (prin cfg s k).reg = true) :
    Inv11 cfg (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  intro k' hreg'
  rw [p_reg hT hreg] at hreg'
  obtain ⟨h1, h2, h3⟩ := hI.inv11 k' hreg'
  simp only [p_rid hT hreg, p_reg hT hreg, e_regs, e_revoked]
  exact ⟨h1, h2, h3⟩

private theorem inv12 (hI : Inv cfg s) : Inv12 (effect cfg s (.request p sg k x)) := by
  intro g hg
  exact hI.inv12 g hg

private theorem inv13 (hI : Inv cfg s) : Inv13 (effect cfg s (.request p sg k x)) := by
  intro i r hr
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv13 i r hr
  · simp [nreq]

private theorem inv14 (hI : Inv cfg s) (hreg : (prin cfg s k).reg = true) :
    Inv14 (effect cfg s (.request p sg k x)) := by
  intro i r hr
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv14 i r hr
  · refine ⟨(hI.inv11 k hreg).1, ?_, ?_⟩ <;> simp [nreq]

private theorem inv15 (hI : Inv cfg s) : Inv15 (effect cfg s (.request p sg k x)) := by
  have := hI.inv15
  unfold Inv15 at this ⊢
  rw [e_regs, e_revoked, e_principals, pmodify_length]
  exact this

private theorem inv16 (hI : Inv cfg s) (hok : requestErr cfg s p sg k x = .ok) :
    Inv16 cfg (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  obtain ⟨hreg, hrole, hacct, -, -⟩ := guard hok
  intro k' i r hreg' hr
  rw [p_reg hT hreg] at hreg'
  simp only [p_acct hT hreg, p_role hT hreg, p_rid hT hreg]
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv16 k' i r hreg' hr
  · refine ⟨fun he => ?_, fun ha => by simp [nreq] at ha, fun hj => by simp [nreq] at hj⟩
    by_cases h : k' = k
    · subst h; exact ⟨rfl, hacct.symm, hrole⟩
    · exact absurd he.symm ((hI.inv11 k hreg).2.2 k' h hreg')

private theorem inv5r (hI : Inv cfg s) : Inv5r (effect cfg s (.request p sg k x)) := by
  intro i r hr hj
  rcases e_req_cases hr with hr | ⟨-, rfl⟩
  · exact hI.inv5r i r hr hj
  · simp [nreq] at hj

private theorem lem2 (hI : Inv cfg s) : Lem2 (effect cfg s (.request p sg k x)) := by
  have := hI.lem2
  unfold Lem2 at this ⊢
  rw [e_nl, e_requests, countIdx_append]
  simpa [nreq] using this

private theorem provenance (hI : Inv cfg s) : Provenance (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  intro i r hr hd
  rcases e_req_cases hr with hr' | ⟨-, rfl⟩
  · obtain ⟨g, hg, h1, h2⟩ := hI.provenance i r hr' hd
    refine ⟨g, ?_, h1, h2⟩
    rw [e_ghost, List.getElem?_append_left (by rw [hT.ghostLen]; exact req_lt hr')]
    exact hg
  · simp [nreq, Request.decided] at hd

private theorem ridLive (hI : Inv cfg s) (hok : requestErr cfg s p sg k x = .ok) :
    RidLive cfg (effect cfg s (.request p sg k x)) := by
  have hT := hI.typeOK
  obtain ⟨hreg, hrole, hacct, -, -⟩ := guard hok
  intro i r hr hd
  rw [unbrokenR_eq hT hreg, liveR_eq hT hreg]
  rcases e_req_cases hr with hr' | ⟨rfl, rfl⟩
  · exact hI.ridLive i r hr' hd
  · have := hI.inv7 k hreg
    simp [unbrokenR, liveR, nreq, hreg, hrole, hacct, this]

end InvRequest

theorem inv_request {cfg : Cfg A} {s : State A K P} {p sg : A} {k : K} {x : Action P}
    (hI : Inv cfg s) (hok : requestErr cfg s p sg k x = .ok) :
    Inv cfg (effect cfg s (.request p sg k x)) := by
  have hreg := (InvRequest.guard hok).1
  exact
    { typeOK := InvRequest.typeOK hI hok
      inv3 := InvRequest.inv3 hI
      inv4 := InvRequest.inv4 hI
      inv5 := InvRequest.inv5 hI
      inv6 := InvRequest.inv6 hI
      inv7 := InvRequest.inv7 hI hreg
      inv8 := InvRequest.inv8 hI hok
      inv9 := InvRequest.inv9 hI hok
      inv11 := InvRequest.inv11 hI hreg
      inv12 := InvRequest.inv12 hI
      inv13 := InvRequest.inv13 hI
      inv14 := InvRequest.inv14 hI hreg
      inv15 := InvRequest.inv15 hI
      inv16 := InvRequest.inv16 hI hok
      inv5r := InvRequest.inv5r hI
      lem1 := hI.lem1
      lem2 := InvRequest.lem2 hI
      provenance := InvRequest.provenance hI
      ridLive := InvRequest.ridLive hI hok
      approvable := approvable_all cfg _ }

end Approval
