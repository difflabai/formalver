/- LEAN-IND, inductive step for `Approve`: `Inv /\ Approve => Inv'`, for states of any size. -/
import ApprovalLean.Lemmas
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

namespace InvApprove

variable {cfg : Cfg A} {s : State A K P} {p sg : A} {k : K} {i : Nat} {x : Action P}
  {r : Request A K P}

/-- The record of request `i` after `Approve`. -/
private def areq (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (r : Request A K P) :
    Request A K P :=
  { r with appr := true, aidx := s.nl, aacct := sg, akey := k, arid := (prin cfg s k).rid }

/-- The ghost record `Approve` writes at index `i`. -/
private def aghost (cfg : Cfg A) (s : State A K P) (sg : A) (k : K) (r : Request A K P) :
    Ghost :=
  { cont := unbrokenR cfg s r,
    decOk := (prin cfg s k).reg && (prin cfg s k).role == .approver
               && (prin cfg s k).acct == sg }

/-! ### The guard -/

private theorem guard (hok : approveErr cfg s p sg k i x = .ok) :
    ∃ r, s.req i = some r ∧ (prin cfg s k).reg = true ∧ (prin cfg s k).role = .approver ∧
      (prin cfg s k).acct = sg ∧ r.appr = false ∧ r.rj = false ∧ liveR cfg s i r = true ∧
      r.act = x ∧ sg ≠ r.acct := by
  unfold approveErr authErr decideErr at hok
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
    by_cases h8 : r.act = x <;> simp [h8] at hok
    exact ⟨by simpa using h5, by simpa using h6, h7, h8, hok⟩

/-- The guard's facts, for the request record `r` at `i`. -/
private theorem gfacts (hok : approveErr cfg s p sg k i x = .ok) (hr : s.req i = some r) :
    (prin cfg s k).reg = true ∧ (prin cfg s k).role = .approver ∧
      (prin cfg s k).acct = sg ∧ r.appr = false ∧ r.rj = false ∧ liveR cfg s i r = true ∧
      r.act = x ∧ sg ≠ r.acct := by
  obtain ⟨r0, hr0, h⟩ := guard hok
  rw [hr] at hr0
  cases hr0
  exact h

omit [DecidableEq P] in
private theorem live_facts (h : liveR cfg s i r = true) :
    (prin cfg s r.key).reg = true ∧ (prin cfg s r.key).role = .agent ∧
      (prin cfg s r.key).acct = r.acct ∧ (prin cfg s r.key).activeFrom ≤ i := by
  simp only [liveR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ### The effect, field by field -/

section Eff
variable (hr : s.req i = some r)
include hr

omit [DecidableEq P] in
private theorem e_requests : (effect cfg s (.approve p sg k i x)).requests =
    s.requests.set i (areq cfg s sg k r) := by
  simp [effect, hr, areq]

omit [DecidableEq P] in
private theorem e_log : (effect cfg s (.approve p sg k i x)).log = s.log ++ [i] := by
  simp [effect, hr]

omit [DecidableEq P] in
private theorem e_principals : (effect cfg s (.approve p sg k i x)).principals =
    pmodify r.key (fun q => { q with pending := q.pending - 1 }) s.principals := by
  simp [effect, hr, decidePrincipals]

omit [DecidableEq P] in
private theorem e_regs : (effect cfg s (.approve p sg k i x)).regs = s.regs := by
  simp [effect, hr]

omit [DecidableEq P] in
private theorem e_revoked : (effect cfg s (.approve p sg k i x)).revoked = s.revoked := by
  simp [effect, hr]

omit [DecidableEq P] in
private theorem e_ghost : (effect cfg s (.approve p sg k i x)).ghost =
    s.ghost.set i (aghost cfg s sg k r) := by
  simp [effect, hr, decideGhost, aghost]

omit [DecidableEq P] in
private theorem e_nr : (effect cfg s (.approve p sg k i x)).nr = s.nr := by
  simp [State.nr, e_requests hr]

omit [DecidableEq P] in
private theorem e_nl : (effect cfg s (.approve p sg k i x)).nl = s.nl + 1 := by
  simp [State.nl, e_log hr]

private theorem e_req (j : Nat) : (effect cfg s (.approve p sg k i x)).req j =
    if j = i then some (areq cfg s sg k r) else s.req j := by
  have hi := req_lt hr
  simp only [State.req, e_requests hr, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [State.nr] at hi; simp [hi]
  · simp [h, Ne.symm h]

private theorem e_req_self :
    (effect cfg s (.approve p sg k i x)).req i = some (areq cfg s sg k r) := by
  rw [e_req hr]; simp

private theorem e_req_ne {j : Nat} (h : j ≠ i) :
    (effect cfg s (.approve p sg k i x)).req j = s.req j := by
  rw [e_req hr]; simp [h]

private theorem e_req_cases {j : Nat} {r' : Request A K P}
    (h : (effect cfg s (.approve p sg k i x)).req j = some r') :
    (j = i ∧ r' = areq cfg s sg k r) ∨ (j ≠ i ∧ s.req j = some r') := by
  rw [e_req hr] at h
  by_cases hj : j = i
  · rw [ite_eq_left hj] at h; exact Or.inl ⟨hj, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hj] at h; exact Or.inr ⟨hj, h⟩

end Eff

/-! ### Principals after the step: only the agent's pending count drops -/

private theorem prin_eq (hT : TypeOK s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) (k' : K) :
    prin cfg (effect cfg s (.approve p sg k i x)) k' =
      { prin cfg s k' with
        pending := (prin cfg s k').pending - if k' = r.key then 1 else 0 } := by
  rw [prin_def, e_principals hr, plookup_pmodify]
  by_cases h : k' = r.key
  · subst h
    rw [ite_eq_left rfl, prin_of_reg cfg hT hkey]
    simp
  · rw [ite_eq_right h, ite_eq_right h]
    simp [prin_def]

section Fields
variable (hT : TypeOK s) (hr : s.req i = some r) (hkey : (prin cfg s r.key).reg = true)
  (k' : K)
include hT hr hkey

private theorem p_reg : (prin cfg (effect cfg s (.approve p sg k i x)) k').reg =
    (prin cfg s k').reg := by rw [prin_eq hT hr hkey]
private theorem p_acct : (prin cfg (effect cfg s (.approve p sg k i x)) k').acct =
    (prin cfg s k').acct := by rw [prin_eq hT hr hkey]
private theorem p_role : (prin cfg (effect cfg s (.approve p sg k i x)) k').role =
    (prin cfg s k').role := by rw [prin_eq hT hr hkey]
private theorem p_rid : (prin cfg (effect cfg s (.approve p sg k i x)) k').rid =
    (prin cfg s k').rid := by rw [prin_eq hT hr hkey]
private theorem p_from : (prin cfg (effect cfg s (.approve p sg k i x)) k').activeFrom =
    (prin cfg s k').activeFrom := by rw [prin_eq hT hr hkey]
private theorem p_pending : (prin cfg (effect cfg s (.approve p sg k i x)) k').pending =
    (prin cfg s k').pending - if k' = r.key then 1 else 0 := by rw [prin_eq hT hr hkey]

end Fields

private theorem liveR_eq (hT : TypeOK s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) (j : Nat) (q : Request A K P) :
    liveR cfg (effect cfg s (.approve p sg k i x)) j q = liveR cfg s j q := by
  simp only [liveR, p_reg hT hr hkey, p_role hT hr hkey, p_acct hT hr hkey, p_from hT hr hkey]

private theorem unbrokenR_eq (hT : TypeOK s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) (q : Request A K P) :
    unbrokenR cfg (effect cfg s (.approve p sg k i x)) q = unbrokenR cfg s q := by
  simp only [unbrokenR, p_reg hT hr hkey, p_rid hT hr hkey]

/-- The agent key's `Pend` drops by one (index `i` is now decided); every other key's
is unchanged. -/
private theorem pend_eq (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) (k' : K) :
    pend cfg (effect cfg s (.approve p sg k i x)) k' + (if k' = r.key then 1 else 0) =
      pend cfg s k' := by
  obtain ⟨-, -, -, happr, hrj, hlive, -, -⟩ := gfacts hok hr
  obtain ⟨hkreg, -, -, hfrom⟩ := live_facts hlive
  obtain ⟨hi, hri⟩ := req_eq_some hr
  unfold pend
  rw [p_from hI.typeOK hr hkreg, e_requests hr]
  have := countIdx_set
    (fun j q => q.key == k' && !q.decided && decide ((prin cfg s k').activeFrom ≤ j))
    s.requests 0 i (areq cfg s sg k r) hi
  have hda : (areq cfg s sg k r).decided = true := by simp [areq, Request.decided]
  have hdr : r.decided = false := by simp [Request.decided, happr, hrj]
  simp only [hri, hda, hdr, Nat.zero_add] at this
  by_cases h : k' = r.key
  · subst h
    simp [hfrom] at this ⊢
    omega
  · simp [Ne.symm h, h] at this ⊢
    omega

/-! ### Each conjunct -/

private theorem typeOK (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : TypeOK (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  obtain ⟨-, -, -, -, hrj, -, -, -⟩ := gfacts hok hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e_principals hr, pmodify_keys]; exact hT.pkeys
  · intro e he
    rw [e_principals hr] at he
    obtain ⟨e0, he0, -, h | h⟩ := mem_pmodify he
    · rw [h]; exact hT.preg e0 he0
    · rw [h]; exact hT.preg e0 he0
  · intro j r' hr'
    rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
    · exact hT.act i r hr
    · exact hT.act j r' hr'
  · intro j r' hr' ha
    rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
    · simp [areq] at ha
    · exact hT.unappr j r' hr' ha
  · intro j r' hr' hj
    rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
    · exact hT.unrj i r hr hrj
    · exact hT.unrj j r' hr' hj
  · rw [e_revoked hr]; exact hT.revNodup
  · rw [e_ghost hr, e_nr hr, List.length_set]; exact hT.ghostLen

private theorem inv3 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Inv3 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, -, -, happr, -, -, -, -⟩ := gfacts hok hr
  intro j hj
  have hget := List.getElem_of_eq (e_log hr (p := p) (sg := sg) (k := k) (x := x)) hj
  rw [hget]
  rw [List.getElem_append]
  by_cases hjl : j < s.log.length
  · rw [dite_eq_left hjl]
    obtain ⟨r0, hr0, h1, h2⟩ := hI.inv3 j hjl
    have hne : s.log[j] ≠ i := by
      intro he
      rw [he, hr] at hr0
      cases hr0
      simp [happr] at h1
    exact ⟨r0, by rw [e_req_ne hr hne]; exact hr0, h1, h2⟩
  · rw [dite_eq_right hjl]
    have hj' : j < s.nl + 1 := by rw [← e_nl hr (p := p) (sg := sg) (k := k) (x := x)]; exact hj
    have hjeq : j = s.log.length := by simp only [State.nl] at hj'; omega
    refine ⟨areq cfg s sg k r, ?_, rfl, ?_⟩
    · simp only [hjeq, Nat.sub_self, List.getElem_cons_zero]
      exact e_req_self hr
    · simp [areq, State.nl, hjeq]

private theorem inv4 (hI : Inv cfg s) (hr : s.req i = some r) :
    Inv4 (effect cfg s (.approve p sg k i x)) := by
  intro j r' hr' ha
  suffices h : (effect cfg s (.approve p sg k i x)).log[r'.aidx]? = some j from
    List.getElem?_eq_some_iff.1 h
  rw [e_log hr]
  rcases e_req_cases hr hr' with ⟨rfl, rfl⟩ | ⟨-, hr'⟩
  · simp [areq, State.nl]
  · obtain ⟨h1, h2⟩ := hI.inv4 j r' hr' ha
    rw [List.getElem?_append_left h1]
    exact List.getElem?_eq_some_iff.2 ⟨h1, h2⟩

private theorem inv5 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Inv5 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, -, -, -, -, -, -, hne⟩ := gfacts hok hr
  intro j r' hr' ha
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · exact hne
  · exact hI.inv5 j r' hr' ha

private theorem inv6 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Inv6 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, hrole, -, -, -, hlive, -, -⟩ := gfacts hok hr
  obtain ⟨-, hagent, -, -⟩ := live_facts hlive
  intro j r' hr' ha
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · show k ≠ r.key
    intro he
    rw [he, hagent] at hrole
    cases hrole
  · exact hI.inv6 j r' hr' ha

private theorem inv7 (hI : Inv cfg s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) : Inv7 cfg (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  intro k' hreg'
  rw [p_reg hT hr hkey] at hreg'
  rw [p_from hT hr hkey, e_nr hr]
  exact hI.inv7 k' hreg'

private theorem inv8 (hI : Inv cfg s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) : Inv8 cfg (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  intro k' j r' hr' hreg' hk hfrom
  rw [p_reg hT hr hkey] at hreg'
  rw [p_from hT hr hkey] at hfrom
  rw [p_acct hT hr hkey, p_role hT hr hkey, p_rid hT hr hkey]
  rcases e_req_cases hr hr' with ⟨rfl, rfl⟩ | ⟨-, hr'⟩
  · exact hI.inv8 k' _ r hr hreg' hk hfrom
  · exact hI.inv8 k' j r' hr' hreg' hk hfrom

private theorem inv9 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) (hkey : (prin cfg s r.key).reg = true) :
    Inv9 cfg (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  intro k' hreg'
  rw [p_reg hT hr hkey] at hreg'
  have hp := pend_eq hI hok hr k' (p := p) (sg := sg) (k := k) (x := x)
  rw [p_pending hT hr hkey]
  obtain ⟨h1, h2⟩ := hI.inv9 k' hreg'
  by_cases h : k' = r.key
  · subst h
    simp only [ite_true] at hp ⊢
    omega
  · simp only [h, ite_false] at hp ⊢
    omega

private theorem inv11 (hI : Inv cfg s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) : Inv11 cfg (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  intro k' hreg'
  rw [p_reg hT hr hkey] at hreg'
  obtain ⟨h1, h2, h3⟩ := hI.inv11 k' hreg'
  rw [p_rid hT hr hkey, e_regs hr, e_revoked hr]
  refine ⟨h1, h2, fun k2 hk2 hreg2 => ?_⟩
  rw [p_reg hT hr hkey] at hreg2
  rw [p_rid hT hr hkey]
  exact h3 k2 hk2 hreg2

private theorem inv12 (hI : Inv cfg s) (hr : s.req i = some r) :
    Inv12 (effect cfg s (.approve p sg k i x)) := by
  intro g hg
  rw [e_revoked hr] at hg
  rw [e_regs hr]
  exact hI.inv12 g hg

private theorem inv13 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Inv13 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, -, -, -, hrj, -, -, -⟩ := gfacts hok hr
  intro j r' hr'
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · simp [areq, hrj]
  · exact hI.inv13 j r' hr'

private theorem inv14 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Inv14 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨hkreg, -, -, -, hrj, -, -, -⟩ := gfacts hok hr
  intro j r' hr'
  rw [e_regs hr]
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · refine ⟨(hI.inv14 i r hr).1, fun _ => (hI.inv11 k hkreg).1, fun h => ?_⟩
    simp [areq, hrj] at h
  · exact hI.inv14 j r' hr'

private theorem inv15 (hI : Inv cfg s) (hr : s.req i = some r) :
    Inv15 (effect cfg s (.approve p sg k i x)) := by
  have := hI.inv15
  unfold Inv15 at this ⊢
  rw [e_regs hr, e_revoked hr, e_principals hr, pmodify_length]
  exact this

private theorem inv16 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) (hkey : (prin cfg s r.key).reg = true) :
    Inv16 cfg (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  obtain ⟨hkreg, hrole, hacct, -, hrj, -, -, -⟩ := gfacts hok hr
  intro k' j r' hreg' hr'
  rw [p_reg hT hr hkey] at hreg'
  simp only [p_acct hT hr hkey, p_role hT hr hkey, p_rid hT hr hkey]
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · obtain ⟨hA, -, -⟩ := hI.inv16 k' i r hreg' hr
    refine ⟨hA, fun _ ha => ?_, fun hj => by simp [areq, hrj] at hj⟩
    have ha' : (prin cfg s k).rid = (prin cfg s k').rid := ha
    by_cases h : k' = k
    · subst h
      exact ⟨rfl, hacct.symm, hrole⟩
    · exact absurd ha'.symm ((hI.inv11 k hkreg).2.2 k' h hreg')
  · exact hI.inv16 k' j r' hreg' hr'

private theorem inv5r (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Inv5r (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, -, -, -, hrj, -, -, -⟩ := gfacts hok hr
  intro j r' hr' hj
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · simp [areq, hrj] at hj
  · exact hI.inv5r j r' hr' hj

private theorem lem1 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Lem1 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, -, -, happr, -, -, -, -⟩ := gfacts hok hr
  have hnot : i ∉ s.log := by
    intro hm
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.1 hm
    obtain ⟨r0, hr0, h1, -⟩ := hI.inv3 j hj
    rw [hji, hr] at hr0
    cases hr0
    simp [happr] at h1
  unfold Lem1
  rw [e_log hr, List.nodup_append]
  refine ⟨hI.lem1, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  intro he
  subst he
  exact hnot ha

private theorem lem2 (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Lem2 (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨-, -, -, happr, -, -, -, -⟩ := gfacts hok hr
  obtain ⟨hi, hri⟩ := req_eq_some hr
  have h2 := hI.lem2
  unfold Lem2 at h2 ⊢
  rw [e_nl hr, e_requests hr]
  have := countIdx_set (fun _ q => q.appr) s.requests 0 i (areq cfg s sg k r) hi
  have hra : (areq cfg s sg k r).appr = true := rfl
  simp only [hri, hra, happr] at this
  simp at this
  omega

private theorem provenance (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok)
    (hr : s.req i = some r) : Provenance (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  obtain ⟨hkreg, hrole, hacct, happr, hrj, hlive, -, -⟩ := gfacts hok hr
  intro j r' hr' hd
  rcases e_req_cases hr hr' with ⟨rfl, rfl⟩ | ⟨hne, hr'⟩
  · refine ⟨aghost cfg s sg k r, ?_, ?_, ?_⟩
    · rw [e_ghost hr, List.getElem?_set_self]
      rw [hT.ghostLen]; exact req_lt hr
    · show unbrokenR cfg s r = true
      have hd0 : r.decided = false := by simp [Request.decided, happr, hrj]
      rw [hI.ridLive _ r hr hd0]; exact hlive
    · show ((prin cfg s k).reg && (prin cfg s k).role == .approver
               && (prin cfg s k).acct == sg) = true
      simp [hkreg, hrole, hacct]
  · obtain ⟨g, hg, h1, h2⟩ := hI.provenance j r' hr' hd
    refine ⟨g, ?_, h1, h2⟩
    rw [e_ghost hr, List.getElem?_set_ne (Ne.symm hne)]
    exact hg

private theorem ridLive (hI : Inv cfg s) (hr : s.req i = some r)
    (hkey : (prin cfg s r.key).reg = true) : RidLive cfg (effect cfg s (.approve p sg k i x)) := by
  have hT := hI.typeOK
  intro j r' hr' hd
  rw [unbrokenR_eq hT hr hkey, liveR_eq hT hr hkey]
  rcases e_req_cases hr hr' with ⟨-, rfl⟩ | ⟨-, hr'⟩
  · simp [areq, Request.decided] at hd
  · exact hI.ridLive j r' hr' hd

end InvApprove

theorem inv_approve {cfg : Cfg A} {s : State A K P} {p sg : A} {k : K} {i : Nat}
    {x : Action P} (hI : Inv cfg s) (hok : approveErr cfg s p sg k i x = .ok) :
    Inv cfg (effect cfg s (.approve p sg k i x)) := by
  obtain ⟨r, hr, -, -, -, -, -, hlive, -, -⟩ := InvApprove.guard hok
  have hkey := (InvApprove.live_facts hlive).1
  exact
    { typeOK := InvApprove.typeOK hI hok hr
      inv3 := InvApprove.inv3 hI hok hr
      inv4 := InvApprove.inv4 hI hr
      inv5 := InvApprove.inv5 hI hok hr
      inv6 := InvApprove.inv6 hI hok hr
      inv7 := InvApprove.inv7 hI hr hkey
      inv8 := InvApprove.inv8 hI hr hkey
      inv9 := InvApprove.inv9 hI hok hr hkey
      inv11 := InvApprove.inv11 hI hr hkey
      inv12 := InvApprove.inv12 hI hr
      inv13 := InvApprove.inv13 hI hok hr
      inv14 := InvApprove.inv14 hI hok hr
      inv15 := InvApprove.inv15 hI hr
      inv16 := InvApprove.inv16 hI hok hr hkey
      inv5r := InvApprove.inv5r hI hok hr
      lem1 := InvApprove.lem1 hI hok hr
      lem2 := InvApprove.lem2 hI hok hr
      provenance := InvApprove.provenance hI hok hr
      ridLive := InvApprove.ridLive hI hr hkey
      approvable := approvable_all cfg _ }

end Approval
