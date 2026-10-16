/- LEAN-IND, inductive step for `AddPrincipal`: `Inv /\ AddPrincipal => Inv'`, for states of any size. -/
import ApprovalLean.Lemmas
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

namespace InvAdd

variable {cfg : Cfg A} {s : State A K P} {c : A} {k : K} {a : A} {ro : Role}

omit [DecidableEq P] in
private theorem req_eq (i : Nat) : (effect cfg s (.add c k a ro)).req i = s.req i := rfl

private theorem pend_ne {k' : K} (h : k' ≠ k) :
    pend cfg (effect cfg s (.add c k a ro)) k' = pend cfg s k' := by
  simp only [pend, prin_add, h, ↓reduceIte, add_requests]

private theorem pend_self : pend cfg (effect cfg s (.add c k a ro)) k = 0 := by
  unfold pend
  apply countIdx_eq_zero
  intro j hj
  simp only [add_requests] at hj
  simp [prin_add, State.nr]
  omega

omit [DecidableEq P] in
private theorem typeOK (hT : TypeOK s) :
    TypeOK (effect cfg s (.add c k a ro)) := by
  refine ⟨?_, ?_, hT.act, hT.unappr, hT.unrj, hT.revNodup, hT.ghostLen⟩
  · simp only [add_principals, List.map_cons, List.nodup_cons]
    exact ⟨not_mem_perase_keys k _, hT.pkeys.sublist (perase_keys_sublist k _)⟩
  · intro e he
    simp only [add_principals, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact hT.preg e ((perase_sublist k _).subset he)

private theorem inv7 (hI : Inv cfg s) : Inv7 cfg (effect cfg s (.add c k a ro)) := by
  intro k' hreg
  rw [prin_add] at hreg ⊢
  by_cases h : k' = k
  · simp [h]; exact Nat.le_refl _
  · simp only [h, ↓reduceIte] at hreg ⊢
    exact hI.inv7 k' hreg

private theorem inv8 (hI : Inv cfg s) : Inv8 cfg (effect cfg s (.add c k a ro)) := by
  intro k' i rq hrq hreg hkey hfrom
  rw [req_eq] at hrq
  rw [prin_add] at hreg hfrom ⊢
  by_cases h : k' = k
  · simp only [h, ↓reduceIte] at hfrom
    have := req_lt hrq
    omega
  · simp only [h, ↓reduceIte] at hreg hfrom ⊢
    exact hI.inv8 k' i rq hrq hreg hkey hfrom

private theorem inv9 (hI : Inv cfg s) : Inv9 cfg (effect cfg s (.add c k a ro)) := by
  intro k' hreg
  by_cases h : k' = k
  · subst h
    rw [pend_self, prin_add]
    simp
  · rw [pend_ne h]
    rw [prin_add] at hreg ⊢
    simp only [h, ↓reduceIte] at hreg ⊢
    exact hI.inv9 k' hreg

private theorem inv11 (hI : Inv cfg s) : Inv11 cfg (effect cfg s (.add c k a ro)) := by
  intro k' hreg
  simp only [add_regs, add_revoked]
  by_cases h : k' = k
  · subst h
    simp only [prin_add, ↓reduceIte]
    refine ⟨Nat.lt_succ_self _, fun hm => Nat.lt_irrefl _ (hI.inv12 _ hm), ?_⟩
    intro k2 hk2 hreg2
    simp only [hk2, ↓reduceIte] at hreg2 ⊢
    have := (hI.inv11 k2 hreg2).1
    omega
  · rw [prin_add] at hreg
    simp only [h, ↓reduceIte] at hreg
    obtain ⟨h1, h2, h3⟩ := hI.inv11 k' hreg
    simp only [prin_add, h, ↓reduceIte]
    refine ⟨Nat.lt_succ_of_lt h1, h2, ?_⟩
    intro k2 hk2 hreg2
    by_cases h' : k2 = k
    · simp only [h', ↓reduceIte]
      omega
    · simp only [h', ↓reduceIte] at hreg2 ⊢
      exact h3 k2 hk2 hreg2

private theorem inv12 (hI : Inv cfg s) : Inv12 (effect cfg s (.add c k a ro)) := by
  intro g hg
  simp only [add_revoked, add_regs] at hg ⊢
  exact Nat.lt_succ_of_lt (hI.inv12 g hg)

private theorem inv14 (hI : Inv cfg s) : Inv14 (effect cfg s (.add c k a ro)) := by
  intro i rq hrq
  rw [req_eq] at hrq
  obtain ⟨h1, h2, h3⟩ := hI.inv14 i rq hrq
  simp only [add_regs]
  exact ⟨Nat.lt_succ_of_lt h1, fun h => Nat.lt_succ_of_lt (h2 h),
    fun h => Nat.lt_succ_of_lt (h3 h)⟩

private theorem inv15 (hI : Inv cfg s) (hk : plookup k s.principals = none) :
    Inv15 (effect cfg s (.add c k a ro)) := by
  have := hI.inv15
  unfold Inv15 at this ⊢
  simp only [add_regs, add_revoked, add_principals, List.length_cons, perase_of_not_mem hk]
  omega

private theorem inv16 (hI : Inv cfg s) : Inv16 cfg (effect cfg s (.add c k a ro)) := by
  intro k' i rq hreg hrq
  rw [req_eq] at hrq
  rw [prin_add] at hreg ⊢
  by_cases h : k' = k
  · simp only [h, ↓reduceIte]
    obtain ⟨h1, h2, h3⟩ := hI.inv14 i rq hrq
    refine ⟨fun he => ?_, fun ha he => ?_, fun hr he => ?_⟩
    · omega
    · have := h2 ha; omega
    · have := h3 hr; omega
  · simp only [h, ↓reduceIte] at hreg ⊢
    exact hI.inv16 k' i rq hreg hrq

private theorem ridLive (hI : Inv cfg s) : RidLive cfg (effect cfg s (.add c k a ro)) := by
  intro i rq hrq hd
  rw [req_eq] at hrq
  unfold unbrokenR liveR
  rw [prin_add]
  by_cases h : rq.key = k
  · simp only [h, ↓reduceIte]
    have h1 := (hI.inv14 i rq hrq).1
    have h2 := req_lt hrq
    have e1 : (s.regs == rq.rid) = false := by simp; omega
    have e2 : decide (s.nr ≤ i) = false := by simp; omega
    simp [e1, e2]
  · simp only [h, ↓reduceIte]
    exact hI.ridLive i rq hrq hd

end InvAdd

theorem inv_add {cfg : Cfg A} {s : State A K P} {c : A} {k : K} {a : A} {r : Role}
    (hI : Inv cfg s) (hok : addErr cfg s c k = .ok) : Inv cfg (effect cfg s (.add c k a r)) := by
  have hreg : (prin cfg s k).reg = false := by
    unfold addErr at hok
    split at hok
    · cases hok
    · split at hok
      · cases hok
      · simpa using (by assumption : ¬(prin cfg s k).reg = true)
  have hk : plookup k s.principals = none := (prin_of_not_reg cfg hI.typeOK hreg).2
  exact
    { typeOK := InvAdd.typeOK hI.typeOK
      inv3 := hI.inv3
      inv4 := hI.inv4
      inv5 := hI.inv5
      inv6 := hI.inv6
      inv7 := InvAdd.inv7 hI
      inv8 := InvAdd.inv8 hI
      inv9 := InvAdd.inv9 hI
      inv11 := InvAdd.inv11 hI
      inv12 := InvAdd.inv12 hI
      inv13 := hI.inv13
      inv14 := InvAdd.inv14 hI
      inv15 := InvAdd.inv15 hI hk
      inv16 := InvAdd.inv16 hI
      inv5r := hI.inv5r
      lem1 := hI.lem1
      lem2 := hI.lem2
      provenance := hI.provenance
      ridLive := InvAdd.ridLive hI
      approvable := approvable_all cfg _ }

end Approval
