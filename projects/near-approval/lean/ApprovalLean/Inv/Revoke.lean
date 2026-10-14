/- LEAN-IND, inductive step for `RevokeKey`: `Inv /\ RevokeKey => Inv'`, for states of any size. -/
import ApprovalLean.Lemmas
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

namespace InvRevoke

variable {cfg : Cfg A} {s : State A K P} {c : A} {k : K}

omit [DecidableEq P] in
private theorem req_eq (i : Nat) : (effect cfg s (.revoke c k)).req i = s.req i := rfl

private theorem reg_ne {k' : K} (h : (prin cfg (effect cfg s (.revoke c k)) k').reg = true) :
    k' ≠ k := by
  intro he
  rw [prin_revoke] at h
  simp [he, noPrincipal] at h

private theorem prin_ne {k' : K} (h : k' ≠ k) :
    prin cfg (effect cfg s (.revoke c k)) k' = prin cfg s k' := by
  rw [prin_revoke]; simp [h]

private theorem pend_ne {k' : K} (h : k' ≠ k) :
    pend cfg (effect cfg s (.revoke c k)) k' = pend cfg s k' := by
  simp only [pend, prin_ne h, revoke_requests]

omit [DecidableEq P] in
private theorem typeOK (hT : TypeOK s) : TypeOK (effect cfg s (.revoke c k)) := by
  refine ⟨?_, ?_, hT.act, hT.unappr, hT.unrj, ?_, hT.ghostLen⟩
  · simp only [revoke_principals]
    exact hT.pkeys.sublist (perase_keys_sublist k _)
  · intro e he
    simp only [revoke_principals] at he
    exact hT.preg e ((perase_sublist k _).subset he)
  · simp only [revoke_revoked]
    exact setInsert_nodup hT.revNodup

private theorem inv7 (hI : Inv cfg s) : Inv7 cfg (effect cfg s (.revoke c k)) := by
  intro k' hreg
  have h := reg_ne hreg
  rw [prin_ne h] at hreg ⊢
  exact hI.inv7 k' hreg

private theorem inv8 (hI : Inv cfg s) : Inv8 cfg (effect cfg s (.revoke c k)) := by
  intro k' i rq hrq hreg hkey hfrom
  have h := reg_ne hreg
  rw [req_eq] at hrq
  rw [prin_ne h] at hreg hfrom ⊢
  exact hI.inv8 k' i rq hrq hreg hkey hfrom

private theorem inv9 (hI : Inv cfg s) : Inv9 cfg (effect cfg s (.revoke c k)) := by
  intro k' hreg
  have h := reg_ne hreg
  rw [pend_ne h]
  rw [prin_ne h] at hreg ⊢
  exact hI.inv9 k' hreg

private theorem inv11 (hI : Inv cfg s) (hk : (prin cfg s k).reg = true) :
    Inv11 cfg (effect cfg s (.revoke c k)) := by
  intro k' hreg
  have h := reg_ne hreg
  rw [prin_ne h] at hreg ⊢
  obtain ⟨h1, h2, h3⟩ := hI.inv11 k' hreg
  have hne : (prin cfg s k').rid ≠ (prin cfg s k).rid := (hI.inv11 k hk).2.2 k' h hreg
  simp only [revoke_regs, revoke_revoked, mem_setInsert]
  refine ⟨h1, ?_, ?_⟩
  · rintro (he | he)
    · exact hne he
    · exact h2 he
  · intro k2 hk2 hreg2
    have h' := reg_ne hreg2
    rw [prin_ne h'] at hreg2 ⊢
    exact h3 k2 hk2 hreg2

private theorem inv12 (hI : Inv cfg s) (hk : (prin cfg s k).reg = true) :
    Inv12 (effect cfg s (.revoke c k)) := by
  intro g hg
  simp only [revoke_revoked, revoke_regs, mem_setInsert] at hg ⊢
  rcases hg with rfl | hg
  · exact (hI.inv11 k hk).1
  · exact hI.inv12 g hg

private theorem inv15 (hI : Inv cfg s) (hk : (prin cfg s k).reg = true) :
    Inv15 (effect cfg s (.revoke c k)) := by
  have h15 := hI.inv15
  have hnm : (prin cfg s k).rid ∉ s.revoked := (hI.inv11 k hk).2.1
  have hsome : (plookup k s.principals).isSome := by
    rw [prin_of_reg cfg hI.typeOK hk]; rfl
  have hlen := perase_length_of_mem hI.typeOK.pkeys hsome
  unfold Inv15 at h15 ⊢
  simp only [revoke_regs, revoke_revoked, revoke_principals, setInsert_length_of_not_mem hnm]
  omega

private theorem inv16 (hI : Inv cfg s) : Inv16 cfg (effect cfg s (.revoke c k)) := by
  intro k' i rq hreg hrq
  have h := reg_ne hreg
  rw [req_eq] at hrq
  rw [prin_ne h] at hreg ⊢
  exact hI.inv16 k' i rq hreg hrq

private theorem ridLive (hI : Inv cfg s) : RidLive cfg (effect cfg s (.revoke c k)) := by
  intro i rq hrq hd
  rw [req_eq] at hrq
  unfold unbrokenR liveR
  by_cases h : rq.key = k
  · rw [prin_revoke]
    simp [h, noPrincipal]
  · rw [prin_ne h]
    exact hI.ridLive i rq hrq hd

end InvRevoke

theorem inv_revoke {cfg : Cfg A} {s : State A K P} {c : A} {k : K}
    (hI : Inv cfg s) (hok : revokeErr cfg s c k = .ok) : Inv cfg (effect cfg s (.revoke c k)) := by
  have hreg : (prin cfg s k).reg = true := by
    unfold revokeErr at hok
    split at hok
    · cases hok
    · split at hok
      · cases hok
      · simpa using (by assumption : ¬(!(prin cfg s k).reg) = true)
  exact
    { typeOK := InvRevoke.typeOK hI.typeOK
      inv3 := hI.inv3
      inv4 := hI.inv4
      inv5 := hI.inv5
      inv6 := hI.inv6
      inv7 := InvRevoke.inv7 hI
      inv8 := InvRevoke.inv8 hI
      inv9 := InvRevoke.inv9 hI
      inv11 := InvRevoke.inv11 hI hreg
      inv12 := InvRevoke.inv12 hI hreg
      inv13 := hI.inv13
      inv14 := hI.inv14
      inv15 := InvRevoke.inv15 hI hreg
      inv16 := InvRevoke.inv16 hI
      inv5r := hI.inv5r
      lem1 := hI.lem1
      lem2 := hI.lem2
      provenance := hI.provenance
      ridLive := InvRevoke.ridLive hI
      approvable := approvable_all cfg _ }

end Approval
