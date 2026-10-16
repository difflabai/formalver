/- LEAN-IND, base case: `Init => Inv`. -/
import ApprovalLean.Lemmas
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

theorem inv_init (cfg : Cfg A) : Inv cfg (init : State A K P) := by
  have hreq : ∀ i, (init : State A K P).req i = none := fun i => by simp [State.req, init]
  have hreg : ∀ k, (prin cfg (init : State A K P) k).reg = false := fun _ => rfl
  refine
    { typeOK := ?_, inv3 := ?_, inv4 := ?_, inv5 := ?_, inv6 := ?_, inv7 := ?_, inv8 := ?_,
      inv9 := ?_, inv11 := ?_, inv12 := ?_, inv13 := ?_, inv14 := ?_, inv15 := ?_,
      inv16 := ?_, inv5r := ?_, lem1 := ?_, lem2 := ?_, provenance := ?_, ridLive := ?_,
      approvable := approvable_all cfg _ }
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [init]
    · simp [init]
    · intro i r h; simp [hreq] at h
    · intro i r h; simp [hreq] at h
    · intro i r h; simp [hreq] at h
    · simp [init]
    · simp [init, State.nr]
  · intro j hj; simp [State.nl, init] at hj
  · intro i r h; simp [hreq] at h
  · intro i r h; simp [hreq] at h
  · intro i r h; simp [hreq] at h
  · intro k h; simp [hreg] at h
  · intro k i r h; simp [hreq] at h
  · intro k h; simp [hreg] at h
  · intro k h; simp [hreg] at h
  · intro g h; simp [init] at h
  · intro i r h; simp [hreq] at h
  · intro i r h; simp [hreq] at h
  · simp [Inv15, init]
  · intro k i r h; simp [hreg] at h
  · intro i r h; simp [hreq] at h
  · simp [Lem1, init]
  · simp [Lem2, init, State.nl, countIdx]
  · intro i r h; simp [hreq] at h
  · intro i r h; simp [hreq] at h

end Approval
