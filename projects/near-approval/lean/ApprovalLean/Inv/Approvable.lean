/-
TLA-LIVE-2 (`Approvable`) holds in every state: it follows from the
definitions of the error operators alone.
-/
import ApprovalLean.Lemmas

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

theorem approvable_all (cfg : Cfg A) (s : State A K P) : Approvable cfg s := by
  intro i r k hr hd hl ⟨hreg, hrole, hacct⟩
  have hdec : decideErr cfg s i = .ok := by
    simp only [Request.decided, Bool.or_eq_false_iff] at hd
    simp [decideErr, hr, hd.1, hd.2, hl]
  have hauth : authErr cfg s (prin cfg s k).acct (prin cfg s k).acct k .approver = .ok := by
    simp [authErr, hreg, hrole]
  constructor
  · simp [approveErr, hauth, hdec, hr, hacct]
  · simp [rejectErr, hauth, hdec, hr, hacct]

end Approval
