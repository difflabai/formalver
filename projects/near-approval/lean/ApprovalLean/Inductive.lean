/-
LEAN-IND: `Inv` is an inductive invariant of the machine, for states of
every size and every value of `MaxPending`, so it holds in every reachable
state. This is TLA-IND (Apalache) without its bound of 3 on the request
array and revocations.
-/
import ApprovalLean.Inv.Init
import ApprovalLean.Inv.Add
import ApprovalLean.Inv.Revoke
import ApprovalLean.Inv.Request
import ApprovalLean.Inv.Approve
import ApprovalLean.Inv.Reject

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-- `Inv /\ Next => Inv'`. -/
theorem inv_next {cfg : Cfg A} {s s' : State A K P} (hI : Inv cfg s) (hN : Next cfg s s') :
    Inv cfg s' := by
  obtain ⟨op, hok, rfl⟩ := hN
  cases op with
  | add c k a r => exact inv_add hI hok
  | revoke c k => exact inv_revoke hI hok
  | request p sg k x => exact inv_request hI hok
  | approve p sg k i x => exact inv_approve hI hok
  | reject p sg k i => exact inv_reject hI hok

/-- Every call, successful or not, preserves `Inv`. -/
theorem inv_step {cfg : Cfg A} {s : State A K P} (hI : Inv cfg s) (op : Op A K P) :
    Inv cfg (step cfg s op) := by
  unfold step
  split
  · exact inv_next hI ⟨op, by assumption, rfl⟩
  · exact hI

/-- `Inv` holds in every reachable state. -/
theorem reach_inv {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) : Inv cfg s := by
  induction h with
  | init => exact inv_init cfg
  | step op _ ih => exact inv_step ih op

end Approval
