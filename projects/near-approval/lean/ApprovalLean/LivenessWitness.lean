/-
LEAN-LIVE non-vacuity, the Lean side of `MC_Liveness_Unfair.cfg`:

* `unfair_violates`: an `UnfairSpec` behaviour (agent key 1 of account 1
  requests, approver key 2 of account 2 stays eligible, then nothing
  happens) violates `Live1`. Fairness is what `live1` uses.
* `fair_witness`: a `LiveSpec` behaviour in which the same request is
  pending with an eligible approver at every instant from the request on,
  so `live1`'s premise is satisfiable; the approval then ends it.

Universe as in `Witness.lean`: accounts, keys and payloads are `Nat`.
-/
import ApprovalLean.Liveness

namespace Approval.LiveWitness

open Approval

abbrev N := Nat
def cfg : Cfg N := { owner := 0, maxPending := 1 }

def op0 : Op N N N := .add 0 1 1 .agent
def op1 : Op N N N := .add 0 2 2 .approver
def op2 : Op N N N := .request 1 1 1 (.pay 7)
def op3 : Op N N N := .approve 2 2 2 0 (.pay 7)

def s0 : State N N N := init
def s1 : State N N N := effect cfg s0 op0
def s2 : State N N N := effect cfg s1 op1
def s3 : State N N N := effect cfg s2 op2
def s4 : State N N N := effect cfg s3 op3

/-- Request 0 pending, approver key 2 eligible, then stutter forever. -/
def unfair : Behavior N N N
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | _ => s3

/-- The same, approved at instant 3, then stutter forever. -/
def fair : Behavior N N N
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | _ => s4

theorem pending_s3 : pendingReq cfg s3 0 := ⟨_, rfl, rfl, rfl⟩

theorem eligible_s3 : Eligible cfg 0 s3 := by
  refine ⟨_, rfl, 2, rfl, rfl, ?_⟩
  decide

theorem eligible_s4 : Eligible cfg 0 s4 := by
  refine ⟨_, rfl, 2, rfl, rfl, ?_⟩
  decide

theorem unfair_steps : Steps (Next cfg) unfair := by
  intro n
  match n with
  | 0 => exact .inl ⟨op0, rfl, rfl⟩
  | 1 => exact .inl ⟨op1, rfl, rfl⟩
  | 2 => exact .inl ⟨op2, rfl, rfl⟩
  | _ + 3 => exact .inr rfl

theorem unfair_spec : UnfairSpec cfg (Next cfg) unfair := ⟨rfl, unfair_steps⟩

theorem unfair_late (m : Nat) (h : 3 ≤ m) : unfair m = s3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rfl

/-- `UnfairSpec` does not imply `Live1`: TLA-LIVE-1 FAILS without fairness. -/
theorem unfair_violates : UnfairSpec cfg (Next cfg) unfair ∧ ¬ Live1 cfg unfair := by
  refine ⟨unfair_spec, fun h => ?_⟩
  have he : EvAlways (Eligible cfg 0) unfair :=
    ⟨3, fun m hm => by rw [unfair_late m hm]; exact eligible_s3⟩
  obtain ⟨m, hm, hnp⟩ := h 0 he 3 pending_s3
  rw [unfair_late m hm] at hnp
  exact hnp pending_s3

theorem fair_steps : Steps (Next cfg) fair := by
  intro n
  match n with
  | 0 => exact .inl ⟨op0, rfl, rfl⟩
  | 1 => exact .inl ⟨op1, rfl, rfl⟩
  | 2 => exact .inl ⟨op2, rfl, rfl⟩
  | 3 => exact .inl ⟨op3, rfl, rfl⟩
  | _ + 4 => exact .inr rfl

theorem fair_late (m : Nat) (h : 4 ≤ m) : fair m = s4 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rfl

/-- A successful approval needs an undecided request. -/
theorem approveErr_ok_undecided {cfg : Cfg N} {s : State N N N} {p sg k i x}
    {r : Request N N N} (h : approveErr cfg s p sg k i x = .ok) (hr : s.req i = some r) :
    r.decided = false := by
  unfold approveErr decideErr at h
  rw [hr] at h
  by_cases hA : authErr cfg s p sg k .approver = .ok <;>
    cases ha : r.appr <;> cases hj : r.rj <;> simp_all [Request.decided]

/-- Nothing is approvable in `s4`: its only request is approved. -/
theorem not_enabled_s4 (i : Nat) : ¬ Enabled (ApproveReq cfg i) s4 := by
  rintro ⟨_, ⟨r, hr, sg, k, hok, _⟩, _⟩
  have hd := approveErr_ok_undecided hok hr
  have hlt : i < 1 := req_lt hr
  obtain rfl : i = 0 := by omega
  have hc : (s4.req 0).map Request.decided = some true := rfl
  rw [hr] at hc
  simp only [Option.map_some, Option.some.injEq] at hc
  rw [hc] at hd
  exact Bool.noConfusion hd

theorem fair_wf (i : Nat) : WeakFair (ApproveReq cfg i) fair := by
  rintro ⟨n, hn⟩
  exact absurd (hn (max n 4) (Nat.le_max_left _ _))
    (by rw [fair_late _ (Nat.le_max_right _ _)]; exact not_enabled_s4 i)

/-- `LiveSpec` with `Next` has a behaviour where request 0 is pending and
eligible approvers exist at every instant from 3 on: the premise of
`Live1` is not vacuous, and the request does leave `Pending`. -/
theorem fair_witness :
    LiveSpec cfg (Next cfg) fair ∧ EvAlways (Eligible cfg 0) fair ∧
      pendingReq cfg (fair 3) 0 ∧ ¬ pendingReq cfg (fair 4) 0 := by
  refine ⟨⟨rfl, fair_steps, fair_wf⟩, ⟨3, fun m hm => ?_⟩, pending_s3, ?_⟩
  · rcases Nat.lt_or_ge m 4 with h | h
    · obtain rfl : m = 3 := by omega
      exact eligible_s3
    · rw [fair_late m h]; exact eligible_s4
  · exact approveReq_not_pending (s := s3) ⟨_, rfl, 2, 2, rfl, rfl⟩

end Approval.LiveWitness
