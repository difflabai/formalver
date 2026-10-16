/-
LEAN-TR: properties of every run, of any length, from a reachable state.
-/
import ApprovalLean.Inductive
import ApprovalLean.StepProps

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

private theorem run_nil (cfg : Cfg A) (s : State A K P) : run cfg s [] = s := rfl

private theorem run_cons (cfg : Cfg A) (s : State A K P) (op : Op A K P) (ops : List (Op A K P)) :
    run cfg s (op :: ops) = run cfg (step cfg s op) ops := rfl

omit [DecidableEq A] [DecidableEq K] [DecidableEq P] in
private theorem hist1_refl (s : State A K P) : Hist1 s s :=
  ⟨Nat.le_refl _, fun _ r hr => ⟨r, hr, rfl, rfl, rfl⟩⟩

omit [DecidableEq A] [DecidableEq K] [DecidableEq P] in
private theorem hist1_trans {s1 s2 s3 : State A K P} (h12 : Hist1 s1 s2) (h23 : Hist1 s2 s3) :
    Hist1 s1 s3 := by
  refine ⟨Nat.le_trans h12.1 h23.1, ?_⟩
  intro i r hr
  obtain ⟨r2, hr2, ha2, hk2, hx2⟩ := h12.2 i r hr
  obtain ⟨r3, hr3, ha3, hk3, hx3⟩ := h23.2 i r2 hr2
  exact ⟨r3, hr3, ha3.trans ha2, hk3.trans hk2, hx3.trans hx2⟩

omit [DecidableEq A] [DecidableEq K] [DecidableEq P] in
private theorem hist3_refl (s : State A K P) : Hist3 s s :=
  ⟨Nat.le_refl _, List.take_length⟩

omit [DecidableEq A] [DecidableEq K] [DecidableEq P] in
private theorem hist3_trans {s1 s2 s3 : State A K P} (h12 : Hist3 s1 s2) (h23 : Hist3 s2 s3) :
    Hist3 s1 s3 := by
  refine ⟨Nat.le_trans h12.1 h23.1, ?_⟩
  have h : s3.log.take s1.nl = (s3.log.take s2.nl).take s1.nl := by
    rw [List.take_take, Nat.min_eq_left h12.1]
  rw [h, h23.2, h12.2]

theorem reach_run {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) (ops : List (Op A K P)) :
    Reach cfg (run cfg s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => rw [run_cons]; exact ih (Reach.step op h)

/-- TR-3 / HIST-8 over runs: `[](Void(i) => []Void(i))`. A void request
stays void after any further calls, including a revoke and re-add of the
same key, account and role. -/
theorem tr3_void_terminal {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) {i : Nat}
    (hv : void cfg s i) (ops : List (Op A K P)) : void cfg (run cfg s ops) i := by
  induction ops generalizing s with
  | nil => exact hv
  | cons op ops ih =>
    rw [run_cons]
    exact ih (Reach.step op h) ((stepProps_step (reach_inv h) op).hist8 i hv)

/-- TR-2 / HIST-2 over runs: a decision is final; the decided request
record never changes again. -/
theorem tr2_decision_final {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) {i : Nat}
    {r : Request A K P} (hr : s.req i = some r) (hd : r.decided = true)
    (ops : List (Op A K P)) : (run cfg s ops).req i = some r := by
  induction ops generalizing s with
  | nil => exact hr
  | cons op ops ih =>
    rw [run_cons]
    exact ih (Reach.step op h) ((stepProps_step (reach_inv h) op).hist2 i r hr hd)

/-- HIST-1 over runs: request content is immutable and never removed. -/
theorem hist1_run {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) (ops : List (Op A K P)) :
    Hist1 s (run cfg s ops) := by
  induction ops generalizing s with
  | nil => exact hist1_refl s
  | cons op ops ih =>
    rw [run_cons]
    exact hist1_trans (stepProps_step (reach_inv h) op).hist1 (ih (Reach.step op h))

/-- HIST-3 over runs: the log only grows at the end. -/
theorem hist3_run {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) (ops : List (Op A K P)) :
    Hist3 s (run cfg s ops) := by
  induction ops generalizing s with
  | nil => exact hist3_refl s
  | cons op ops ih =>
    rw [run_cons]
    exact hist3_trans (stepProps_step (reach_inv h) op).hist3 (ih (Reach.step op h))

/-- HIST-10 over runs: the registration counter and the revocation set only
grow. -/
theorem hist10_run {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) (ops : List (Op A K P)) :
    s.regs ≤ (run cfg s ops).regs ∧ ∀ g ∈ s.revoked, g ∈ (run cfg s ops).revoked := by
  induction ops generalizing s with
  | nil => exact ⟨Nat.le_refl _, fun _ hg => hg⟩
  | cons op ops ih =>
    rw [run_cons]
    have h10 := (stepProps_step (reach_inv h) op).hist10
    have ih' := ih (Reach.step op h)
    exact ⟨Nat.le_trans h10.1 ih'.1, fun g hg => ih'.2 g (h10.2.1 g hg)⟩

/-- TR-1: every decided request in every reachable state was made by an
Agent key of its account whose registration was unbroken when it was
decided, and decided by an Approver key of the deciding account, which is
another account (INV-5, INV-5r). -/
theorem tr1_provenance {cfg : Cfg A} {s : State A K P} (h : Reach cfg s) {i : Nat}
    {r : Request A K P} (hr : s.req i = some r) (hd : r.decided = true) :
    (∃ g, s.ghost[i]? = some g ∧ g.cont = true ∧ g.decOk = true) ∧
    (r.appr = true → r.aacct ≠ r.acct ∧ r.akey ≠ r.key) ∧
    (r.rj = true → r.racct ≠ r.acct ∧ r.rkey ≠ r.key) := by
  have hI := reach_inv h
  exact ⟨hI.provenance i r hr hd,
    fun ha => ⟨hI.inv5 i r hr ha, hI.inv6 i r hr ha⟩,
    fun hj => hI.inv5r i r hr hj⟩

end Approval
