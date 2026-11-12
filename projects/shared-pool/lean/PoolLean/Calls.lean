/-
Per-call properties beyond StepProps, at every size and from every state:
DEP-1, OBS-1 and PAUSE-1.
-/
import PoolLean.StepProps

namespace Pool

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- `observe` has no no-op path: `Ok` means every guard passed. -/
theorem observe_ok_none {cfg : Cfg A} {s : State} {c : A} {vals : List Int} {now : Nat}
    (h : (exec cfg s (.observe c vals now)).1.isOk = true) :
    outcome cfg s (.observe c vals now) = none := by
  rw [isOk_exec] at h
  cases ho : outcome cfg s (.observe c vals now) with
  | none => rfl
  | some o =>
    cases o with
    | err e => exact absurd ho (h e)
    | noop => have := noop_kind ho; simp [Op.isAck] at this

/-- DEP-1: an accepted `submit` had every prerequisite met by the units of
Completed records. -/
theorem dep1 {cfg : Cfg A} {s : State} {c : A} {r u ver exp now : Nat}
    (h : (exec cfg s (.submit c r u ver exp now)).1.isOk = true) :
    ∀ pu ∈ (cfg.recipe r).requires, pu.2 ≤ doneUnits s.records pu.1 := by
  have F := submit_ok (submit_ok_none h)
  have hp := F.prereq
  simp only [prereqFail, List.any_eq_false, decide_eq_true_eq, Nat.not_lt] at hp
  exact hp

/-- OBS-1: an accepted `observe` found no open record, and it leaves the
records alone (the config is a parameter of the machine, so it never
changes). -/
theorem obs1 {cfg : Cfg A} {s : State} {c : A} {vals : List Int} {now : Nat}
    (h : (exec cfg s (.observe c vals now)).1.isOk = true) :
    (∀ x ∈ s.records, x.status.isOpen = false) ∧
      (exec cfg s (.observe c vals now)).2.records = s.records ∧
      (exec cfg s (.observe c vals now)).2.values = vals := by
  have ho := observe_ok_none h
  refine ⟨(observe_ok ho).closed, ?_, ?_⟩ <;> rw [exec_none ho] <;> rfl

/-- PAUSE-1, first half: while paused, `submit` and `dispatch` change nothing. -/
theorem pause1_blocks {cfg : Cfg A} {s : State} (hp : s.paused = true) :
    (∀ c r u ver exp now, step cfg s (.submit c r u ver exp now) = s) ∧
      (∀ c id now, step cfg s (.dispatch c id now) = s) := by
  constructor
  · intro c r u ver exp now
    have : outcome cfg s (.submit c r u ver exp now) = some (.err .paused) := by
      simp [outcome, guards, submitGuards, firstFail, hp]
    simp only [step, exec_err this]
  · intro c id now
    rcases exec_cases cfg s (.dispatch c id now) with h | ⟨h, -⟩
    · exact h
    · have := (dispatch_ok h).notPaused; rw [hp] at this; cases this

/-- PAUSE-1, second half: `ack`, `cancel`, `settle` and `observe` do not
read the pause flag: from a state that differs only in `paused` they give
the same result and the same post-state (up to `paused`). -/
theorem pause1_transparent (cfg : Cfg A) (s : State) (b : Bool) (op : Op A)
    (hop : (∃ id acc, op = .ack id acc) ∨ (∃ c id now, op = .cancel c id now) ∨
      (∃ c id d, op = .settle c id d) ∨ (∃ c vals now, op = .observe c vals now)) :
    (exec cfg { s with paused := b } op).1 = (exec cfg s op).1 ∧
      (exec cfg { s with paused := b } op).2 = { (exec cfg s op).2 with paused := b } := by
  have hg : outcome cfg { s with paused := b } op = outcome cfg s op := by
    rcases hop with ⟨id, acc, rfl⟩ | ⟨c, id, now, rfl⟩ | ⟨c, id, d, rfl⟩ | ⟨c, vals, now, rfl⟩ <;> rfl
  cases ho : outcome cfg s op with
  | none =>
    have ho' : outcome cfg { s with paused := b } op = none := by rw [hg, ho]
    rw [exec_none ho, exec_none ho']
    rcases hop with ⟨id, acc, rfl⟩ | ⟨c, id, now, rfl⟩ | ⟨c, id, d, rfl⟩ | ⟨c, vals, now, rfl⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
    · cases d <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  | some o =>
    have ho' : outcome cfg { s with paused := b } op = some o := by rw [hg, ho]
    cases o with
    | err e => rw [exec_err ho, exec_err ho']; exact ⟨rfl, rfl⟩
    | noop => rw [exec_noop ho, exec_noop ho']; exact ⟨rfl, rfl⟩

end Pool
