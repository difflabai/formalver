/-
LEAN-WIT: concrete witnesses, all checked by `decide` / `rfl` in the kernel
(never `native_decide`).

* F-1 (the wedge, trace 0 of core.txt): the state is reachable from `init`,
  satisfies `Inv`, has B ≠ 0, and there `settle(true)`, `settle(false)`,
  `cancel` and `observe` all fail. `f1_forever`: from the wedge, for EVERY
  sequence of calls, the values stay [10, 5] and record 0 stays Active, so
  the record never becomes terminal and every `observe` fails `Pending`.
* Non-vacuity: a valid config, a reachable healthy state where the
  premises of LIVE-1 hold (and its conclusion is observed concretely), and
  reachable Completed and Cancelled records.

Accounts: o = 0, a1 = 1, x1 = 2.
-/
import PoolLean.Live

namespace Pool.Witness
open Pool

theorem reach_run {A : Type} [DecidableEq A] [Inhabited A] {cfg : Cfg A} {s : State}
    (h : Reach cfg s) (ops : List (Op A)) : Reach cfg (run cfg s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (Reach.step op h)

theorem run_cons {A : Type} [DecidableEq A] [Inhabited A] (cfg : Cfg A) (s : State) (op : Op A)
    (ops : List (Op A)) : run cfg s (op :: ops) = run cfg (step cfg s op) ops := rfl

/-- The F-1 config: m(0,10,5), m(-100,100,5); t(1,0,1,target);
r(a1,x1,[-2,0],[2,-5],1,[]). -/
def wcfg : Cfg Nat :=
  { owner := 0, maxAge := 0,
    metrics := [⟨0, 10, 5⟩, ⟨-100, 100, 5⟩],
    terms := [⟨1, 0, 1, .target⟩],
    recipes := [⟨1, 2, [-2, 0], [2, -5], 1, []⟩] }

theorem wcfg_valid : Valid wcfg := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    ?_⟩
  intro k hk
  have : k = 0 := by simp [wcfg] at hk; omega
  subst this
  have e : wcfg.recipes[0]'hk = ⟨1, 2, [-2, 0], [2, -5], 1, []⟩ := rfl
  rw [e]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-! ## F-1 -/

def f1ops : List (Op Nat) :=
  [.observe 0 [12, 5] 100, .submit 1 0 1 1 200 100, .dispatch 1 0 101, .ack 0 true]

def wedge : State := run wcfg (init wcfg 100) f1ops

/-- The record of the wedge. -/
def r0 : Rec := ⟨0, 0, 1, 200, .active⟩

theorem wedge_eq : wedge =
    { values := [10, 5], version := 4, observedAt := 100, paused := false, records := [r0],
      base := [12, 5], k0 := 0, eff := 4 } := by decide

/-- Every call of the F-1 run is `Ok` (`submit` returns id 0). -/
theorem f1_results :
    (exec wcfg (init wcfg 100) (.observe 0 [12, 5] 100)).1 = .ok ∧
    (exec wcfg (run wcfg (init wcfg 100) (f1ops.take 1)) (.submit 1 0 1 1 200 100)).1 = .okId 0 ∧
    (exec wcfg (run wcfg (init wcfg 100) (f1ops.take 2)) (.dispatch 1 0 101)).1 = .ok ∧
    (exec wcfg (run wcfg (init wcfg 100) (f1ops.take 3)) (.ack 0 true)).1 = .ok := by decide

theorem wedge_reach : Reach wcfg wedge := reach_run (Reach.init 100) f1ops

theorem wedge_inv : Inv wcfg wedge := reach_inv wcfg_valid wedge_reach

/-- The baseline is disturbed (B ≠ 0): LIVE-1's premise fails, as it must. -/
theorem wedge_B : B wcfg wedge 0 = 2 := by decide

/-- ... although the current point is healthy. -/
theorem wedge_healthy_now : viol wcfg wedge.values 0 = 0 ∧ viol wcfg wedge.values 1 = 0 := by decide

theorem f1_settle_true : exec wcfg wedge (.settle 2 0 true) = (.err .bounds, wedge) := by decide
theorem f1_settle_false : exec wcfg wedge (.settle 2 0 false) = (.err .bounds, wedge) := by decide
theorem f1_cancel_owner : exec wcfg wedge (.cancel 0 0 102) = (.err .pending, wedge) := by decide
theorem f1_cancel_actor : exec wcfg wedge (.cancel 1 0 102) = (.err .pending, wedge) := by decide
theorem f1_observe : exec wcfg wedge (.observe 0 [5, 5] 103) = (.err .pending, wedge) := by decide

/-- The wedge's frozen part: values and records. -/
def Frozen (s : State) : Prop := s.values = [10, 5] ∧ s.records = [r0]

theorem frozen_wedge : Frozen wedge := by rw [wedge_eq]; exact ⟨rfl, rfl⟩

theorem rec0 {s : State} (hr : s.records = [r0]) {id : Nat} (hk : id < s.records.length) :
    id = 0 ∧ s.record id = r0 := by
  rw [hr] at hk
  have : id = 0 := by simp at hk; omega
  subst this
  exact ⟨rfl, by simp [State.record, hr]⟩

/-- One step from a frozen state stays frozen: every call that could move
record 0 or the values fails. -/
theorem frozen_step {s : State} (h : Frozen s) (op : Op Nat) : Frozen (step wcfg s op) := by
  obtain ⟨hv, hr⟩ := h
  rcases exec_cases wcfg s op with h | ⟨ho, he⟩
  · simp only [step, h]; exact ⟨hv, hr⟩
  · cases op with
    | submit c r u ver exp now =>
      exfalso
      have F := submit_ok ho
      have hr0 : r = 0 := by have := F.recipe; simp [wcfg] at this; omega
      subst hr0
      have hu : u = 1 := by
        have h1 := F.unitsLe; have h2 := F.unitsPos
        simp [wcfg, Cfg.recipe] at h1; omega
      subst hu
      have := F.bnd
      simp only [boundsFail, hv, hr] at this
      revert this; decide
    | dispatch c id now =>
      exfalso
      have F := dispatch_ok ho
      obtain ⟨-, h0⟩ := rec0 hr F.found
      have := F.reserved; rw [h0] at this; cases this
    | ack id acc =>
      exfalso
      have F := ack_ok (cfg := wcfg) ho
      obtain ⟨-, h0⟩ := rec0 hr F.found
      have := F.inflight; rw [h0] at this; simp [r0] at this
    | cancel c id now =>
      exfalso
      have F := cancel_ok ho
      obtain ⟨-, h0⟩ := rec0 hr F.found
      have := F.reserved; rw [h0] at this; cases this
    | settle c id done =>
      exfalso
      have F := settle_ok ho
      obtain ⟨hid, h0⟩ := rec0 hr F.found
      subst hid
      cases done with
      | true =>
        have := (F.complete rfl).bnd
        simp only [boundsFail, completeNext, h0, hv, hr] at this
        revert this; decide
      | false =>
        have := (F.release rfl).bnd
        simp only [boundsFail, releaseNext, h0, hv, hr] at this
        revert this; decide
    | pause c b => simp only [step, he, effect]; exact ⟨hv, hr⟩
    | observe c vals now =>
      exfalso
      have F := observe_ok ho
      have := F.closed r0 (by rw [hr]; simp)
      simp [r0, Status.isOpen] at this

theorem frozen_run {s : State} (h : Frozen s) (ops : List (Op Nat)) : Frozen (run wcfg s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (frozen_step h op)

/-- F-1 is permanent: whatever calls follow (any caller, argument, time,
`pause`, new submits), the values stay [10, 5] and record 0 stays Active. -/
theorem f1_forever (ops : List (Op Nat)) :
    (run wcfg wedge ops).values = [10, 5] ∧ (run wcfg wedge ops).records = [r0] :=
  frozen_run frozen_wedge ops

/-- ... so record 0 never becomes terminal ... -/
theorem f1_never_terminal (ops : List (Op Nat)) :
    ∃ h : 0 < (run wcfg wedge ops).records.length,
      (run wcfg wedge ops).records[0].status = .active := by
  have := (f1_forever ops).2
  refine ⟨by rw [this]; decide, ?_⟩
  simp only [this]; rfl

/-- ... and every later `observe` fails (`Pending`, or `Unauthorized` for a
non-owner), so the pool is frozen for observations. -/
theorem f1_observe_forever (ops : List (Op Nat)) (c : Nat) (vals : List Int) (now : Nat) :
    ∃ e, exec wcfg (run wcfg wedge ops) (.observe c vals now) =
      (.err e, run wcfg wedge ops) := by
  have hr := (f1_forever ops).2
  generalize run wcfg wedge ops = s at hr
  cases h : outcome wcfg s (.observe c vals now) with
  | none =>
    have := (observe_ok h).closed r0 (by rw [hr]; simp)
    simp [r0, Status.isOpen] at this
  | some o =>
    cases o with
    | err e => exact ⟨e, exec_err h⟩
    | noop => have := noop_kind h; simp [Op.isAck] at this

/-- ... and every later `settle` of record 0 fails. -/
theorem f1_settle_forever (ops : List (Op Nat)) (c : Nat) (done : Bool) :
    ∃ e, exec wcfg (run wcfg wedge ops) (.settle c 0 done) = (.err e, run wcfg wedge ops) := by
  have ⟨hv, hr⟩ := f1_forever ops
  generalize run wcfg wedge ops = s at hv hr
  cases h : outcome wcfg s (.settle c 0 done) with
  | none =>
    have := frozen_step ⟨hv, hr⟩ (.settle c 0 done)
    have hs := exec_none h
    simp only [Frozen, step, hs, effect] at this
    cases done with
    | true =>
      simp only [ite_true] at this
      have h2 := this.2
      simp [hr, setStatus, r0] at h2
    | false =>
      simp only [Bool.false_eq_true, ite_false, release] at this
      have h2 := this.2
      simp [hr, setStatus, r0] at h2
  | some o =>
    cases o with
    | err e => exact ⟨e, exec_err h⟩
    | noop =>
      exfalso
      simp only [outcome, guards, settleGuards, foundGuard, hr, State.record] at h
      by_cases hc : c = 2
      · subst hc
        cases done <;> simp [firstFail, wcfg, Cfg.recipe, r0, inFlight] at h <;>
          · have := Guard.firstFail_mem h
            simp [releaseGuards, addGuards, boundsGuards, verGuard, foundGuard] at this
      · simp [firstFail, hc, wcfg, Cfg.recipe, r0] at h

/-! ## Non-vacuity: the healthy path -/

/-- From `init`: submit 1 unit, dispatch it. -/
def hops : List (Op Nat) := [.submit 1 0 1 0 200 100, .dispatch 1 0 101]

def hstate : State := run wcfg (init wcfg 100) hops

theorem hstate_eq : hstate =
    { values := [3, 5], version := 2, observedAt := 100, paused := false,
      records := [⟨0, 0, 1, 200, .dispatched⟩], base := [5, 5], k0 := 0, eff := 2 } := by decide

theorem hstate_reach : Reach wcfg hstate := reach_run (Reach.init 100) hops

/-- LIVE-1's premises are satisfiable on a reachable state. -/
theorem live1_premises :
    (∀ i < wcfg.n, B wcfg hstate i = 0) ∧ hstate.version < U32_MAX ∧
      ∃ h : 0 < hstate.records.length, inFlight hstate.records[0].status = true := by
  rw [hstate_eq]
  refine ⟨?_, by decide, by decide, by decide⟩
  intro i hi
  have : i = 0 ∨ i = 1 := by simp [wcfg, Cfg.n] at hi; omega
  rcases this with rfl | rfl <;> decide

/-- `live1` applied to it, and the concrete settle agreeing. -/
theorem live1_instance : outcome wcfg hstate (.settle 2 0 true) = none := by
  have ⟨hB, hv, hk, hst⟩ := live1_premises
  have := live1_reach wcfg_valid hstate_reach hB hv hk hst
  have e : (wcfg.recipe (hstate.records[0]'hk).recipe).executor = 2 := by
    simp only [hstate_eq]; rfl
  rw [e] at this
  exact this

theorem healthy_settle :
    exec wcfg hstate (.settle 2 0 true) =
      (.ok, { values := [5, 0], version := 3, observedAt := 100, paused := false,
              records := [⟨0, 0, 1, 200, .completed⟩], base := [5, 5], k0 := 0, eff := 3 }) := by
  decide

/-- A Cancelled record is reachable too (submit, then the actor cancels). -/
theorem cancelled_reach :
    run wcfg (init wcfg 100) [.submit 1 0 1 0 200 100, .cancel 1 0 102] =
      { values := [5, 5], version := 2, observedAt := 100, paused := false,
        records := [⟨0, 0, 1, 200, .cancelled⟩], base := [5, 5], k0 := 0, eff := 2 } := by decide

/-- STALE-1 concretely: a submit carrying an old version fails `Stale`. -/
theorem stale_instance : (exec wcfg hstate (.submit 1 0 1 0 300 102)).1 = .err .stale := by decide

/-- A healthy dispatched record whose execution the executor reports unknown,
then settles: the Unknown branch of LIVE-1. -/
theorem unknown_settle :
    (exec wcfg (run wcfg hstate [.ack 0 false]) (.settle 2 0 true)).1 = .ok ∧
      (run wcfg hstate [.ack 0 false]).records = [⟨0, 0, 1, 200, .unknown⟩] := by decide

end Pool.Witness
