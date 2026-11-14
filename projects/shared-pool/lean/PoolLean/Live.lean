/-
LEAN-LIVE1: LIVE-1 at every size. In any state satisfying `Inv` whose
baseline is healthy (B = 0: the last `observe`, or `new`, left every metric
inside [min, max]) and whose version is below `u32::MAX`, the executor can
settle every Dispatched/Active/Unknown record as completed. Also
INV-HEALTHY: with B = 0, every subset of the open records' completions
lands inside [min, max].

The premise B = 0 is necessary: the F-1 witness (Witness.lean) is a
reachable `Inv` state with B ≠ 0 in which both settles fail.
-/
import PoolLean.StepProps

namespace Pool

variable {A : Type} [DecidableEq A] [Inhabited A]

theorem metric_bounded {cfg : Cfg A} (hV : Valid cfg) {i : Nat} (hi : i < cfg.n) :
    Bounded (cfg.metric i).min ∧ Bounded (cfg.metric i).max := by
  have hm : cfg.metric i = cfg.metrics[i] := by simp [Cfg.metric, Cfg.n] at hi ⊢; simp [hi]
  obtain ⟨h1, h2, -⟩ := hV.metric _ (List.getElem_mem hi)
  rw [hm]; exact ⟨h1, h2⟩

/-- With B = 0, the envelope lies inside [min, max] on every metric. -/
theorem env_inside {cfg : Cfg A} {s : State} (I : Inv cfg s) (hB : ∀ i < cfg.n, B cfg s i = 0)
    {i : Nat} (hi : i < cfg.n) :
    (cfg.metric i).min ≤ low cfg s.records s.values none none i ∧
      high cfg s.records s.values none none i ≤ (cfg.metric i).max := by
  have h := I.hard.2 i hi
  rw [hB i hi] at h
  simp only [ev] at h
  omega

/-- INV-HEALTHY: with B = 0, applying the completions of any subset `sel`
of the open records to the current values lands inside [min, max]. -/
theorem healthy {cfg : Cfg A} {s : State} (I : Inv cfg s) (hB : ∀ i < cfg.n, B cfg s i = 0)
    (sel : Rec → Bool) {i : Nat} (hi : i < cfg.n) :
    (cfg.metric i).min ≤ get s.values i +
        sumI (fun c => if c.status.isOpen && sel c then dlt cfg c.recipe c.units i else 0) s.records ∧
      get s.values i +
        sumI (fun c => if c.status.isOpen && sel c then dlt cfg c.recipe c.units i else 0) s.records
        ≤ (cfg.metric i).max := by
  obtain ⟨h1, h2⟩ := env_inside I hB hi
  have hl : envS (fun x => min 0 x) cfg s.records none i ≤
      sumI (fun c => if c.status.isOpen && sel c then dlt cfg c.recipe c.units i else 0) s.records := by
    apply sumI_le; intro c _
    simp only [inEnv]
    have := Int.min_le_left 0 (dlt cfg c.recipe c.units i)
    have := Int.min_le_right 0 (dlt cfg c.recipe c.units i)
    by_cases ho : c.status.isOpen <;> by_cases hs : sel c <;> simp [ho, hs] <;> omega
  have hh : sumI (fun c => if c.status.isOpen && sel c then dlt cfg c.recipe c.units i else 0) s.records ≤
      envS (fun x => max 0 x) cfg s.records none i := by
    apply sumI_le; intro c _
    simp only [inEnv]
    have := Int.le_max_left 0 (dlt cfg c.recipe c.units i)
    have := Int.le_max_right 0 (dlt cfg c.recipe c.units i)
    by_cases ho : c.status.isOpen <;> by_cases hs : sel c <;> simp [ho, hs] <;> omega
  simp only [low, high, extraD] at h1 h2
  omega

/-- LEAN-LIVE1 (LIVE-1): in an `Inv` state with B = 0 and version below
`u32::MAX`, `settle(executor, id, true)` passes every guard for every
Dispatched/Active/Unknown record `id`. -/
theorem live1 {cfg : Cfg A} (hV : Valid cfg) {s : State} (I : Inv cfg s)
    (hB : ∀ i < cfg.n, B cfg s i = 0) (hv : s.version < U32_MAX)
    {id : Nat} (hk : id < s.records.length) (hst : inFlight s.records[id].status = true) :
    outcome cfg s (.settle (cfg.recipe s.records[id].recipe).executor id true) = none := by
  have W := I.wf
  have hr := record_eq hk
  have R := W.recs id hk
  have RO := hV.recipe _ R.recipe
  have hcomp : (cfg.recipe s.records[id].recipe).complete.length = cfg.n := by
    have : cfg.recipe s.records[id].recipe = cfg.recipes[s.records[id].recipe]'R.recipe := by
      simp [Cfg.recipe, R.recipe]
    rw [this]; exact RO.completeLen
  have ho : s.records[id].status.isOpen = true := by
    revert hst; cases s.records[id].status <;> simp [inFlight, Status.isOpen]
  have hnc : s.records[id].status ≠ .completed := fun h => by rw [h] at ho; cases ho
  have hid : ∀ j (h : j < s.records.length), s.records[j].id = j := fun j h => (W.recs j h).id
  let next := completeNext cfg s id
  have hnlen : next.length = cfg.n := by
    simp only [next, completeNext, length_addv, hr, hcomp, W.vlen]; simp
  -- the arithmetic of one metric
  have key : ∀ i < cfg.n,
      (cfg.metric i).min ≤ get next i ∧ get next i ≤ (cfg.metric i).max ∧
      (cfg.metric i).min ≤ low cfg s.records next none (some id) i ∧
      high cfg s.records next none (some id) i ≤ (cfg.metric i).max ∧
      low cfg s.records next none (some id) i ≤ high cfg s.records next none (some id) i := by
    intro i hi
    have hi1 : i < s.values.length := by rw [W.vlen]; exact hi
    have hn : get next i = get s.values i + dlt cfg s.records[id].recipe s.records[id].units i := by
      simp only [next, completeNext, hr, dlt]
      exact get_addv hi1 (by rw [hcomp]; exact hi)
    obtain ⟨h1, h2⟩ := env_inside I hB hi
    have sl := envS_split (fun x => min 0 x) cfg hk hid i
    have sh := envS_split (fun x => max 0 x) cfg hk hid i
    have e1 := envS_min_nonpos cfg s.records (some id) i
    have e2 := envS_max_nonneg cfg s.records (some id) i
    simp only [ho, ite_true] at sl sh
    simp only [low, high, extraD] at h1 h2 ⊢
    rw [hn]
    omega
  simp only [outcome, guards, settleGuards, firstFail_eq_none, noFire_append, noFire_cons,
    noFire_nil, foundGuard, addGuards, boundsGuards, verGuard, ite_true, List.cons_append,
    List.nil_append, and_true]
  refine ⟨by simp; omega, by simp [hr], by simp [hr, hnc], by simp [hr, hst], ?_, ?_, ?_, ?_,
    by simp; omega⟩
  · simp [hr, hcomp, W.vlen]
  · simp only [Bool.not_eq_false', decide_eq_true_eq]
    show AllB next
    apply allB_of_get
    intro i hi
    rw [hnlen] at hi
    obtain ⟨k1, k2, -⟩ := key i hi
    obtain ⟨⟨m1, m2⟩, ⟨m3, m4⟩⟩ := metric_bounded hV hi
    simp only [Bounded] at *; exact ⟨by omega, by omega⟩
  · show envFail cfg s.records next none (some id) = false
    rw [envFail_false]
    intro i hi
    rw [hnlen] at hi
    obtain ⟨-, -, k3, k4, k5⟩ := key i hi
    obtain ⟨⟨m1, m2⟩, ⟨m3, m4⟩⟩ := metric_bounded hV hi
    simp only [Bounded] at *
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  · show boundsFail cfg s next none (some id) = false
    rw [boundsFail_false]
    intro i hi
    obtain ⟨-, -, k3, k4, -⟩ := key i hi
    have := viol_nonneg cfg s.values i
    simp only [ev]
    omega

/-- LIVE-1 as a run: the settle is `Ok` and completes the record. -/
theorem live1_exec {cfg : Cfg A} (hV : Valid cfg) {s : State} (I : Inv cfg s)
    (hB : ∀ i < cfg.n, B cfg s i = 0) (hv : s.version < U32_MAX)
    {id : Nat} (hk : id < s.records.length) (hst : inFlight s.records[id].status = true) :
    (exec cfg s (.settle (cfg.recipe s.records[id].recipe).executor id true)).1 = .ok ∧
      ∃ h : id < (step cfg s (.settle (cfg.recipe s.records[id].recipe).executor id true)).records.length,
        (step cfg s (.settle (cfg.recipe s.records[id].recipe).executor id true)).records[id].status =
          .completed := by
  have ho := live1 hV I hB hv hk hst
  refine ⟨by rw [exec_none ho]; rfl, ?_⟩
  simp only [step, exec_none ho]
  have h' : id < (setStatus s.records id .completed).length := by rw [length_setStatus]; exact hk
  refine ⟨h', ?_⟩
  show ((setStatus s.records id .completed)[id]'h').status = .completed
  rw [getElem_setStatus hk]; simp

/-- LIVE-1 from any reachable state of a valid config. -/
theorem live1_reach {cfg : Cfg A} (hV : Valid cfg) {s : State} (h : Reach cfg s)
    (hB : ∀ i < cfg.n, B cfg s i = 0) (hv : s.version < U32_MAX)
    {id : Nat} (hk : id < s.records.length) (hst : inFlight s.records[id].status = true) :
    outcome cfg s (.settle (cfg.recipe s.records[id].recipe).executor id true) = none :=
  live1 hV (reach_inv hV h) hB hv hk hst

end Pool
