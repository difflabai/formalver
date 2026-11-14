/-
LEAN-IND: `Inv` (INV-WF, INV-LEDGER, INV-HARD, INV-DEP, INV-VER) holds
initially and is preserved by every call, for every config `validate`
accepts and states of every size (any number of metrics, terms, recipes and
records); hence it holds in every reachable state (`reach_inv`).
-/
import PoolLean.Facts

namespace Pool

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- The shape of every effective post-state that changes values and records. -/
def upd (s : State) (v : List Int) (recs : List Rec) : State :=
  { s with values := v, records := recs, version := s.version + 1, eff := s.eff + 1 }

/-! ## init -/

theorem inv_init {cfg : Cfg A} (hV : Valid cfg) (now : Nat) : Inv cfg (init cfg now) := by
  have hlen : (cfg.metrics.map (·.initial)).length = cfg.n := by simp [Cfg.n]
  have hb : AllB (cfg.metrics.map (·.initial)) := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨h1, h2, _, h4, h5⟩ := hV.metric m hm
    simp only [Bounded] at *; omega
  refine ⟨⟨hlen, hb, hlen, hb, by simp [init, MAX_RECORDS], by simp [init], by simp [init]⟩,
    ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i _; simp [init, ledger]
  · rw [envFail_false]; intro i hi
    simp only [init, low, high, envS, extraD, sumI_nil, Int.add_zero]
    have := allB_get hb hi
    exact ⟨this, this⟩
  · intro i _; simp [init, ev, low, high, envS, extraD, B, viol]
  · intro j hj; simp [init] at hj
  · simp [init, Ver, U32_MAX]

/-! ## Generic: a status update of record `k` -/

section generic

variable {cfg : Cfg A} {s : State} {k : Nat} {st : Status}

theorem wf_set (W : WF cfg s) (hk : k < s.records.length) (ho : s.records[k].status.isOpen = true)
    {v : List Int} (hv : v.length = cfg.n) (hvb : AllB v) :
    WF cfg (upd s v (setStatus s.records k st)) := by
  refine ⟨hv, hvb, W.blen, W.bbnd, ?_, ?_, ?_⟩
  · simp only [upd, length_setStatus]; exact W.full
  · simp only [upd, length_setStatus]; exact W.k0le
  · intro j hj
    simp only [upd] at hj ⊢
    have hj' : j < s.records.length := by rwa [length_setStatus] at hj
    have R := W.recs j hj'
    rw [getElem_setStatus hk]
    split
    · rename_i h
      subst h
      have hk0 : ¬ k < s.k0 := fun h => by have := R.old h; rw [ho] at this; cases this
      exact ⟨R.id, R.recipe, R.unitsPos, R.unitsLe, fun h => absurd h hk0⟩
    · exact ⟨R.id, R.recipe, R.unitsPos, R.unitsLe, R.old⟩

theorem k0_le_of_open (W : WF cfg s) (hk : k < s.records.length)
    (ho : s.records[k].status.isOpen = true) : s.k0 ≤ s.records[k].id := by
  have R := W.recs k hk
  rw [R.id]
  refine Nat.le_of_not_lt fun h => ?_
  have := R.old h; rw [ho] at this; cases this

theorem ledger_set (W : WF cfg s) (L : Ledger cfg s) (hk : k < s.records.length)
    (ho : s.records[k].status.isOpen = true) {v : List Int}
    (hv : ∀ i < cfg.n, get v i = get s.values i +
      (contrib cfg i { s.records[k] with status := st } - contrib cfg i s.records[k])) :
    Ledger cfg (upd s v (setStatus s.records k st)) := by
  intro i hi
  simp only [upd]
  rw [ledger_setStatus cfg hk st s.k0 i (k0_le_of_open W hk ho), hv i hi, L i hi]
  omega

theorem hard_close (W : WF cfg s) (H : Hard cfg s) (hk : k < s.records.length)
    (hst : st.isOpen = false) {v : List Int} (henv : envFail cfg s.records v none (some k) = false)
    (hbnd : boundsFail cfg s v none (some k) = false) :
    Hard cfg (upd s v (setStatus s.records k st)) := by
  have hid : ∀ j (h : j < s.records.length), s.records[j].id = j := fun j h => (W.recs j h).id
  have hl : ∀ i, low cfg (setStatus s.records k st) v none none i = low cfg s.records v none (some k) i := by
    intro i; simp only [low, envS_close _ cfg hk hid hst]
  have hh : ∀ i, high cfg (setStatus s.records k st) v none none i = high cfg s.records v none (some k) i := by
    intro i; simp only [high, envS_close _ cfg hk hid hst]
  constructor
  · show envFail cfg (setStatus s.records k st) v none none = false
    rw [envFail_congr hl hh]; exact henv
  · intro i hi
    show ev cfg (setStatus s.records k st) v none none i ≤ viol cfg s.base i
    rw [ev_congr hl hh]
    have h1 := (boundsFail_false.mp hbnd) i hi
    have h2 := viol_le_ev cfg s.records s.values none none i
    have h3 := H.2 i hi
    simp only [B] at h3
    omega

theorem hard_open (H : Hard cfg s) (hk : k < s.records.length)
    (ho : s.records[k].status.isOpen = true) (hst : st.isOpen = true) :
    Hard cfg (upd s s.values (setStatus s.records k st)) := by
  have hl : ∀ i, low cfg (setStatus s.records k st) s.values none none i = low cfg s.records s.values none none i := by
    intro i; simp only [low, envS_open _ cfg hk ho hst]
  have hh : ∀ i, high cfg (setStatus s.records k st) s.values none none i = high cfg s.records s.values none none i := by
    intro i; simp only [high, envS_open _ cfg hk ho hst]
  constructor
  · show envFail cfg (setStatus s.records k st) s.values none none = false
    rw [envFail_congr hl hh]; exact H.1
  · intro i hi
    show ev cfg (setStatus s.records k st) s.values none none i ≤ viol cfg s.base i
    rw [ev_congr hl hh]; exact H.2 i hi

theorem dep_set (D : Dep cfg s) (hk : k < s.records.length)
    (hnc : s.records[k].status ≠ .completed) {v : List Int} :
    Dep cfg (upd s v (setStatus s.records k st)) := by
  intro j hj pu hpu
  simp only [upd] at hj hpu ⊢
  have hj' : j < s.records.length := by rwa [length_setStatus] at hj
  have e : (setStatus s.records k st)[j].recipe = s.records[j].recipe := by
    rw [getElem_setStatus hk]; split
    · rename_i h; subst h; rfl
    · rfl
  rw [e] at hpu
  exact Nat.le_trans (D j hj' pu hpu) (doneUnits_setStatus_ge hk hnc st j pu.1)

theorem ver_upd (V : Ver s) (h : s.version < U32_MAX) (v : List Int) (recs : List Rec) :
    Ver (upd s v recs) := by
  simp only [Ver, upd] at *; omega

/-- A status update of an open record, with the new values' ledger delta. -/
theorem inv_set (I : Inv cfg s) (hk : k < s.records.length) (ho : s.records[k].status.isOpen = true)
    (hver : s.version < U32_MAX) {v : List Int} (hv : v.length = cfg.n) (hvb : AllB v)
    (hl : ∀ i < cfg.n, get v i = get s.values i +
      (contrib cfg i { s.records[k] with status := st } - contrib cfg i s.records[k]))
    (hh : Hard cfg (upd s v (setStatus s.records k st))) :
    Inv cfg (upd s v (setStatus s.records k st)) :=
  ⟨wf_set I.wf hk ho hv hvb, ledger_set I.wf I.ledger hk ho hl, hh,
   dep_set I.dep hk (fun h => by rw [h] at ho; cases ho), ver_upd I.ver hver v _⟩

end generic

/-! ## Each call -/

section calls

variable {cfg : Cfg A} {s : State}

theorem inv_dispatch {c : A} {id now : Nat} (I : Inv cfg s)
    (h : outcome cfg s (.dispatch c id now) = none) :
    Inv cfg { effect cfg s (.dispatch c id now) with eff := s.eff + 1 } := by
  have F := dispatch_ok h
  have hk := F.found
  have hst := F.reserved
  rw [record_eq F.found] at hst
  have ho : s.records[id].status.isOpen = true := by rw [hst]; rfl
  show Inv cfg (upd s s.values (setStatus s.records id .dispatched))
  exact inv_set I F.found ho F.noOverflow I.wf.vlen I.wf.vbnd
    (fun i _ => by simp [contrib, hst]) (hard_open I.hard F.found ho rfl)

theorem inv_ack {id : Nat} {acc : Bool} (I : Inv cfg s) (h : outcome cfg s (.ack id acc) = none) :
    Inv cfg { effect cfg s (.ack id acc) with eff := s.eff + 1 } := by
  have F := ack_ok (cfg := cfg) h
  have hk := F.found
  have hst := F.inflight
  rw [record_eq F.found] at hst
  have ho : s.records[id].status.isOpen = true := by rcases hst with h | h <;> rw [h] <;> rfl
  have hst' : (ackStatus acc).isOpen = true := by cases acc <;> rfl
  have hc : ∀ i, contrib cfg i { s.records[id] with status := ackStatus acc } =
      contrib cfg i s.records[id] := by
    intro i
    rcases hst with h | h <;> cases acc <;> simp [contrib, h, ackStatus]
  show Inv cfg (upd s s.values (setStatus s.records id (ackStatus acc)))
  exact inv_set I F.found ho F.noOverflow I.wf.vlen I.wf.vbnd
    (fun i _ => by rw [hc]; omega) (hard_open I.hard F.found ho hst')

/-- `release(id)` from an open record. -/
theorem inv_release {id : Nat} (I : Inv cfg s) (hk : id < s.records.length)
    (ho : s.records[id].status.isOpen = true) (F : ReleaseOk cfg s id) :
    Inv cfg (release cfg s id |> fun s' => { s' with eff := s.eff + 1 }) := by
  have hlen := F.len
  rw [record_eq hk] at hlen
  have hnc : s.records[id].status ≠ .cancelled := fun h => by rw [h] at ho; cases ho
  have hnd : s.records[id].status ≠ .completed := fun h => by rw [h] at ho; cases ho
  show Inv cfg (upd s (releaseNext cfg s id) (setStatus s.records id .cancelled))
  refine inv_set I hk ho F.noOverflow ?_ F.nextB ?_ (hard_close I.wf I.hard hk rfl F.env F.bnd)
  · simp only [releaseNext, length_addv, length_neg, record_eq hk, ← hlen, I.wf.vlen]; simp
  · intro i hi
    have hi1 : i < s.values.length := by rw [I.wf.vlen]; exact hi
    simp only [releaseNext, record_eq hk]
    rw [get_addv hi1 (by rw [length_neg, ← hlen]; exact hi1), get_neg]
    simp [contrib, hnc, hnd, Int.neg_mul]

theorem inv_cancel {c : A} {id now : Nat} (I : Inv cfg s)
    (h : outcome cfg s (.cancel c id now) = none) :
    Inv cfg { effect cfg s (.cancel c id now) with eff := s.eff + 1 } := by
  have F := cancel_ok h
  have hk := F.found
  have hst := F.reserved
  rw [record_eq F.found] at hst
  exact inv_release I F.found (by rw [hst]; rfl) F.release

theorem inv_settle {c : A} {id : Nat} {done : Bool} (I : Inv cfg s)
    (h : outcome cfg s (.settle c id done) = none) :
    Inv cfg { effect cfg s (.settle c id done) with eff := s.eff + 1 } := by
  have F := settle_ok h
  have hk := F.found
  have hst := F.inflight
  rw [record_eq F.found] at hst
  have ho : s.records[id].status.isOpen = true := by
    revert hst; cases s.records[id].status <;> simp [inFlight, Status.isOpen]
  have hnc : s.records[id].status ≠ .cancelled := fun h => by rw [h] at ho; cases ho
  have hnd : s.records[id].status ≠ .completed := fun h => by rw [h] at ho; cases ho
  cases done with
  | false => exact inv_release I F.found ho (F.release rfl)
  | true =>
    have G := F.complete rfl
    have hlen := G.len
    rw [record_eq F.found] at hlen
    show Inv cfg (upd s (completeNext cfg s id) (setStatus s.records id .completed))
    refine inv_set I F.found ho G.noOverflow ?_ G.nextB ?_
      (hard_close I.wf I.hard F.found rfl G.env G.bnd)
    · simp only [completeNext, length_addv, record_eq F.found, ← hlen, I.wf.vlen]; simp
    · intro i hi
      have hi1 : i < s.values.length := by rw [I.wf.vlen]; exact hi
      simp only [completeNext, record_eq F.found]
      rw [get_addv hi1 (by rw [← hlen]; exact hi1)]
      simp [contrib, hnc, hnd]
      omega

theorem inv_submit {c : A} {r u ver exp now : Nat} (I : Inv cfg s)
    (h : outcome cfg s (.submit c r u ver exp now) = none) :
    Inv cfg { effect cfg s (.submit c r u ver exp now) with eff := s.eff + 1 } := by
  have F := submit_ok h
  have W := I.wf
  let new : Rec := ⟨s.records.length, r, u, exp, .reserved⟩
  let next := addv s.values (cfg.recipe r).reserve u
  have hnext : next.length = cfg.n := by
    simp only [next, length_addv, ← F.len, W.vlen]; simp
  show Inv cfg (upd s next (s.records ++ [new]))
  have hl : ∀ i, low cfg (s.records ++ [new]) next none none i = low cfg s.records next (some (r, u)) none i := by
    intro i; simp only [low, new, envS_append_new, extraD]; omega
  have hh : ∀ i, high cfg (s.records ++ [new]) next none none i = high cfg s.records next (some (r, u)) none i := by
    intro i; simp only [high, new, envS_append_new, extraD]; omega
  refine ⟨⟨hnext, F.nextB, W.blen, W.bbnd, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · show (s.records ++ [new]).length ≤ MAX_RECORDS
    simp only [List.length_append, List.length_singleton]; exact F.full
  · show s.k0 ≤ (s.records ++ [new]).length
    simp only [List.length_append, List.length_singleton]; have := W.k0le; omega
  · intro j hj
    simp only [upd, List.length_append, List.length_singleton] at hj ⊢
    by_cases hjl : j < s.records.length
    · have R := W.recs j hjl
      rw [List.getElem_append_left hjl]
      exact ⟨R.id, R.recipe, R.unitsPos, R.unitsLe, R.old⟩
    · have hj' : j = s.records.length := by omega
      subst hj'
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero, new]
      exact ⟨rfl, F.recipe, F.unitsPos, F.unitsLe, fun h => absurd W.k0le (by omega)⟩
  · intro i hi
    simp only [upd, next]
    have hi1 : i < s.values.length := by rw [W.vlen]; exact hi
    rw [ledger_append_new cfg s.records s.k0 r u exp i W.k0le,
      get_addv hi1 (by rw [← F.len]; exact hi1), I.ledger i hi]
    omega
  · show envFail cfg (s.records ++ [new]) next none none = false
    rw [envFail_congr hl hh]; exact F.env
  · intro i hi
    show ev cfg (s.records ++ [new]) next none none i ≤ viol cfg s.base i
    rw [ev_congr hl hh]
    simp only [next]
    have h1 := (boundsFail_false.mp F.bnd) i hi
    have h2 := viol_le_ev cfg s.records s.values none none i
    have h3 := I.hard.2 i hi
    simp only [B] at h3
    omega
  · intro j hj pu hpu
    simp only [upd, List.length_append, List.length_singleton] at hj hpu ⊢
    by_cases hjl : j < s.records.length
    · rw [List.getElem_append_left hjl] at hpu
      rw [List.take_append_of_le_length (Nat.le_of_lt hjl)]
      exact I.dep j hjl pu hpu
    · have hj' : j = s.records.length := by omega
      subst hj'
      rw [List.getElem_append_right (Nat.le_refl _)] at hpu
      simp only [Nat.sub_self, List.getElem_cons_zero, new] at hpu
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      have := F.prereq
      simp only [prereqFail, List.any_eq_false, decide_eq_true_eq, Nat.not_lt] at this
      exact this pu hpu
  · exact ver_upd I.ver F.noOverflow _ _

theorem inv_pause {c : A} {b : Bool} (I : Inv cfg s) (h : outcome cfg s (.pause c b) = none) :
    Inv cfg { effect cfg s (.pause c b) with eff := s.eff + 1 } := by
  have F := pause_ok h
  obtain ⟨W, L, H, D, V⟩ := I
  show Inv cfg { s with paused := b, version := s.version + 1, eff := s.eff + 1 }
  exact ⟨⟨W.vlen, W.vbnd, W.blen, W.bbnd, W.full, W.k0le, fun j hj => W.recs j hj⟩, L, H, D,
    by show s.version + 1 = s.eff + 1 ∧ s.version + 1 ≤ U32_MAX
       have := V.1; have := F.2; omega⟩

theorem inv_observe {c : A} {vals : List Int} {now : Nat} (I : Inv cfg s)
    (h : outcome cfg s (.observe c vals now) = none) :
    Inv cfg { effect cfg s (.observe c vals now) with eff := s.eff + 1 } := by
  have F := observe_ok h
  obtain ⟨W, L, H, D, V⟩ := I
  show Inv cfg
    { s with values := vals, observedAt := now, version := s.version + 1, base := vals,
             k0 := s.records.length, eff := s.eff + 1 }
  have hlen : vals.length = cfg.n := by rw [F.len, W.vlen]
  have hclosed : ∀ j (hj : j < s.records.length), s.records[j].status.isOpen = false :=
    fun j hj => F.closed _ (List.getElem_mem hj)
  have henv : ∀ (f : Int → Int) i, envS f cfg s.records none i = 0 := by
    intro f i
    apply Eq.trans (sumI_congr _) (sumI_zero s.records)
    intro x hx
    simp [inEnv, F.closed x hx]
  refine ⟨⟨hlen, F.valsB, hlen, F.valsB, W.full, Nat.le_refl _, ?_⟩, ?_, ⟨?_, ?_⟩, D, ?_⟩
  · intro j hj
    have R := W.recs j hj
    exact ⟨R.id, R.recipe, R.unitsPos, R.unitsLe, fun _ => hclosed j hj⟩
  · intro i _
    show get vals i = get vals i + ledger cfg s.records s.records.length i
    have : ledger cfg s.records s.records.length i = 0 := by
      apply Eq.trans (sumI_congr _) (sumI_zero s.records)
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      have := (W.recs j hj).id
      simp only [this]; simp; omega
    omega
  · show envFail cfg s.records vals none none = false
    rw [envFail_false]; intro i hi
    simp only [low, high, henv, extraD, Int.add_zero]
    have := allB_get F.valsB hi
    exact ⟨this, this⟩
  · intro i _
    show ev cfg s.records vals none none i ≤ viol cfg vals i
    simp only [ev, low, high, henv, extraD, Int.add_zero, viol]
    omega
  · show s.version + 1 = s.eff + 1 ∧ s.version + 1 ≤ U32_MAX
    have := V.1; have := F.noOverflow; omega

end calls

/-! ## Every call, every reachable state -/

theorem inv_effect {cfg : Cfg A} {s : State} {op : Op A} (I : Inv cfg s)
    (h : outcome cfg s op = none) : Inv cfg { effect cfg s op with eff := s.eff + 1 } := by
  cases op with
  | submit c r u ver exp now => exact inv_submit I h
  | dispatch c id now => exact inv_dispatch I h
  | ack id acc => exact inv_ack I h
  | cancel c id now => exact inv_cancel I h
  | settle c id done => exact inv_settle I h
  | pause c b => exact inv_pause I h
  | observe c vals now => exact inv_observe I h

/-- LEAN-IND: every call, accepted or not, preserves `Inv`. -/
theorem inv_step {cfg : Cfg A} {s : State} (I : Inv cfg s) (op : Op A) : Inv cfg (step cfg s op) := by
  rcases exec_cases cfg s op with h | ⟨h1, h2⟩
  · simp only [step, h]; exact I
  · simp only [step, h2]; exact inv_effect I h1

/-- LEAN-IND: `Inv` holds in every reachable state of every valid config. -/
theorem reach_inv {cfg : Cfg A} (hV : Valid cfg) {s : State} (h : Reach cfg s) : Inv cfg s := by
  induction h with
  | init now => exact inv_init hV now
  | step op _ ih => exact inv_step ih op

end Pool
