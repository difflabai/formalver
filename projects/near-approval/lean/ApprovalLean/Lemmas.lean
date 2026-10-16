/-
Shared lemmas: the principal map, `countIdx`, and how each action's
effect rewrites the state's fields.
-/
import ApprovalLean.Props

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## The principal map -/

@[simp] theorem plookup_nil (k : K) : plookup k ([] : List (K × Principal A)) = none := rfl

theorem plookup_cons (k k' : K) (p : Principal A) (l : List (K × Principal A)) :
    plookup k ((k', p) :: l) = if k' = k then some p else plookup k l := rfl

@[simp] theorem plookup_cons_self (k : K) (p : Principal A) (l : List (K × Principal A)) :
    plookup k ((k, p) :: l) = some p := by simp [plookup_cons]

theorem plookup_cons_ne {k k' : K} (h : k' ≠ k) (p : Principal A) (l : List (K × Principal A)) :
    plookup k ((k', p) :: l) = plookup k l := by simp [plookup_cons, h]

theorem plookup_perase (k k' : K) (l : List (K × Principal A)) :
    plookup k' (perase k l) = if k' = k then none else plookup k' l := by
  induction l with
  | nil => simp [perase]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · subst h0
      by_cases h1 : k' = k0
      · subst h1; simp [perase, ih]
      · simp [perase, plookup_cons, h1, Ne.symm h1, ih]
    · by_cases h1 : k' = k0
      · subst h1; simp [perase, plookup_cons, h0, Ne.symm h0]
      · simp [perase, plookup_cons, h0, Ne.symm h1, ih]

theorem plookup_pmodify (k k' : K) (f : Principal A → Principal A)
    (l : List (K × Principal A)) :
    plookup k' (pmodify k f l) = if k' = k then (plookup k l).map f else plookup k' l := by
  induction l with
  | nil => simp [pmodify]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · subst h0
      by_cases h1 : k' = k0
      · subst h1; simp [pmodify]
      · simp [pmodify, plookup_cons, h1, Ne.symm h1, ih]
    · by_cases h1 : k' = k0
      · subst h1; simp [pmodify, plookup_cons, h0, Ne.symm h0]
      · simp [pmodify, plookup_cons, h0, Ne.symm h1, ih]

theorem perase_keys_sublist (k : K) (l : List (K × Principal A)) :
    ((perase k l).map Prod.fst).Sublist (l.map Prod.fst) := by
  induction l with
  | nil => simp [perase]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · simp only [perase, if_pos h0, List.map_cons]; exact ih.cons _
    · simp only [perase, if_neg h0, List.map_cons]; exact ih.cons₂ _

theorem perase_sublist (k : K) (l : List (K × Principal A)) : (perase k l).Sublist l := by
  induction l with
  | nil => simp [perase]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · simp only [perase, if_pos h0]; exact ih.cons _
    · simp only [perase, if_neg h0]; exact ih.cons₂ _

theorem not_mem_perase_keys (k : K) (l : List (K × Principal A)) :
    k ∉ (perase k l).map Prod.fst := by
  induction l with
  | nil => simp [perase]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · simp only [perase, if_pos h0]; exact ih
    · simp only [perase, if_neg h0, List.map_cons, List.mem_cons]
      rintro (h | h)
      · exact h0 h.symm
      · exact ih h

theorem pmodify_keys (k : K) (f : Principal A → Principal A) (l : List (K × Principal A)) :
    (pmodify k f l).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => simp [pmodify]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k <;> simp [pmodify, h0, ih]

theorem pmodify_length (k : K) (f : Principal A → Principal A) (l : List (K × Principal A)) :
    (pmodify k f l).length = l.length := by
  have := congrArg List.length (pmodify_keys k f l)
  simpa using this

theorem mem_pmodify {k : K} {f : Principal A → Principal A} {l : List (K × Principal A)}
    {e : K × Principal A} (h : e ∈ pmodify k f l) : ∃ e0 ∈ l, e.1 = e0.1 ∧ (e.2 = e0.2 ∨ e.2 = f e0.2) := by
  induction l with
  | nil => simp [pmodify] at h
  | cons e1 l ih =>
    obtain ⟨k0, p0⟩ := e1
    by_cases h0 : k0 = k
    · simp only [pmodify, if_pos h0, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨(k0, p0), by simp, by simp [h], Or.inr (by simp [h])⟩
      · obtain ⟨e0, he0, h1, h2⟩ := ih h
        exact ⟨e0, List.mem_cons_of_mem _ he0, h1, h2⟩
    · simp only [pmodify, if_neg h0, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨(k0, p0), by simp, by simp [h], Or.inl (by simp [h])⟩
      · obtain ⟨e0, he0, h1, h2⟩ := ih h
        exact ⟨e0, List.mem_cons_of_mem _ he0, h1, h2⟩

theorem plookup_none_of_not_mem {k : K} {l : List (K × Principal A)}
    (h : k ∉ l.map Prod.fst) : plookup k l = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [plookup_cons_ne (Ne.symm h.1), ih h.2]

/-- Erasing an absent key changes nothing. -/
theorem perase_of_not_mem {k : K} {l : List (K × Principal A)} (hk : plookup k l = none) :
    perase k l = l := by
  induction l with
  | nil => simp [perase]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · subst h0; simp at hk
    · simp only [plookup_cons, if_neg h0] at hk
      simp only [perase, if_neg h0, ih hk]

/-- With distinct keys, erasing a present key removes exactly one entry. -/
theorem perase_length_of_mem {k : K} {l : List (K × Principal A)} (hnd : (l.map Prod.fst).Nodup)
    (hk : (plookup k l).isSome) : (perase k l).length + 1 = l.length := by
  induction l with
  | nil => simp at hk
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases h0 : k0 = k
    · subst h0
      have : perase k0 l = l := perase_of_not_mem (plookup_none_of_not_mem hnd.1)
      simp [perase, this]
    · simp only [plookup_cons, if_neg h0] at hk
      simp only [perase, if_neg h0, List.length_cons]
      rw [ih hnd.2 hk]

theorem plookup_mem {k : K} {l : List (K × Principal A)} {p : Principal A}
    (h : plookup k l = some p) : (k, p) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · subst h0; simp at h; simp [h]
    · simp only [plookup_cons, if_neg h0] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ## `prin` -/

theorem prin_def (cfg : Cfg A) (s : State A K P) (k : K) :
    prin cfg s k = (plookup k s.principals).getD (noPrincipal cfg) := rfl

/-- Under `TypeOK`, a key is registered exactly when it is in the map. -/
theorem reg_iff_some (cfg : Cfg A) {s : State A K P} (hT : TypeOK s) (k : K) :
    (prin cfg s k).reg = true ↔ ∃ p, plookup k s.principals = some p := by
  unfold prin
  cases h : plookup k s.principals with
  | none => simp [noPrincipal]
  | some p =>
    simp only [Option.getD_some, Option.some.injEq, exists_eq', iff_true]
    exact hT.preg _ (plookup_mem h)

theorem prin_of_reg (cfg : Cfg A) {s : State A K P} {k : K} (hT : TypeOK s)
    (h : (prin cfg s k).reg = true) : plookup k s.principals = some (prin cfg s k) := by
  obtain ⟨p, hp⟩ := (reg_iff_some cfg hT k).1 h
  simp [prin, hp]

theorem prin_of_not_reg (cfg : Cfg A) {s : State A K P} {k : K} (hT : TypeOK s)
    (h : (prin cfg s k).reg = false) : prin cfg s k = noPrincipal cfg ∧
      plookup k s.principals = none := by
  unfold prin at *
  cases hp : plookup k s.principals with
  | none => simp
  | some p =>
    rw [hp] at h
    simp only [Option.getD_some] at h
    have := hT.preg _ (plookup_mem hp)
    simp_all

/-! ## `countIdx` -/

theorem countIdx_append (f : Nat → R → Bool) (l : List R) (x : R) (n : Nat) :
    countIdx f (l ++ [x]) n = countIdx f l n + (if f (n + l.length) x then 1 else 0) := by
  induction l generalizing n with
  | nil => simp [countIdx]
  | cons r l ih =>
    simp only [List.cons_append, countIdx, ih, List.length_cons]
    have : n + 1 + l.length = n + (l.length + 1) := by omega
    rw [this]; omega

theorem countIdx_congr (f g : Nat → R → Bool) (l : List R) (n : Nat)
    (h : ∀ j (hj : j < l.length), f (n + j) l[j] = g (n + j) l[j]) :
    countIdx f l n = countIdx g l n := by
  induction l generalizing n with
  | nil => simp [countIdx]
  | cons r l ih =>
    simp only [countIdx]
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0, ih (n + 1)]
    intro j hj
    have := h (j + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    rw [show n + 1 + j = n + (j + 1) by omega]; exact this

theorem countIdx_set (f : Nat → R → Bool) (l : List R) (n i : Nat) (x : R) (hi : i < l.length) :
    countIdx f (l.set i x) n + (if f (n + i) l[i] then 1 else 0) =
      countIdx f l n + (if f (n + i) x then 1 else 0) := by
  induction l generalizing n i with
  | nil => simp at hi
  | cons r l ih =>
    cases i with
    | zero => simp [countIdx]; omega
    | succ i =>
      simp only [List.set_cons_succ, countIdx, List.getElem_cons_succ]
      have := ih (n + 1) i (by simpa using hi)
      rw [show n + 1 + i = n + (i + 1) by omega] at this
      omega

theorem countIdx_eq_zero (f : Nat → R → Bool) (l : List R) (n : Nat)
    (h : ∀ j (hj : j < l.length), f (n + j) l[j] = false) : countIdx f l n = 0 := by
  rw [countIdx_congr f (fun _ _ => false) l n (by simpa using h)]
  clear h
  induction l generalizing n with
  | nil => rfl
  | cons r l ih => simp [countIdx, ih]

/-! ## Requests -/

theorem req_append (s : State A K P) (l : List (Request A K P)) (i : Nat) :
    (s.requests ++ l)[i]? = if i < s.nr then s.req i else l[i - s.nr]? := by
  simp only [State.req, State.nr]
  by_cases h : i < s.requests.length
  · simp [h, List.getElem?_append_left h]
  · simp [h, List.getElem?_append_right (Nat.le_of_not_lt h)]

theorem req_eq_some {s : State A K P} {i : Nat} {r : Request A K P} (h : s.req i = some r) :
    ∃ hi : i < s.nr, s.requests[i] = r := by
  simp only [State.req, List.getElem?_eq_some_iff] at h
  exact ⟨h.1, h.2⟩

theorem req_lt {s : State A K P} {i : Nat} {r : Request A K P} (h : s.req i = some r) :
    i < s.nr := (req_eq_some h).1

/-! ## Each action's effect, field by field -/

section Effects
variable (cfg : Cfg A) (s : State A K P)

@[simp] theorem add_principals (c k a r) : (effect cfg s (.add c k a r)).principals =
    (k, { reg := true, acct := a, role := r, rid := s.regs, activeFrom := s.nr, pending := 0 })
      :: perase k s.principals := rfl
@[simp] theorem add_requests (c k a r) : (effect cfg s (.add c k a r)).requests = s.requests := rfl
@[simp] theorem add_log (c k a r) : (effect cfg s (.add c k a r)).log = s.log := rfl
@[simp] theorem add_regs (c k a r) : (effect cfg s (.add c k a r)).regs = s.regs + 1 := rfl
@[simp] theorem add_revoked (c k a r) : (effect cfg s (.add c k a r)).revoked = s.revoked := rfl
@[simp] theorem add_ghost (c k a r) : (effect cfg s (.add c k a r)).ghost = s.ghost := rfl

@[simp] theorem revoke_principals (c k) : (effect cfg s (.revoke c k)).principals =
    perase k s.principals := rfl
@[simp] theorem revoke_requests (c k) : (effect cfg s (.revoke c k)).requests = s.requests := rfl
@[simp] theorem revoke_log (c k) : (effect cfg s (.revoke c k)).log = s.log := rfl
@[simp] theorem revoke_regs (c k) : (effect cfg s (.revoke c k)).regs = s.regs := rfl
@[simp] theorem revoke_revoked (c k) : (effect cfg s (.revoke c k)).revoked =
    setInsert (prin cfg s k).rid s.revoked := rfl
@[simp] theorem revoke_ghost (c k) : (effect cfg s (.revoke c k)).ghost = s.ghost := rfl

end Effects

theorem prin_add (cfg : Cfg A) (s : State A K P) (c k a r k') :
    prin cfg (effect cfg s (.add c k a r)) k' =
      if k' = k then { reg := true, acct := a, role := r, rid := s.regs, activeFrom := s.nr,
                       pending := 0 }
      else prin cfg s k' := by
  simp only [prin, add_principals, plookup_cons, plookup_perase]
  by_cases h : k' = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem prin_revoke (cfg : Cfg A) (s : State A K P) (c k k') :
    prin cfg (effect cfg s (.revoke c k)) k' = if k' = k then noPrincipal cfg else prin cfg s k' := by
  simp only [prin, revoke_principals, plookup_perase]
  by_cases h : k' = k <;> simp [h]

theorem mem_setInsert (g x : Nat) (l : List Nat) : x ∈ setInsert g l ↔ x = g ∨ x ∈ l := by
  unfold setInsert; split <;> simp_all <;> grind

theorem setInsert_nodup {g : Nat} {l : List Nat} (h : l.Nodup) : (setInsert g l).Nodup := by
  unfold setInsert; split
  · exact h
  · exact List.nodup_cons.2 ⟨by assumption, h⟩

theorem setInsert_length_of_not_mem {g : Nat} {l : List Nat} (h : g ∉ l) :
    (setInsert g l).length = l.length + 1 := by
  simp [setInsert, h]

end Approval
