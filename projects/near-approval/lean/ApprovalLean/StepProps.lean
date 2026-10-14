/-
LEAN-STEP: every step from an `Inv` state satisfies `StepProps`
(HIST-1/2/3/7/8/10), for states of every size.
-/
import ApprovalLean.Lemmas

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## Frame lemmas: a field the step leaves alone -/

private theorem hist1_same {s s' : State A K P} (h : s'.requests = s.requests) : Hist1 s s' :=
  ⟨by simp [State.nr, h], fun _ r hr => ⟨r, by simpa [State.req, h] using hr, rfl, rfl, rfl⟩⟩

private theorem hist2_same {s s' : State A K P} (h : s'.requests = s.requests) : Hist2 s s' := by
  intro i r hr _
  simpa [State.req, h] using hr

private theorem hist3_same {s s' : State A K P} (h : s'.log = s.log) : Hist3 s s' :=
  ⟨by simp [State.nl, h], by simp [State.nl, h]⟩

private theorem hist7_same {cfg : Cfg A} {s s' : State A K P} (h : s'.log = s.log) :
    Hist7 cfg s s' :=
  fun _ => h

private theorem hist10_same {cfg : Cfg A} {s s' : State A K P} (h1 : s'.regs = s.regs)
    (h2 : s'.revoked = s.revoked) : Hist10 cfg s s' :=
  ⟨by simp [h1], by simp [h2], fun g hg hn => absurd (h2 ▸ hg) hn⟩

private theorem hist8_of {cfg : Cfg A} {s s' : State A K P}
    (h : ∀ i r, s.req i = some r → r.decided = false → liveR cfg s i r = false →
      s'.req i = some r ∧ liveR cfg s' i r = false) : Hist8 cfg s s' := by
  rintro i ⟨r, hr, hd, hl⟩
  obtain ⟨h1, h2⟩ := h i r hr hd hl
  exact ⟨r, h1, hd, h2⟩

/-- A stutter satisfies every step property. -/
theorem stepProps_refl (cfg : Cfg A) (s : State A K P) : StepProps cfg s s :=
  ⟨hist1_same rfl, hist2_same rfl, hist3_same rfl, hist7_same rfl,
   hist8_of (fun _ _ hr _ hl => ⟨hr, hl⟩), hist10_same rfl rfl⟩

/-! ## `liveR` under each change of the principal map -/

/-- Changing only a field other than `reg`, `role`, `acct`, `activeFrom` of
one entry leaves those fields of every `prin` alone. -/
private theorem prin_pmodify_fields (cfg : Cfg A) {s s' : State A K P} (k : K)
    (f : Principal A → Principal A)
    (hf : ∀ p, (f p).reg = p.reg ∧ (f p).role = p.role ∧ (f p).acct = p.acct ∧
      (f p).activeFrom = p.activeFrom)
    (hs : s'.principals = pmodify k f s.principals) (k' : K) :
    (prin cfg s' k').reg = (prin cfg s k').reg ∧ (prin cfg s' k').role = (prin cfg s k').role ∧
      (prin cfg s' k').acct = (prin cfg s k').acct ∧
      (prin cfg s' k').activeFrom = (prin cfg s k').activeFrom := by
  simp only [prin]
  rw [hs, plookup_pmodify]
  by_cases h : k' = k
  · rw [ite_eq_left h, h]
    cases plookup k s.principals with
    | none => exact ⟨rfl, rfl, rfl, rfl⟩
    | some p => exact hf p
  · rw [ite_eq_right h]; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem liveR_pmodify (cfg : Cfg A) {s s' : State A K P} (k : K)
    (f : Principal A → Principal A)
    (hf : ∀ p, (f p).reg = p.reg ∧ (f p).role = p.role ∧ (f p).acct = p.acct ∧
      (f p).activeFrom = p.activeFrom)
    (hs : s'.principals = pmodify k f s.principals) (i : Nat) (r : Request A K P) :
    liveR cfg s' i r = liveR cfg s i r := by
  obtain ⟨h1, h2, h3, h4⟩ := prin_pmodify_fields cfg k f hf hs r.key
  simp only [liveR, h1, h2, h3, h4]

private theorem liveR_add (cfg : Cfg A) (s : State A K P) (c : A) (k : K) (a : A) (ro : Role)
    (i : Nat) (r : Request A K P) (hi : i < s.nr) :
    liveR cfg (effect cfg s (.add c k a ro)) i r = if r.key = k then false else liveR cfg s i r := by
  simp only [liveR]
  rw [prin_add]
  by_cases h : r.key = k
  · simp only [ite_eq_left h]
    have : ¬ s.nr ≤ i := by omega
    simp [this]
  · simp only [ite_eq_right h]

private theorem liveR_revoke (cfg : Cfg A) (s : State A K P) (c : A) (k : K)
    (i : Nat) (r : Request A K P) :
    liveR cfg (effect cfg s (.revoke c k)) i r = if r.key = k then false else liveR cfg s i r := by
  simp only [liveR]
  rw [prin_revoke]
  by_cases h : r.key = k
  · simp [h, noPrincipal]
  · simp only [ite_eq_right h]

/-! ## Requests rewritten at one index -/

private theorem req_set_self {s s' : State A K P} {i : Nat} {r r' : Request A K P}
    (hs : s'.requests = s.requests.set i r') (hr : s.req i = some r) : s'.req i = some r' := by
  simp only [State.req, hs]
  exact List.getElem?_set_self (req_lt hr)

private theorem req_set_ne {s s' : State A K P} {i j : Nat} {r' : Request A K P}
    (hs : s'.requests = s.requests.set i r') (hj : j ≠ i) : s'.req j = s.req j := by
  simp only [State.req, hs]
  exact List.getElem?_set_ne (Ne.symm hj)

private theorem hist1_set {s s' : State A K P} {i : Nat} {r r' : Request A K P}
    (hs : s'.requests = s.requests.set i r') (hr : s.req i = some r)
    (h1 : r'.acct = r.acct) (h2 : r'.key = r.key) (h3 : r'.act = r.act) : Hist1 s s' := by
  refine ⟨by simp [State.nr, hs], ?_⟩
  intro j r0 hr0
  by_cases hj : j = i
  · subst hj
    obtain rfl : r = r0 := Option.some.inj (hr.symm.trans hr0)
    exact ⟨r', req_set_self hs hr, h1, h2, h3⟩
  · exact ⟨r0, by rw [req_set_ne hs hj]; exact hr0, rfl, rfl, rfl⟩

private theorem hist2_set {s s' : State A K P} {i : Nat} {r r' : Request A K P}
    (hs : s'.requests = s.requests.set i r') (hr : s.req i = some r)
    (hd : r.decided = false) : Hist2 s s' := by
  intro j r0 hr0 hd0
  by_cases hj : j = i
  · subst hj
    obtain rfl : r = r0 := Option.some.inj (hr.symm.trans hr0)
    rw [hd] at hd0; cases hd0
  · rw [req_set_ne hs hj]; exact hr0

private theorem hist8_set {cfg : Cfg A} {s s' : State A K P} {i : Nat} {r r' : Request A K P}
    (hs : s'.requests = s.requests.set i r') (hr : s.req i = some r)
    (hl : liveR cfg s i r = true) (hlive : ∀ j r0, liveR cfg s' j r0 = liveR cfg s j r0) :
    Hist8 cfg s s' := by
  refine hist8_of (fun j r0 hr0 _ hl0 => ?_)
  have hj : j ≠ i := by
    rintro rfl
    obtain rfl : r = r0 := Option.some.inj (hr.symm.trans hr0)
    rw [hl] at hl0; cases hl0
  exact ⟨by rw [req_set_ne hs hj]; exact hr0, by rw [hlive]; exact hl0⟩

/-- A decision changes the record at its index, so the request list changes. -/
private theorem requests_set_ne {s s' : State A K P} {i : Nat} {r r' : Request A K P}
    (hs : s'.requests = s.requests.set i r') (hr : s.req i = some r) (hne : r' ≠ r) :
    s'.requests ≠ s.requests := by
  intro h
  have h1 := req_set_self hs hr
  simp only [State.req, h] at h1
  simp only [State.req] at hr
  rw [hr] at h1
  exact hne (Option.some.inj h1).symm

/-! ## Error operators -/

private theorem decideErr_ok {cfg : Cfg A} {s : State A K P} {i : Nat}
    (h : decideErr cfg s i = .ok) :
    ∃ r, s.req i = some r ∧ r.appr = false ∧ r.rj = false ∧ liveR cfg s i r = true := by
  unfold decideErr at h
  split at h
  · cases h
  · rename_i r hr
    refine ⟨r, hr, ?_⟩
    cases ha : r.appr <;> cases hj : r.rj <;> cases hl : liveR cfg s i r <;> simp_all

private theorem approveErr_dec {cfg : Cfg A} {s : State A K P} {pred signer : A} {k : K}
    {i : Nat} {x : Action P} (h : approveErr cfg s pred signer k i x = .ok) :
    decideErr cfg s i = .ok := by
  unfold approveErr at h
  by_cases ha : authErr cfg s pred signer k .approver = .ok
  · by_cases hd : decideErr cfg s i = .ok
    · exact hd
    · simp [ha, hd] at h
  · simp [ha] at h

private theorem rejectErr_dec {cfg : Cfg A} {s : State A K P} {pred signer : A} {k : K}
    {i : Nat} (h : rejectErr cfg s pred signer k i = .ok) :
    decideErr cfg s i = .ok := by
  unfold rejectErr at h
  by_cases ha : authErr cfg s pred signer k .approver = .ok
  · by_cases hd : decideErr cfg s i = .ok
    · exact hd
    · simp [ha, hd] at h
  · simp [ha] at h

private theorem revokeErr_reg {cfg : Cfg A} {s : State A K P} {c : A} {k : K}
    (h : revokeErr cfg s c k = .ok) : (prin cfg s k).reg = true := by
  unfold revokeErr at h
  by_cases hc : c = cfg.owner <;> cases hk : (prin cfg s k).reg <;> simp_all

/-! ## Each action -/

private theorem sp_add (cfg : Cfg A) (s : State A K P) (c : A) (k : K) (a : A) (ro : Role) :
    StepProps cfg s (effect cfg s (.add c k a ro)) := by
  refine ⟨hist1_same (add_requests ..), hist2_same (add_requests ..),
    hist3_same (add_log ..), hist7_same (add_log ..), ?_, ?_⟩
  · refine hist8_of (fun i r hr _ hl => ⟨by simpa [State.req] using hr, ?_⟩)
    rw [liveR_add cfg s c k a ro i r (req_lt hr), hl]
    simp
  · exact ⟨by simp, by simp, fun g hg hn => absurd (by simpa using hg) hn⟩

private theorem sp_revoke (cfg : Cfg A) (s : State A K P) (c : A) (k : K)
    (hE : revokeErr cfg s c k = .ok) :
    StepProps cfg s (effect cfg s (.revoke c k)) := by
  refine ⟨hist1_same (revoke_requests ..), hist2_same (revoke_requests ..),
    hist3_same (revoke_log ..), hist7_same (revoke_log ..), ?_, ?_⟩
  · refine hist8_of (fun i r hr _ hl => ⟨by simpa [State.req] using hr, ?_⟩)
    rw [liveR_revoke cfg s c k i r, hl]
    simp
  · refine ⟨by simp, fun g hg => by simp [mem_setInsert, hg], fun g hg hn => ?_⟩
    simp only [revoke_revoked, mem_setInsert] at hg
    rcases hg with hg | hg
    · exact ⟨k, revokeErr_reg hE, hg.symm⟩
    · exact absurd hg hn

private theorem sp_request (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K)
    (x : Action P) : StepProps cfg s (effect cfg s (.request pred signer k x)) := by
  generalize hs' : effect cfg s (.request pred signer k x) = s'
  have hreq : s'.requests = s.requests ++
      [{ acct := signer, key := k, rid := (prin cfg s k).rid, act := x,
         appr := false, aidx := 0, aacct := signer, akey := k, arid := 0,
         rj := false, racct := signer, rkey := k, rrid := 0 }] := by
    rw [← hs']; rfl
  have hlog : s'.log = s.log := by rw [← hs']; rfl
  have hregs : s'.regs = s.regs := by rw [← hs']; rfl
  have hrev : s'.revoked = s.revoked := by rw [← hs']; rfl
  have hprin : s'.principals =
      pmodify k (fun p => { p with pending := p.pending + 1 }) s.principals := by
    rw [← hs']; rfl
  have hold : ∀ i r, s.req i = some r → s'.req i = some r := by
    intro i r hr
    simp only [State.req, hreq]
    rw [req_append, ite_eq_left (req_lt hr)]
    exact hr
  have hlive := liveR_pmodify cfg k (fun p => { p with pending := p.pending + 1 })
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) hprin
  refine ⟨⟨by simp [State.nr, hreq], fun i r hr => ⟨r, hold i r hr, rfl, rfl, rfl⟩⟩,
    fun i r hr _ => hold i r hr, hist3_same hlog, hist7_same hlog, ?_, hist10_same hregs hrev⟩
  exact hist8_of (fun i r hr _ hl => ⟨hold i r hr, by rw [hlive]; exact hl⟩)

private theorem sp_approve (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K) (i : Nat)
    (x : Action P) (hE : approveErr cfg s pred signer k i x = .ok) :
    StepProps cfg s (effect cfg s (.approve pred signer k i x)) := by
  obtain ⟨r, hr, ha, hj, hl⟩ := decideErr_ok (approveErr_dec hE)
  generalize hs' : effect cfg s (.approve pred signer k i x) = s'
  have hreq : s'.requests = s.requests.set i
      { r with appr := true, aidx := s.nl, aacct := signer, akey := k,
               arid := (prin cfg s k).rid } := by
    rw [← hs']; simp [effect, hr]
  have hlog : s'.log = s.log ++ [i] := by rw [← hs']; simp [effect, hr]
  have hregs : s'.regs = s.regs := by rw [← hs']; simp [effect, hr]
  have hrev : s'.revoked = s.revoked := by rw [← hs']; simp [effect, hr]
  have hprin : s'.principals =
      pmodify r.key (fun p => { p with pending := p.pending - 1 }) s.principals := by
    rw [← hs']; simp [effect, hr, decidePrincipals]
  have hd : r.decided = false := by simp [Request.decided, ha, hj]
  have hlive := liveR_pmodify cfg r.key (fun p => { p with pending := p.pending - 1 })
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) hprin
  refine ⟨hist1_set hreq hr rfl rfl rfl, hist2_set hreq hr hd,
    ⟨by simp [State.nl, hlog], by simp [State.nl, hlog]⟩, ?_,
    hist8_set hreq hr hl hlive, hist10_same hregs hrev⟩
  rintro ⟨_, hrq⟩
  refine absurd hrq (requests_set_ne hreq hr ?_)
  intro h
  have := congrArg Request.appr h
  simp [ha] at this

private theorem sp_reject (cfg : Cfg A) (s : State A K P) (pred signer : A) (k : K) (i : Nat)
    (hE : rejectErr cfg s pred signer k i = .ok) :
    StepProps cfg s (effect cfg s (.reject pred signer k i)) := by
  obtain ⟨r, hr, ha, hj, hl⟩ := decideErr_ok (rejectErr_dec hE)
  generalize hs' : effect cfg s (.reject pred signer k i) = s'
  have hreq : s'.requests = s.requests.set i
      { r with rj := true, racct := signer, rkey := k, rrid := (prin cfg s k).rid } := by
    rw [← hs']; simp [effect, hr]
  have hlog : s'.log = s.log := by rw [← hs']; simp [effect, hr]
  have hregs : s'.regs = s.regs := by rw [← hs']; simp [effect, hr]
  have hrev : s'.revoked = s.revoked := by rw [← hs']; simp [effect, hr]
  have hprin : s'.principals =
      pmodify r.key (fun p => { p with pending := p.pending - 1 }) s.principals := by
    rw [← hs']; simp [effect, hr, decidePrincipals]
  have hd : r.decided = false := by simp [Request.decided, ha, hj]
  have hlive := liveR_pmodify cfg r.key (fun p => { p with pending := p.pending - 1 })
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) hprin
  exact ⟨hist1_set hreq hr rfl rfl rfl, hist2_set hreq hr hd, hist3_same hlog, hist7_same hlog,
    hist8_set hreq hr hl hlive, hist10_same hregs hrev⟩

/-- `Inv /\ Next => StepProps`. -/
theorem stepProps_next {cfg : Cfg A} {s s' : State A K P} (hI : Inv cfg s)
    (hN : Next cfg s s') : StepProps cfg s s' := by
  -- The step properties follow from the guards alone; no invariant is needed.
  have _ := hI
  obtain ⟨op, hE, rfl⟩ := hN
  cases op with
  | add c k a ro => exact sp_add cfg s c k a ro
  | revoke c k => exact sp_revoke cfg s c k hE
  | request pred signer k x => exact sp_request cfg s pred signer k x
  | approve pred signer k i x => exact sp_approve cfg s pred signer k i x hE
  | reject pred signer k i => exact sp_reject cfg s pred signer k i hE

/-- A rejected call is a stutter, so `StepProps` holds for every call. -/
theorem stepProps_step {cfg : Cfg A} {s : State A K P} (hI : Inv cfg s) (op : Op A K P) :
    StepProps cfg s (step cfg s op) := by
  unfold step
  by_cases hE : err cfg s op = .ok
  · rw [ite_eq_left hE]
    exact stepProps_next hI ⟨op, hE, rfl⟩
  · rw [ite_eq_right hE]
    exact stepProps_refl cfg s

end Approval
