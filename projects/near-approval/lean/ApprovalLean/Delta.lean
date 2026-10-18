/-
LEAN-DELTA (strategy.md section 18.6, l2-oracle-proposal.md): the local
specification `ghost::expect` / `ghost::protocol` of the Kani crate refines
the model's step, at every state size.

`cstep` transcribes `expect` (the error) and `protocol` (the mutating
`Store` calls) line by line. It reads the store only through `Rd`, the
getters `Store` offers, so LINK (`approval-lean link`, kani/src/link.rs)
can run it on exactly the footprint view the Rust side sees and compare.

`CStore` is the contract's store as the core sees it: a map of principals
(no `reg` flag: absent means unregistered), requests at their positions,
the approval log, the registration counter and the set of revoked
registrations. Counters are the sequence lengths (the ST-1 store laws).
`applyCalls` runs `cstep`'s calls on it.

`delta_refines`: for every store of any size whose request ids equal their
positions (INV-1) and whose counters are below `u64::MAX` (A6), `cstep`'s
error is the model's `err` on `α s`, and running its calls lands on the
model's `step`, up to map equality of principals and set equality of
revocations. With ST-8 (the core makes exactly `expect`'s result and
`protocol`'s calls at every store size) and LINK, the code steps like the
model on every state. Block times are not modelled (A7).
-/
import ApprovalLean.Lemmas

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## The store as the core sees it -/

/-- `Principal<A>`: a registered key's record. -/
structure CPrin (A : Type) where
  acct : A
  role : Role
  rid : Nat
  activeFrom : Nat
  pending : Nat
  deriving DecidableEq, Repr

/-- `Approval` / `Rejection` without the time (`idx` is the approval index;
0 for rejections). -/
structure CDec (A K : Type) where
  idx : Nat
  acct : A
  key : K
  rid : Nat
  deriving DecidableEq, Repr

/-- `ActionRequest<A, K>` without `requested_at`. -/
structure CReq (A K P : Type) where
  id : Nat
  acct : A
  key : K
  rid : Nat
  act : Action P
  appr : Option (CDec A K)
  rej : Option (CDec A K)
  deriving DecidableEq, Repr

structure CStore (A K P : Type) where
  owner : A
  principals : List (K × CPrin A)
  requests : List (CReq A K P)
  log : List Nat
  regs : Nat
  revs : List Nat

/-- `u64::MAX`. -/
def maxU : Nat := 2 ^ 64 - 1

def clookup (k : K) : List (K × CPrin A) → Option (CPrin A)
  | [] => none
  | (k', p) :: l => if k' = k then some p else clookup k l

def cerase (k : K) : List (K × CPrin A) → List (K × CPrin A)
  | [] => []
  | (k', p) :: l => if k' = k then cerase k l else (k', p) :: cerase k l

/-- One mutating `Store` call (`ghost::Call`). -/
inductive Call (A K P : Type) where
  | incG
  | insP (k : K) (p : CPrin A)
  | rmP (k : K)
  | pushR (r : CReq A K P)
  | replR (r : CReq A K P)
  | pushA (i : Nat)
  | insRev (g : Nat)

/-- The `Store` contract: maps insert/overwrite and remove, sequences append
and replace at `id`. -/
def applyCall (s : CStore A K P) : Call A K P → CStore A K P
  | .incG => { s with regs := s.regs + 1 }
  | .insP k p => { s with principals := (k, p) :: cerase k s.principals }
  | .rmP k => { s with principals := cerase k s.principals }
  | .pushR r => { s with requests := s.requests ++ [r] }
  | .replR r => { s with requests := s.requests.set r.id r }
  | .pushA i => { s with log := s.log ++ [i] }
  | .insRev g => { s with revs := g :: s.revs }

def applyCalls (s : CStore A K P) (cs : List (Call A K P)) : CStore A K P :=
  cs.foldl applyCall s

/-- What `expect` and `protocol` read: `Store`'s getters. -/
structure Rd (A K P : Type) where
  owner : A
  prin : K → Option (CPrin A)
  req : Nat → Option (CReq A K P)
  nr : Nat
  nl : Nat
  regs : Nat

/-- The getters of a concrete store. -/
def CStore.rd (s : CStore A K P) : Rd A K P :=
  { owner := s.owner, prin := fun k => clookup k s.principals, req := fun i => s.requests[i]?,
    nr := s.requests.length, nl := s.log.length, regs := s.regs }

/-! ## `expect` and `protocol`, transcribed -/

/-- `auth`: the first failing authentication guard, or the signer's record. -/
def cauth (s : Rd A K P) (pred signer : A) (k : K) (role : Role) :
    Except Err (CPrin A) :=
  if pred ≠ signer then .error .indirectCall
  else match s.prin k with
    | none => .error .unknownKey
    | some p =>
      if p.role ≠ role then .error .wrongRole
      else if p.acct ≠ signer then .error .keyAccountMismatch
      else .ok p

/-- `decidable`: the request and its live agent registration. -/
def cdecidable (s : Rd A K P) (i : Nat) : Except Err (CReq A K P × CPrin A) :=
  match s.req i with
  | none => .error .requestNotFound
  | some r =>
    if r.appr.isSome then .error .alreadyApproved
    else if r.rej.isSome then .error .alreadyRejected
    else match s.prin r.key with
      | some p =>
        if p.role = .agent ∧ p.acct = r.acct ∧ p.activeFrom ≤ r.id then .ok (r, p)
        else .error .agentRevoked
      | none => .error .agentRevoked

/-- `expect` (the error) and `protocol` (the calls) of one operation. -/
def cstep (cfg : Cfg A) (s : Rd A K P) : Op A K P → Err × List (Call A K P)
  | .add c k a r =>
    if c ≠ s.owner then (.notOwner, [])
    else if (s.prin k).isSome then (.keyAlreadyRegistered, [])
    else if s.regs = maxU then (.logFull, [])
    else (.ok, [.incG, .insP k { acct := a, role := r, rid := s.regs,
                                  activeFrom := s.nr, pending := 0 }])
  | .revoke c k =>
    if c ≠ s.owner then (.notOwner, [])
    else match s.prin k with
      -- F-6: `remove_principal` runs before the absence is known.
      | none => (.keyNotRegistered, [.rmP k])
      | some p => (.ok, [.rmP k, .insRev p.rid])
  | .request pred signer k x =>
    match cauth s pred signer k .agent with
    | .error e => (e, [])
    | .ok p =>
      if x = .empty then (.emptyAction, [])
      else if x = .tooLong then (.actionTooLong, [])
      else if p.pending ≥ cfg.maxPending then (.tooManyPending, [])
      else if s.nr = maxU then (.logFull, [])
      else (.ok, [.insP k { p with pending := p.pending + 1 },
                  .pushR { id := s.nr, acct := signer, key := k, rid := p.rid,
                           act := x, appr := none, rej := none }])
  | .approve pred signer k i x =>
    match cauth s pred signer k .approver with
    | .error e => (e, [])
    | .ok b =>
      match cdecidable s i with
      | .error e => (e, [])
      | .ok (r, ag) =>
        if r.act ≠ x then (.actionMismatch, [])
        else if signer = r.acct then (.selfApproval, [])
        else if s.nl = maxU then (.logFull, [])
        else (.ok, [.insP r.key { ag with pending := ag.pending - 1 },
                    .replR { r with appr := some { idx := s.nl, acct := signer,
                                                   key := k, rid := b.rid } },
                    .pushA i])
  | .reject pred signer k i =>
    match cauth s pred signer k .approver with
    | .error e => (e, [])
    | .ok b =>
      match cdecidable s i with
      | .error e => (e, [])
      | .ok (r, ag) =>
        if signer = r.acct then (.selfApproval, [])
        else (.ok, [.insP r.key { ag with pending := ag.pending - 1 },
                    .replR { r with rej := some { idx := 0, acct := signer, key := k,
                                                  rid := b.rid } }])

/-! ## Abstraction to the model -/

def toP (p : CPrin A) : Principal A :=
  { reg := true, acct := p.acct, role := p.role, rid := p.rid,
    activeFrom := p.activeFrom, pending := p.pending }

/-- Unset decision fields take the defaults `TypeOK` fixes. -/
def toR (r : CReq A K P) : Request A K P :=
  { acct := r.acct, key := r.key, rid := r.rid, act := r.act,
    appr := r.appr.isSome,
    aidx := (r.appr.map (·.idx)).getD 0,
    aacct := (r.appr.map (·.acct)).getD r.acct,
    akey := (r.appr.map (·.key)).getD r.key,
    arid := (r.appr.map (·.rid)).getD 0,
    rj := r.rej.isSome,
    racct := (r.rej.map (·.acct)).getD r.acct,
    rkey := (r.rej.map (·.key)).getD r.key,
    rrid := (r.rej.map (·.rid)).getD 0 }

def αP (l : List (K × CPrin A)) : List (K × Principal A) := l.map (fun e => (e.1, toP e.2))

/-- `α`, with the model's ghost passed through (the store has none). -/
def α (s : CStore A K P) (g : List Ghost) : State A K P :=
  { principals := αP s.principals, requests := s.requests.map toR, log := s.log,
    regs := s.regs, revoked := s.revs, ghost := g }

/-- Equal as abstract states, ghost aside: principals as maps, revocations
as sets. -/
def Same (x y : State A K P) : Prop :=
  (∀ k, plookup k x.principals = plookup k y.principals) ∧ x.requests = y.requests ∧
  x.log = y.log ∧ x.regs = y.regs ∧ (∀ g, g ∈ x.revoked ↔ g ∈ y.revoked)

/-- INV-1 for the store, and A6: no counter at `u64::MAX`. -/
structure WF (s : CStore A K P) : Prop where
  ids : ∀ i (r : CReq A K P), s.requests[i]? = some r → r.id = i
  regs : s.regs < maxU
  nr : s.requests.length < maxU
  nl : s.log.length < maxU

/-! ## Lemmas -/

theorem plookup_αP (k : K) (l : List (K × CPrin A)) :
    plookup k (αP l) = (clookup k l).map toP := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h : k0 = k <;> simp [αP, plookup, clookup, h] at ih ⊢ <;> exact ih

theorem αP_cerase (k : K) (l : List (K × CPrin A)) : αP (cerase k l) = perase k (αP l) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h : k0 = k <;> simp [αP, cerase, perase, h] at ih ⊢ <;> exact ih

theorem prin_α (cfg : Cfg A) (s : CStore A K P) (g : List Ghost) (k : K) :
    prin cfg (α s g) k = ((clookup k s.principals).map toP).getD (noPrincipal cfg) := by
  simp [prin, α, plookup_αP]

theorem req_α (s : CStore A K P) (g : List Ghost) (i : Nat) :
    (α s g).req i = (s.requests[i]?).map toR := by
  simp [State.req, α]

/-- Inserting over a present key equals modifying it in place, as maps. -/
theorem plookup_insert_eq_pmodify (k k' : K) (l : List (K × Principal A))
    (f : Principal A → Principal A) (p : Principal A) (hp : plookup k l = some p) :
    plookup k' ((k, f p) :: perase k l) = plookup k' (pmodify k f l) := by
  rw [plookup_pmodify]
  by_cases h : k' = k
  · subst h; simp [hp]
  · rw [plookup_cons_ne (Ne.symm h), plookup_perase]; simp [h]


theorem clookup_cerase (k k' : K) (l : List (K × CPrin A)) :
    clookup k' (cerase k l) = if k' = k then none else clookup k' l := by
  induction l with
  | nil => simp [cerase, clookup]
  | cons e l ih =>
    obtain ⟨k0, p0⟩ := e
    by_cases h0 : k0 = k
    · subst h0
      by_cases h1 : k' = k0
      · subst h1; simp [cerase, ih]
      · simp [cerase, clookup, h1, Ne.symm h1, ih]
    · by_cases h1 : k' = k0
      · subst h1; simp [cerase, clookup, h0]
      · simp [cerase, clookup, h0, Ne.symm h1, ih]

/-- Authentication: `cauth` fails exactly with `AuthErr`, and succeeds with
the signer's record. -/
theorem authErr_α (cfg : Cfg A) (s : CStore A K P) (g : List Ghost) (pred signer : A) (k : K)
    (role : Role) :
    authErr cfg (α s g) pred signer k role =
      match cauth s.rd pred signer k role with
      | .ok _ => .ok
      | .error e => e := by
  unfold authErr cauth CStore.rd
  dsimp only
  rw [prin_α]
  by_cases h1 : pred = signer
  · cases h : clookup k s.principals with
    | none => simp [h1, noPrincipal]
    | some p =>
      by_cases h2 : p.role = role <;> by_cases h3 : p.acct = signer <;> simp [h1, h2, h3, toP]
  · simp [h1]

theorem cauth_err_ne_ok {s : CStore A K P} {pred signer : A} {k : K} {role : Role} {e : Err}
    (h : cauth s.rd pred signer k role = .error e) : e ≠ .ok := by
  unfold cauth CStore.rd at h
  dsimp only at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · split at h
        · cases h; decide
        · cases h

theorem cauth_ok {s : CStore A K P} {pred signer : A} {k : K} {role : Role} {p : CPrin A}
    (h : cauth s.rd pred signer k role = .ok p) :
    clookup k s.principals = some p ∧ p.role = role ∧ p.acct = signer := by
  unfold cauth CStore.rd at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i p' hp
      split at h
      · cases h
      · split at h
        · cases h
        · cases h; simp_all

/-- `decidable` fails exactly with `DecideErr` (given INV-1). -/
theorem decideErr_α (cfg : Cfg A) (s : CStore A K P) (g : List Ghost) (hW : WF s) (i : Nat) :
    decideErr cfg (α s g) i =
      match cdecidable s.rd i with
      | .ok _ => .ok
      | .error e => e := by
  unfold decideErr cdecidable CStore.rd
  dsimp only
  rw [req_α]
  cases hr : s.requests[i]? with
  | none => simp
  | some r =>
    have hid := hW.ids i r hr
    simp only [Option.map_some]
    unfold liveR
    rw [prin_α]
    cases hp : clookup r.key s.principals with
    | none => cases ha : r.appr <;> cases hj : r.rej <;> simp [toR, ha, hj, hp, noPrincipal]
    | some p =>
      cases ha : r.appr <;> cases hj : r.rej <;> simp only [toR, ha, hj, Option.isSome_none,
        Option.isSome_some, hp, Option.map_some, Option.getD_some, toP, hid] <;> try rfl
      by_cases h1 : p.role = .agent <;> by_cases h2 : p.acct = r.acct <;>
        by_cases h3 : p.activeFrom ≤ i <;> simp [h1, h2, h3]

theorem cdecidable_err_ne_ok {s : CStore A K P} {i : Nat} {e : Err}
    (h : cdecidable s.rd i = .error e) : e ≠ .ok := by
  unfold cdecidable CStore.rd at h
  dsimp only at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · split at h
        · split at h
          · cases h
          · cases h; decide
        · cases h; decide

theorem cdecidable_ok {s : CStore A K P} {i : Nat} {r : CReq A K P} {p : CPrin A}
    (h : cdecidable s.rd i = .ok (r, p)) :
    s.requests[i]? = some r ∧ r.appr = none ∧ r.rej = none ∧
      clookup r.key s.principals = some p ∧ p.role = .agent ∧ p.acct = r.acct := by
  unfold cdecidable CStore.rd at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r' hr
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i p' hp
          split at h
          · cases h; simp_all
          · cases h
        · cases h


@[simp] theorem αP_cons (k : K) (p : CPrin A) (l : List (K × CPrin A)) :
    αP ((k, p) :: l) = (k, toP p) :: αP l := rfl

theorem Same.refl (x : State A K P) : Same x x := by
  refine ⟨fun _ => rfl, rfl, rfl, rfl, fun _ => Iff.rfl⟩

theorem Same.ghost {x y : State A K P} (g : List Ghost) (h : Same x y) :
    Same x { y with ghost := g } := h

theorem reg_α (cfg : Cfg A) (s : CStore A K P) (g : List Ghost) (k : K) :
    (prin cfg (α s g) k).reg = (clookup k s.principals).isSome := by
  rw [prin_α]; cases clookup k s.principals <;> rfl

/-! ## The refinement, one operation at a time -/

section Ops
variable (cfg : Cfg A) (s : CStore A K P) (g : List Ghost)

theorem delta_add (hW : WF s) (ho : cfg.owner = s.owner) (c : A) (k : K) (a : A) (r : Role) :
    (cstep cfg s.rd (.add c k a r)).1 = err cfg (α s g) (.add c k a r) ∧
    Same (α (applyCalls s (cstep cfg s.rd (.add c k a r)).2) g) (step cfg (α s g) (.add c k a r)) := by
  have hm : s.regs ≠ maxU := Nat.ne_of_lt hW.regs
  simp only [cstep, CStore.rd, err, addErr, step, reg_α, ← ho]
  by_cases h1 : c = cfg.owner
  · by_cases h2 : (clookup k s.principals).isSome
    · simp [h1, h2, applyCalls]; exact Same.refl _
    · simp only [h1, h2, hm, ne_eq, not_true_eq_false, if_false, Bool.false_eq_true, if_true]
      refine ⟨trivial, ?_⟩
      refine ⟨fun _ => ?_, rfl, rfl, rfl, fun _ => Iff.rfl⟩
      simp only [applyCalls, List.foldl, applyCall, α, effect, αP_cons, αP_cerase, State.nr,
        List.length_map, toP]
  · simp [h1, applyCalls]; exact Same.refl _

theorem delta_revoke (ho : cfg.owner = s.owner) (c : A) (k : K) :
    (cstep cfg s.rd (.revoke c k)).1 = err cfg (α s g) (.revoke c k) ∧
    Same (α (applyCalls s (cstep cfg s.rd (.revoke c k)).2) g) (step cfg (α s g) (.revoke c k)) := by
  simp only [cstep, CStore.rd, err, revokeErr, step, reg_α, ← ho]
  by_cases h1 : c = cfg.owner
  · cases h2 : clookup k s.principals with
    | none =>
      simp only [h1, h2, ne_eq, not_true_eq_false, if_false, Option.isSome_none, Bool.not_false,
        if_true]
      refine ⟨trivial, ?_⟩
      simp only [applyCalls, List.foldl, applyCall]
      refine ⟨fun k' => ?_, rfl, rfl, rfl, fun _ => Iff.rfl⟩
      simp only [α, αP_cerase, plookup_perase, plookup_αP]
      by_cases h : k' = k
      · subst h; simp [h2, plookup_αP]
      · simp [h, plookup_αP]
    | some p =>
      simp only [h1, h2, ne_eq, not_true_eq_false, if_false, Option.isSome_some, Bool.not_true,
        Bool.false_eq_true, if_true]
      refine ⟨trivial, ?_⟩
      simp only [applyCalls, List.foldl, applyCall]
      refine ⟨fun k' => by simp [α, αP_cerase], rfl, rfl, rfl, fun x => ?_⟩
      simp [α, effect, mem_setInsert, prin, plookup_αP, h2, toP]
  · simp [h1, applyCalls]; exact Same.refl _

theorem prin_α_some {k : K} {p : CPrin A} (h : clookup k s.principals = some p) :
    prin cfg (α s g) k = toP p := by
  simp [prin_α, h]

/-- A decision's principal update, as maps: overwrite equals modify. -/
theorem decide_principals_same {k : K} {p : CPrin A} (h : clookup k s.principals = some p)
    (f : Nat → Nat) (k' : K) :
    plookup k' (αP ((k, { p with pending := f p.pending }) :: cerase k s.principals)) =
      plookup k' (pmodify k (fun q => { q with pending := f q.pending }) (αP s.principals)) := by
  rw [αP_cons, αP_cerase]
  have := plookup_insert_eq_pmodify k k' (αP s.principals)
    (fun q => { q with pending := f q.pending }) (toP p) (by simp [plookup_αP, h])
  simpa [toP] using this

theorem delta_request (hW : WF s) (pred signer : A) (k : K) (x : Action P) :
    (cstep cfg s.rd (.request pred signer k x)).1 = err cfg (α s g) (.request pred signer k x) ∧
    Same (α (applyCalls s (cstep cfg s.rd (.request pred signer k x)).2) g)
      (step cfg (α s g) (.request pred signer k x)) := by
  have hm : s.rd.nr ≠ maxU := Nat.ne_of_lt hW.nr
  simp only [cstep, err, requestErr, step]
  simp only [authErr_α]
  cases hc : cauth s.rd pred signer k .agent with
  | error e =>
    have he := cauth_err_ne_ok hc
    simp [he, applyCalls]; exact Same.refl _
  | ok p =>
    obtain ⟨hk, -, hacct⟩ := cauth_ok hc
    rw [prin_α_some cfg s g hk]
    by_cases h1 : x = .empty
    · simp [h1, applyCalls]; exact Same.refl _
    by_cases h2 : x = .tooLong
    · simp [h1, h2, applyCalls]; exact Same.refl _
    by_cases h3 : p.pending ≥ cfg.maxPending
    · simp [h1, h2, h3, toP, applyCalls]; exact Same.refl _
    simp only [h1, h2, h3, hm, ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true,
      toP]
    refine ⟨trivial, fun k' => ?_, ?_, rfl, rfl, fun _ => Iff.rfl⟩
    · simpa [applyCalls, applyCall, α, effect] using
        decide_principals_same s hk (· + 1) k'
    · simp [applyCalls, applyCall, α, effect, toR, prin, plookup_αP, hk, toP]

theorem delta_approve (hW : WF s) (pred signer : A) (k : K) (i : Nat) (x : Action P) :
    (cstep cfg s.rd (.approve pred signer k i x)).1 = err cfg (α s g) (.approve pred signer k i x) ∧
    Same (α (applyCalls s (cstep cfg s.rd (.approve pred signer k i x)).2) g)
      (step cfg (α s g) (.approve pred signer k i x)) := by
  have hm : s.rd.nl ≠ maxU := Nat.ne_of_lt hW.nl
  simp only [cstep, err, approveErr, step]
  simp only [authErr_α, decideErr_α cfg s g hW]
  cases hc : cauth s.rd pred signer k .approver with
  | error e =>
    have he := cauth_err_ne_ok hc
    simp [he, applyCalls]; exact Same.refl _
  | ok b =>
    obtain ⟨hk, -, -⟩ := cauth_ok hc
    cases hd : cdecidable s.rd i with
    | error e =>
      have he := cdecidable_err_ne_ok hd
      simp [he, applyCalls]; exact Same.refl _
    | ok rp =>
      obtain ⟨r, ag⟩ := rp
      obtain ⟨hr, ha, hj, hag, -, -⟩ := cdecidable_ok hd
      have hid := hW.ids i r hr
      have hr' : (α s g).req i = some (toR r) := by simp [req_α, hr]
      have hkey : (toR r).key = r.key := rfl
      simp only [hr', toR]
      by_cases h1 : r.act = x
      · by_cases h2 : signer = r.acct
        · simp [h1, h2, applyCalls]; exact Same.refl _
        simp only [h1, h2, hm, ne_eq, not_true_eq_false, ite_false, ite_true]
        simp only [effect, hr']
        refine ⟨trivial, fun k' => ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;> try simp [applyCalls, applyCall, α, effect, hr']
        · simpa [applyCalls, applyCall, α, effect, hr', hkey, decidePrincipals] using
            decide_principals_same s hag (· - 1) k'
        · simp [applyCalls, applyCall, α, effect, hr', hid, List.map_set, toR, ha, hj, prin,
            plookup_αP, hk, toP, State.nl, h1, CStore.rd]
      · simp [h1, applyCalls]; exact Same.refl _

theorem delta_reject (hW : WF s) (pred signer : A) (k : K) (i : Nat) :
    (cstep cfg s.rd (.reject pred signer k i)).1 = err cfg (α s g) (.reject pred signer k i) ∧
    Same (α (applyCalls s (cstep cfg s.rd (.reject pred signer k i)).2) g)
      (step cfg (α s g) (.reject pred signer k i)) := by
  simp only [cstep, err, rejectErr, step]
  simp only [authErr_α, decideErr_α cfg s g hW]
  cases hc : cauth s.rd pred signer k .approver with
  | error e =>
    have he := cauth_err_ne_ok hc
    simp [he, applyCalls]; exact Same.refl _
  | ok b =>
    obtain ⟨hk, -, -⟩ := cauth_ok hc
    cases hd : cdecidable s.rd i with
    | error e =>
      have he := cdecidable_err_ne_ok hd
      simp [he, applyCalls]; exact Same.refl _
    | ok rp =>
      obtain ⟨r, ag⟩ := rp
      obtain ⟨hr, ha, hj, hag, -, -⟩ := cdecidable_ok hd
      have hid := hW.ids i r hr
      have hr' : (α s g).req i = some (toR r) := by simp [req_α, hr]
      have hkey : (toR r).key = r.key := rfl
      simp only [hr', toR]
      by_cases h2 : signer = r.acct
      · simp [h2, applyCalls]; exact Same.refl _
      simp only [h2, ne_eq, not_true_eq_false, ite_false, ite_true]
      simp only [effect, hr']
      refine ⟨trivial, fun k' => ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;>
        try simp [applyCalls, applyCall, α, effect, hr']
      · simpa [applyCalls, applyCall, α, effect, hr', hkey, decidePrincipals] using
          decide_principals_same s hag (· - 1) k'
      · simp [applyCalls, applyCall, α, effect, hr', hid, List.map_set, toR, ha, hj, prin,
          plookup_αP, hk, toP]

end Ops

/-- L-DELTA: on every store of every size satisfying INV-1 and A6, the
transcribed `expect` is the model's error, and running the transcribed
`protocol` lands on the model's step (its effect on `Ok`, a stutter
otherwise), up to map and set equality. -/
theorem delta_refines (cfg : Cfg A) (s : CStore A K P) (g : List Ghost) (op : Op A K P)
    (hW : WF s) (ho : cfg.owner = s.owner) :
    (cstep cfg s.rd op).1 = err cfg (α s g) op ∧
    Same (α (applyCalls s (cstep cfg s.rd op).2) g) (step cfg (α s g) op) := by
  cases op with
  | add c k a r => exact delta_add cfg s g hW ho c k a r
  | revoke c k => exact delta_revoke cfg s g ho c k
  | request pred signer k x => exact delta_request cfg s g hW pred signer k x
  | approve pred signer k i x => exact delta_approve cfg s g hW pred signer k i x
  | reject pred signer k i => exact delta_reject cfg s g hW pred signer k i

end Approval
