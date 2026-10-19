/-
LEAN-LIVE: TLA-LIVE-1 (`MC_Liveness.tla`) at every size.

TLC checks `Live1` under `LiveSpec` with at most 2 requests, 2 keys and 4
registrations. Here the same formula is proved for every behaviour of the
machine: any account, key and payload types, any `MaxPending`, any number
of requests and registrations, and any step relation contained in `Next`
(so `MC_Liveness`'s bounded `BNext` is one instance).

TLA+'s temporal operators are transcribed over behaviours `Nat → State`,
each a definition next to the formula it encodes:

* `[][N]_vars`         every step is an `N` step or a stutter (`Steps`);
* `<>[]F`              from some instant on, `F` at every instant;
* `[]<>F`              after every instant, `F` at some later instant;
* `ENABLED <<A>>_vars` some non-stuttering `A` step leaves the state;
* `WF_vars(A)`         `<>[]ENABLED <<A>>_vars => []<><<A>>_vars` (`WeakFair`);
* `SF_vars(A)`         `[]<>ENABLED <<A>>_vars => []<><<A>>_vars` (`StrongFair`).

`ApproveReq(i)` and `Eligible(i)` are `MC_Liveness.tla`'s operators;
`Pending(i)` is `pendingReq` (`Machine.lean`).
-/
import ApprovalLean.Inv.Approvable

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

/-! ## Temporal operators over behaviours -/

/-- A behaviour: the state at each instant. -/
abbrev Behavior (A K P : Type) := Nat → State A K P

/-- `[][R]_vars`. -/
def Steps (R : State A K P → State A K P → Prop) (σ : Behavior A K P) : Prop :=
  ∀ n, R (σ n) (σ (n + 1)) ∨ σ (n + 1) = σ n

/-- `<<A>>_vars`: an `A` step that changes the state. -/
def Angle (R : State A K P → State A K P → Prop) (s s' : State A K P) : Prop :=
  R s s' ∧ s' ≠ s

/-- `ENABLED <<A>>_vars`. -/
def Enabled (R : State A K P → State A K P → Prop) (s : State A K P) : Prop :=
  ∃ s', Angle R s s'

/-- `<>[]F`. -/
def EvAlways (F : State A K P → Prop) (σ : Behavior A K P) : Prop :=
  ∃ n, ∀ m, n ≤ m → F (σ m)

/-- `[]<>F`. -/
def InfOften (F : State A K P → Prop) (σ : Behavior A K P) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ F (σ m)

/-- `[]<><<A>>_vars`. -/
def InfOftenStep (R : State A K P → State A K P → Prop) (σ : Behavior A K P) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ Angle R (σ m) (σ (m + 1))

/-- `WF_vars(A)`. -/
def WeakFair (R : State A K P → State A K P → Prop) (σ : Behavior A K P) : Prop :=
  EvAlways (Enabled R) σ → InfOftenStep R σ

/-- `SF_vars(A)`. -/
def StrongFair (R : State A K P → State A K P → Prop) (σ : Behavior A K P) : Prop :=
  InfOften (Enabled R) σ → InfOftenStep R σ

/-! ## `MC_Liveness.tla` -/

/-- `ApproveReq(i) == i \in Ids /\ \E s, k: Approve(s, s, k, i, Req(i).act)`. -/
def ApproveReq (cfg : Cfg A) (i : Nat) (s s' : State A K P) : Prop :=
  ∃ r, s.req i = some r ∧ ∃ sg k,
    approveErr cfg s sg sg k i r.act = .ok ∧ s' = effect cfg s (.approve sg sg k i r.act)

/-- `Eligible(i) == i \in Ids /\ \E k: EligibleKey(i, k)`. -/
def Eligible (cfg : Cfg A) (i : Nat) (s : State A K P) : Prop :=
  ∃ r, s.req i = some r ∧ ∃ k, EligibleKey cfg s r k

/-- `[](Pending(i) => <>~Pending(i))`. -/
def LeadsOff (cfg : Cfg A) (i : Nat) (σ : Behavior A K P) : Prop :=
  ∀ n, pendingReq cfg (σ n) i → ∃ m, n ≤ m ∧ ¬ pendingReq cfg (σ m) i

/-- `Live1 == \A i: (<>[]Eligible(i)) => [](Pending(i) => <>~Pending(i))`. -/
def Live1 (cfg : Cfg A) (σ : Behavior A K P) : Prop :=
  ∀ i, EvAlways (Eligible cfg i) σ → LeadsOff cfg i σ

/-- The same with an eligible approver only infinitely often (`[]<>`),
for `live1_sf` under strong fairness (TLA-LIVE-1s). -/
def Live1Inf (cfg : Cfg A) (σ : Behavior A K P) : Prop :=
  ∀ i, InfOften (Eligible cfg i) σ → LeadsOff cfg i σ

/-- `LiveSpec == Init /\ [][Next]_vars /\ \A i: WF_vars(ApproveReq(i))`,
with any step relation `R` in place of `Next`. -/
def LiveSpec (cfg : Cfg A) (R : State A K P → State A K P → Prop)
    (σ : Behavior A K P) : Prop :=
  σ 0 = init ∧ Steps R σ ∧ ∀ i, WeakFair (ApproveReq cfg i) σ

/-- `UnfairSpec == Init /\ [][Next]_vars`. -/
def UnfairSpec (_cfg : Cfg A) (R : State A K P → State A K P → Prop)
    (σ : Behavior A K P) : Prop :=
  σ 0 = init ∧ Steps R σ

/-! ## The two facts liveness rests on -/

/-- An approval of request `i` decides it, so it is no longer pending. -/
theorem approveReq_not_pending {cfg : Cfg A} {i : Nat} {s s' : State A K P}
    (h : ApproveReq cfg i s s') : ¬ pendingReq cfg s' i := by
  obtain ⟨r, hr, sg, k, _, rfl⟩ := h
  have hlt := req_lt hr
  have hr0 : s.requests[i]? = some r := hr
  rintro ⟨r', hr', hd, _⟩
  simp only [effect, State.req, hr0, List.getElem?_set_self hlt] at hr'
  cases hr'
  simp [Request.decided] at hd

/-- TLA-LIVE-2 gives the enabling condition: a pending request with an
eligible approver can be approved, by a step that changes the state. -/
theorem enabled_of_pending {cfg : Cfg A} {i : Nat} {s : State A K P}
    (hp : pendingReq cfg s i) (he : Eligible cfg i s) : Enabled (ApproveReq cfg i) s := by
  obtain ⟨r, hr, hd, hl⟩ := hp
  obtain ⟨r', hr', k, hk⟩ := he
  rw [hr] at hr'
  cases hr'
  have hok := (approvable_all cfg s i r k hr hd hl hk).1
  refine ⟨_, ⟨r, hr, _, k, hok, rfl⟩, ?_⟩
  intro heq
  exact approveReq_not_pending ⟨r, hr, _, k, hok, heq.symm⟩ ⟨r, hr, hd, hl⟩

/-! ## TLA-LIVE-1 at every size -/

/-- Pending forever from instant `n` contradicts an approval at or after `n`. -/
theorem leadsOff_of_steps {cfg : Cfg A} {i : Nat} {σ : Behavior A K P}
    (hstep : ∀ n, (∀ m, n ≤ m → pendingReq cfg (σ m) i) →
      ∃ m, n ≤ m ∧ ApproveReq cfg i (σ m) (σ (m + 1))) :
    LeadsOff cfg i σ := by
  intro n _
  apply Classical.byContradiction
  intro hno
  have hall : ∀ m, n ≤ m → pendingReq cfg (σ m) i := fun m hm =>
    Classical.byContradiction fun h => hno ⟨m, hm, h⟩
  obtain ⟨m, hm, ha⟩ := hstep n hall
  exact approveReq_not_pending ha (hall (m + 1) (Nat.le_succ_of_le hm))

/-- Weak fairness on approval and an eligible approver from some point on:
the request leaves `Pending`. No step relation, initial state or invariant
is needed: `Approvable` holds in every state (`approvable_all`). -/
theorem live1_wf {cfg : Cfg A} {i : Nat} {σ : Behavior A K P}
    (hwf : WeakFair (ApproveReq cfg i) σ) (he : EvAlways (Eligible cfg i) σ) :
    LeadsOff cfg i σ := by
  apply leadsOff_of_steps
  intro n hp
  obtain ⟨n0, hn0⟩ := he
  have hen : EvAlways (Enabled (ApproveReq cfg i)) σ :=
    ⟨max n n0, fun m hm =>
      enabled_of_pending (hp m (Nat.le_trans (Nat.le_max_left _ _) hm))
        (hn0 m (Nat.le_trans (Nat.le_max_right _ _) hm))⟩
  obtain ⟨m, hm, ha, _⟩ := hwf hen n
  exact ⟨m, hm, ha⟩

/-- TLA-LIVE-1: `LiveSpec => Live1`, for every step relation `R`, so for
`Next` at every size and for `MC_Liveness`'s bounded `BNext`. -/
theorem live1 {cfg : Cfg A} {R : State A K P → State A K P → Prop}
    {σ : Behavior A K P} (h : LiveSpec cfg R σ) : Live1 cfg σ :=
  fun i he => live1_wf (h.2.2 i) he

/-- TLA-LIVE-1 strengthened: under strong fairness, an eligible approver
infinitely often (an approver key revoked and re-added, say) is enough. -/
theorem live1_sf {cfg : Cfg A} {σ : Behavior A K P}
    (hsf : ∀ i, StrongFair (ApproveReq cfg i) σ) : Live1Inf cfg σ := by
  intro i he
  apply leadsOff_of_steps
  intro n hp
  have hen : InfOften (Enabled (ApproveReq cfg i)) σ := fun m => by
    obtain ⟨m', hm', he'⟩ := he (max n m)
    exact ⟨m', Nat.le_trans (Nat.le_max_right _ _) hm',
      enabled_of_pending (hp m' (Nat.le_trans (Nat.le_max_left _ _) hm')) he'⟩
  obtain ⟨m, hm, ha, _⟩ := hsf i hen n
  exact ⟨m, hm, ha⟩

/-- `Live1Inf` implies `Live1`: `<>[]` implies `[]<>`. -/
theorem live1_of_live1Inf {cfg : Cfg A} {σ : Behavior A K P} (h : Live1Inf cfg σ) :
    Live1 cfg σ := by
  intro i ⟨n0, hn0⟩
  exact h i fun n => ⟨max n n0, Nat.le_max_left _ _, hn0 _ (Nat.le_max_right _ _)⟩

end Approval
