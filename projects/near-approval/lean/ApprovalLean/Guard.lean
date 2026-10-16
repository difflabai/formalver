/-
LEAN-GUARD: each error operator returns the first failing guard of a guard
list whose codes are exactly TLA+'s `GuardOrder` for that entry point
(`LogFull` included, with a condition that never holds: counters are
unbounded, assumption A6). `Main.lean guards` prints `guardOrder` in the
format of `prolog/extracted/tla_facts.pl`, and `run-lean.sh` requires the
two to be equal (C-2t's chain: core = TLA+ = Prolog = Lean).
-/
import ApprovalLean.Lemmas

namespace Approval

variable {A K P : Type} [DecidableEq A] [DecidableEq K] [DecidableEq P]

inductive OpKind where
  | add
  | revoke
  | request
  | approve
  | reject
  deriving DecidableEq, Repr

def Op.kind : Op A K P → OpKind
  | .add .. => .add
  | .revoke .. => .revoke
  | .request .. => .request
  | .approve .. => .approve
  | .reject .. => .reject

/-- `GuardOrder`. -/
def guardOrder : OpKind → List Err
  | .add => [.notOwner, .keyAlreadyRegistered, .logFull]
  | .revoke => [.notOwner, .keyNotRegistered]
  | .request => [.indirectCall, .unknownKey, .wrongRole, .keyAccountMismatch,
                 .emptyAction, .actionTooLong, .tooManyPending, .logFull]
  | .approve => [.indirectCall, .unknownKey, .wrongRole, .keyAccountMismatch,
                 .requestNotFound, .alreadyApproved, .alreadyRejected, .agentRevoked,
                 .actionMismatch, .selfApproval, .logFull]
  | .reject => [.indirectCall, .unknownKey, .wrongRole, .keyAccountMismatch,
                .requestNotFound, .alreadyApproved, .alreadyRejected, .agentRevoked,
                .selfApproval]

/-- The first guard whose failure condition holds. -/
def firstFail : List (Err × Bool) → Option Err
  | [] => none
  | (e, b) :: gs => if b then some e else firstFail gs

/-- The guards of each call, in order: an error code and the condition
under which that guard fails. Conditions on a request read its record when
it exists; a missing request has already failed `RequestNotFound`. -/
def guards (cfg : Cfg A) (s : State A K P) : Op A K P → List (Err × Bool)
  | .add c k _ _ =>
    [(.notOwner, c ≠ cfg.owner), (.keyAlreadyRegistered, (prin cfg s k).reg), (.logFull, false)]
  | .revoke c k =>
    [(.notOwner, c ≠ cfg.owner), (.keyNotRegistered, !(prin cfg s k).reg)]
  | .request p sg k x =>
    authGuards cfg s p sg k .agent ++
    ([(.emptyAction, x = .empty), (.actionTooLong, x = .tooLong),
     (.tooManyPending, (prin cfg s k).pending ≥ cfg.maxPending), (.logFull, false)] : List (Err × Bool))
  | .approve p sg k i x =>
    authGuards cfg s p sg k .approver ++ decideGuards cfg s i ++
    ([(.actionMismatch, (s.req i).any (·.act ≠ x)),
      (.selfApproval, (s.req i).any (·.acct = sg)), (.logFull, false)] : List (Err × Bool))
  | .reject p sg k i =>
    authGuards cfg s p sg k .approver ++ decideGuards cfg s i ++
    ([(.selfApproval, (s.req i).any (·.acct = sg))] : List (Err × Bool))
where
  authGuards (cfg : Cfg A) (s : State A K P) (p sg : A) (k : K) (role : Role) :
      List (Err × Bool) :=
    [(.indirectCall, p ≠ sg), (.unknownKey, !(prin cfg s k).reg),
     (.wrongRole, (prin cfg s k).role ≠ role), (.keyAccountMismatch, (prin cfg s k).acct ≠ sg)]
  decideGuards (cfg : Cfg A) (s : State A K P) (i : Nat) : List (Err × Bool) :=
    [(.requestNotFound, (s.req i).isNone), (.alreadyApproved, (s.req i).any (·.appr)),
     (.alreadyRejected, (s.req i).any (·.rj)),
     (.agentRevoked, (s.req i).any (fun r => !liveR cfg s i r))]

theorem firstFail_append (g h : List (Err × Bool)) :
    firstFail (g ++ h) = (firstFail g).or (firstFail h) := by
  induction g with
  | nil => simp [firstFail]
  | cons e g ih =>
    obtain ⟨e, b⟩ := e
    cases b <;> simp [firstFail, ih]

/-- The guard list of every call has exactly `GuardOrder`'s codes. -/
theorem guards_order (cfg : Cfg A) (s : State A K P) (op : Op A K P) :
    (guards cfg s op).map Prod.fst = guardOrder op.kind := by
  cases op <;> simp [guards, guards.authGuards, guards.decideGuards, guardOrder, Op.kind]

private theorem authErr_eq (cfg : Cfg A) (s : State A K P) (p sg : A) (k : K) (role : Role) :
    authErr cfg s p sg k role = (firstFail (guards.authGuards cfg s p sg k role)).getD .ok ∧
    (authErr cfg s p sg k role = .ok ↔ firstFail (guards.authGuards cfg s p sg k role) = none) := by
  simp only [authErr, guards.authGuards, firstFail]
  repeat (first | split | simp_all)

private theorem decideErr_eq (cfg : Cfg A) (s : State A K P) (i : Nat) :
    decideErr cfg s i = (firstFail (guards.decideGuards cfg s i)).getD .ok ∧
    (decideErr cfg s i = .ok ↔ firstFail (guards.decideGuards cfg s i) = none) := by
  simp only [decideErr, guards.decideGuards, firstFail]
  cases s.req i with
  | none => simp
  | some r =>
    simp only [Option.isNone_some, Option.any_some, Bool.false_eq_true]
    repeat (first | split | simp_all)

theorem firstFail_mem (gs : List (Err × Bool)) {e : Err} (h : firstFail gs = some e) :
    e ∈ gs.map Prod.fst := by
  induction gs with
  | nil => simp [firstFail] at h
  | cons g gs ih =>
    obtain ⟨e', b⟩ := g
    cases b
    · simp only [firstFail, Bool.false_eq_true, ite_false] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp only [firstFail, ite_true, Option.some.injEq] at h
      simp [h]

theorem firstFail_or_getD (g h : List (Err × Bool)) (hg : ∀ e ∈ g.map Prod.fst, e ≠ .ok) :
    (firstFail (g ++ h)).getD .ok =
      if (firstFail g).getD .ok ≠ .ok then (firstFail g).getD .ok else (firstFail h).getD .ok := by
  rw [firstFail_append]
  cases hf : firstFail g with
  | none => simp
  | some e =>
    have : e ≠ .ok := hg e (firstFail_mem g hf)
    simp [this]

private theorem auth_codes (cfg : Cfg A) (s : State A K P) (p sg : A) (k : K) (role : Role) :
    ∀ e ∈ (guards.authGuards cfg s p sg k role).map Prod.fst, e ≠ .ok := by
  simp [guards.authGuards]

private theorem decide_codes (cfg : Cfg A) (s : State A K P) (i : Nat) :
    ∀ e ∈ (guards.decideGuards cfg s i).map Prod.fst, e ≠ .ok := by
  simp [guards.decideGuards]

/-- Each error operator is the first failing guard, so the guards are
checked in `GuardOrder`'s order (`ok` when none fails). -/
theorem err_eq_firstFail (cfg : Cfg A) (s : State A K P) (op : Op A K P) :
    err cfg s op = (firstFail (guards cfg s op)).getD .ok := by
  cases op with
  | add c k a r =>
    simp only [err, addErr, guards, firstFail]
    by_cases h1 : c = cfg.owner <;> by_cases h2 : (prin cfg s k).reg = true <;> simp [h1, h2]
  | revoke c k =>
    simp only [err, revokeErr, guards, firstFail]
    by_cases h1 : c = cfg.owner <;> by_cases h2 : (prin cfg s k).reg = true <;> simp [h1, h2]
  | request p sg k x =>
    simp only [err, requestErr, guards]
    rw [firstFail_or_getD _ _ (auth_codes cfg s p sg k .agent), ← (authErr_eq cfg s p sg k .agent).1]
    split
    · rfl
    · simp only [firstFail]
      by_cases h1 : x = .empty
      · simp [h1]
      · by_cases h2 : x = .tooLong
        · simp [h2]
        · by_cases h3 : cfg.maxPending ≤ (prin cfg s k).pending <;> simp [h1, h2, h3]
  | approve p sg k i x =>
    simp only [err, approveErr, guards, List.append_assoc]
    rw [firstFail_or_getD _ _ (auth_codes cfg s p sg k .approver),
      ← (authErr_eq cfg s p sg k .approver).1]
    split
    · rfl
    · rw [firstFail_or_getD _ _ (decide_codes cfg s i), ← (decideErr_eq cfg s i).1]
      split
      · rfl
      · rename_i hd
        simp only [ne_eq, Decidable.not_not] at hd
        simp only [firstFail]
        cases hr : s.req i with
        | none => simp [decideErr, hr] at hd
        | some r =>
          by_cases h1 : r.act = x
          · by_cases h2 : sg = r.acct
            · simp [h1, h2]
            · simp [h1, h2, Ne.symm h2]
          · simp [h1]
  | reject p sg k i =>
    simp only [err, rejectErr, guards, List.append_assoc]
    rw [firstFail_or_getD _ _ (auth_codes cfg s p sg k .approver),
      ← (authErr_eq cfg s p sg k .approver).1]
    split
    · rfl
    · rw [firstFail_or_getD _ _ (decide_codes cfg s i), ← (decideErr_eq cfg s i).1]
      split
      · rfl
      · rename_i hd
        simp only [ne_eq, Decidable.not_not] at hd
        simp only [firstFail]
        cases hr : s.req i with
        | none => simp [decideErr, hr] at hd
        | some r =>
          by_cases h2 : sg = r.acct
          · simp [h2]
          · simp [h2, Ne.symm h2]

/-- Every error a call returns is one `GuardOrder` lists for it. -/
theorem err_mem_guardOrder (cfg : Cfg A) (s : State A K P) (op : Op A K P) :
    err cfg s op = .ok ∨ err cfg s op ∈ guardOrder op.kind := by
  rw [err_eq_firstFail, ← guards_order cfg s op]
  cases h : firstFail (guards cfg s op) with
  | none => simp
  | some e => exact Or.inr (firstFail_mem _ h)

/-- `LogFull` is never returned: counters are unbounded (assumption A6). -/
theorem err_ne_logFull (cfg : Cfg A) (s : State A K P) (op : Op A K P) :
    err cfg s op ≠ .logFull := by
  cases op <;>
    simp only [err, addErr, revokeErr, requestErr, approveErr, rejectErr, authErr, decideErr] <;>
    repeat (first | split | simp_all)

end Approval
