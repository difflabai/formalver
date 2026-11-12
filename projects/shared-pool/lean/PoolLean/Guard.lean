/-
LEAN-GUARD: the guard list of every call has exactly the code's order of
outcomes (`guardOrder`, read off lib.rs), and every outcome a call can have
is the first guard of that list that fires. `pool-lean guards` prints
`guardOrder` for comparison with the other layers' guard tables (C-2).
-/
import PoolLean.Machine

namespace Pool.Guard

open Pool

variable {A : Type} [DecidableEq A] [Inhabited A]

/-- Call kinds; `settle` has one guard list per value of `completed`. -/
inductive Kind where
  | submit
  | dispatch
  | ack
  | cancel
  | settleDone
  | settleUndone
  | pause
  | observe
  deriving DecidableEq, Repr

def kinds : List Kind :=
  [.submit, .dispatch, .ack, .cancel, .settleDone, .settleUndone, .pause, .observe]

def kind : Op A → Kind
  | .submit .. => .submit
  | .dispatch .. => .dispatch
  | .ack .. => .ack
  | .cancel .. => .cancel
  | .settle _ _ true => .settleDone
  | .settle _ _ false => .settleUndone
  | .pause .. => .pause
  | .observe .. => .observe

open Out Err in
/-- The code's guard order, call by call (lib.rs line of each check). -/
def guardOrder : Kind → List Out
  -- candidate 233-285, submit 326
  | .submit => [err paused, err stale, err expired, err snapshotExpired, err full,
                err invalidRecipe, err unauthorized, err invalidUnits, err prerequisite,
                err invalidConfig, err arithmetic,       -- add (274)
                err arithmetic, err bounds,              -- check_bounds (275)
                err bounds, err bounds, err Err.energy,      -- energy before/after (276-280)
                err invalidConfig, err arithmetic,       -- recovery add (282)
                err bounds, err Err.energy,                  -- recovery energy (282)
                err arithmetic]                          -- version (326)
  -- 347-369
  | .dispatch => [err notFound, err unauthorized, err paused, err invalidState, err expired,
                  err snapshotExpired, err arithmetic]
  -- 375-389
  | .ack => [err notFound, noop, noop, err arithmetic]
  -- 394-406, then release 409-416
  | .cancel => [err notFound, err unauthorized, noop, err pending,
                err notFound, err invalidConfig, err arithmetic, err arithmetic, err bounds,
                err arithmetic]
  -- 424-445
  | .settleDone => [err notFound, err unauthorized, noop, err invalidState,
                    err invalidConfig, err arithmetic, err arithmetic, err bounds, err arithmetic]
  -- 424-441, then release 409-416
  | .settleUndone => [err notFound, err unauthorized, noop, err invalidState,
                      err notFound, err invalidConfig, err arithmetic, err arithmetic, err bounds,
                      err arithmetic]
  -- 451-454
  | .pause => [err unauthorized, err arithmetic]
  -- 461-471
  | .observe => [err unauthorized, err pending, err bounds, err bounds, err arithmetic]

/-- LEAN-GUARD: every call's guard list has exactly `guardOrder`'s outcomes, in order. -/
theorem guards_order (cfg : Cfg A) (s : State) (op : Op A) :
    (guards cfg s op).map Prod.fst = guardOrder (kind op) := by
  cases op with
  | settle c id done => cases done <;> rfl
  | _ => rfl

theorem firstFail_mem {gs : List Guard} {o : Out} (h : firstFail gs = some o) :
    o ∈ gs.map Prod.fst := by
  induction gs with
  | nil => simp [firstFail] at h
  | cons g gs ih =>
    obtain ⟨o', b⟩ := g
    cases b
    · simp only [firstFail] at h; exact List.mem_cons_of_mem _ (ih (by simpa using h))
    · simp only [firstFail, if_true] at h; cases h; simp

/-- Every outcome a call can have is in its kind's `guardOrder`. -/
theorem outcome_mem (cfg : Cfg A) (s : State) (op : Op A) {o : Out}
    (h : outcome cfg s op = some o) : o ∈ guardOrder (kind op) := by
  rw [← guards_order cfg s op]; exact firstFail_mem h

def outName : Out → String
  | .noop => "noop"
  | .err e => match e with
    | .invalidConfig => "invalid_config"
    | .unauthorized => "unauthorized"
    | .paused => "paused"
    | .stale => "stale"
    | .expired => "expired"
    | .snapshotExpired => "snapshot_expired"
    | .invalidRecipe => "invalid_recipe"
    | .invalidUnits => "invalid_units"
    | .prerequisite => "prerequisite"
    | .full => "full"
    | .arithmetic => "arithmetic"
    | .bounds => "bounds"
    | .energy => "energy"
    | .invalidState => "invalid_state"
    | .notFound => "not_found"
    | .pending => "pending"

def kindName : Kind → String
  | .submit => "submit"
  | .dispatch => "dispatch"
  | .ack => "ack"
  | .cancel => "cancel"
  | .settleDone => "settle_completed"
  | .settleUndone => "settle_cancelled"
  | .pause => "pause"
  | .observe => "observe"

end Pool.Guard
