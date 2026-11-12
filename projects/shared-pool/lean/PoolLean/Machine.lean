/-
The shared-pool decision kernel (`pool-core`) as a Lean state machine.

Upstream: difflabai/shared-pool-controls crates/core/src/lib.rs
Pin:      a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7 (PR #1 head)

Each definition names the code it transcribes (`lib.rs` line). Every call is
a list of guards in the code's order (`guards`), each an outcome (an error,
or an idempotent `Ok` no-op) and the condition under which it fires; the
first guard that fires is the call's outcome (`outcome`), and a call no
guard stops applies `effect`. A rejected call or a no-op leaves the state
alone (TX-0, TX-NOOP).

Representation, each difference fixed by the replay (`Main.lean`, REF-5L)
against the real core's traces:

* Numbers are `Int` (values, vectors, targets) and `Nat` (counters, units,
  times, versions). The code's i64/u64 arithmetic cannot overflow on the
  paths the model takes (NUM-1, NUM-2: add's operands are bounded by
  `validate` and `units ≤ 100`), so the model computes exactly; the u32
  `version` overflow is modelled exactly (`verGuard`: `checked_add(1)` fails
  at `U32_MAX`), and so is u64 `saturating_add` on times.
* `energy` is the exact sum `Σ w·r²` (no u64 overflow: NUM-1, which the
  code's bounds make impossible; Kani's job, not this layer's).
* `envelope` (lib.rs 185): the code applies the open records one by one and
  fails `Arithmetic` as soon as a partial `low`/`high` leaves ±1e6. Partial
  lows only decrease and partial highs only increase from the candidate,
  and the candidate is always the output of a successful `add` (so bounded),
  so "some partial sum leaves ±1e6" is "the final `low` or `high` leaves
  ±1e6"; the model checks the final sums (`envFail`).
* Vectors are read with `getD i 0` (`get`) and recipes with `getD k default`
  (`Cfg.recipe`). The code indexes (and would panic out of range); `Inv`
  (INV-WF, `Valid`) proves every such index in range in every reachable
  state, so the defaults are never read there.
* Metric, recipe and pool names and `max_age`'s u32 type are not modelled
  (no guard reads a name; `validate`'s string checks are out of scope).
* Accounts are a type parameter `A` with decidable equality: every theorem
  holds for every account universe.
* Ghost fields (never read by a guard): `base` and `k0`, the values and the
  record count at the last `observe` (or `new`), and `eff`, the number of
  effective transitions (calls that applied `effect`).
-/
namespace Pool

/-! ## Constants (lib.rs 9-15) -/

def MAX_METRICS : Nat := 32
def MAX_RECIPES : Nat := 32
def MAX_TERMS : Nat := 64
def MAX_RECORDS : Nat := 256
def MAX_VALUE : Int := 1000000
def MAX_WEIGHT : Nat := 1000
def MAX_UNITS : Nat := 100
/-- `u32::MAX`: `version.checked_add(1)` fails here. -/
def U32_MAX : Nat := 4294967295
/-- `u64::MAX`: `saturating_add` stops here. -/
def U64_MAX : Nat := 18446744073709551615
/-- The submit horizon (lib.rs 239). -/
def DAY : Nat := 86400

/-- `bounded` (lib.rs 50). -/
def Bounded (v : Int) : Prop := -MAX_VALUE ≤ v ∧ v ≤ MAX_VALUE

instance (v : Int) : Decidable (Bounded v) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every entry of a vector is bounded. -/
def AllB (v : List Int) : Prop := ∀ x ∈ v, Bounded x

instance (v : List Int) : Decidable (AllB v) := inferInstanceAs (Decidable (∀ x ∈ v, _))

/-! ## Data (lib.rs 25-42) -/

structure Metric where
  min : Int
  max : Int
  initial : Int
  deriving DecidableEq, Repr, Inhabited

inductive Shape where
  | target
  | excess
  | deficit
  deriving DecidableEq, Repr, Inhabited

structure Term where
  metric : Nat
  target : Int
  weight : Nat
  shape : Shape
  deriving DecidableEq, Repr, Inhabited

structure Recipe (A : Type) where
  actor : A
  executor : A
  reserve : List Int
  complete : List Int
  maxUnits : Nat
  requires : List (Nat × Nat)
  deriving DecidableEq, Repr, Inhabited

structure Cfg (A : Type) where
  owner : A
  maxAge : Nat
  metrics : List Metric
  terms : List Term
  recipes : List (Recipe A)
  deriving DecidableEq, Repr

inductive Status where
  | reserved
  | dispatched
  | active
  | unknown
  | completed
  | cancelled
  deriving DecidableEq, Repr, Inhabited

/-- `Commitment`. -/
structure Rec where
  id : Nat
  recipe : Nat
  units : Nat
  expiresAt : Nat
  status : Status
  deriving DecidableEq, Repr, Inhabited

/-- `Error` (lib.rs 41). -/
inductive Err where
  | invalidConfig
  | unauthorized
  | paused
  | stale
  | expired
  | snapshotExpired
  | invalidRecipe
  | invalidUnits
  | prerequisite
  | full
  | arithmetic
  | bounds
  | energy
  | invalidState
  | notFound
  | pending
  deriving DecidableEq, Repr, Inhabited

/-- `Pool` minus its (immutable) config, plus the ghost fields. -/
structure State where
  values : List Int
  version : Nat
  observedAt : Nat
  paused : Bool
  records : List Rec
  /-- ghost: `values` at the last `observe` (or `new`) -/
  base : List Int
  /-- ghost: `records.len()` at the last `observe` (or `new`) -/
  k0 : Nat
  /-- ghost: the number of effective transitions -/
  eff : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Every call the pool exposes. `now` is the block time in seconds. -/
inductive Op (A : Type) where
  | submit (caller : A) (recipe units version expiresAt now : Nat)
  | dispatch (caller : A) (id now : Nat)
  | ack (id : Nat) (accepted : Bool)
  | cancel (caller : A) (id now : Nat)
  | settle (caller : A) (id : Nat) (completed : Bool)
  | pause (caller : A) (paused : Bool)
  | observe (caller : A) (values : List Int) (now : Nat)
  deriving DecidableEq, Repr

variable {A : Type} [DecidableEq A] [Inhabited A]

/-! ## Helpers -/

def Cfg.n (cfg : Cfg A) : Nat := cfg.metrics.length
def Cfg.recipe (cfg : Cfg A) (k : Nat) : Recipe A := cfg.recipes.getD k default
def Cfg.metric (cfg : Cfg A) (i : Nat) : Metric := cfg.metrics.getD i default

/-- `v[i]`. -/
def get (v : List Int) (i : Nat) : Int := v.getD i 0

def sumI {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | a :: l => f a + sumI f l

def sumN {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => f a + sumN f l

/-- Some index below `n` satisfies `p`. -/
def anyLt (n : Nat) (p : Nat → Bool) : Bool := (List.range n).any p

/-- `u64::saturating_add`. -/
def satAdd (a b : Nat) : Nat := min (a + b) U64_MAX

/-- `open` (lib.rs 56). -/
def Status.isOpen : Status → Bool
  | .completed => false
  | .cancelled => false
  | _ => true

/-- `add`'s result (lib.rs 59): `base[i] + d[i]·u`, over the shorter length. -/
def addv (base d : List Int) (u : Nat) : List Int :=
  List.zipWith (fun x y => x + y * (u : Int)) base d

/-- `release`'s `undo` (lib.rs 411). -/
def neg (d : List Int) : List Int := d.map (fun x => -x)

/-- `violations(values)[i]` (lib.rs 176): PV_i. -/
def viol (cfg : Cfg A) (v : List Int) (i : Nat) : Int :=
  max 0 ((cfg.metric i).min - get v i) + max 0 (get v i - (cfg.metric i).max)

/-- `violations(values).iter().any(|v| *v > 0)`. -/
def violating (cfg : Cfg A) (v : List Int) : Bool :=
  anyLt cfg.n (fun i => decide (0 < viol cfg v i))

/-! ## Envelope and bounds (lib.rs 185-231) -/

/-- `r.complete[i] · units` for recipe `r`. -/
def dlt (cfg : Cfg A) (r u i : Nat) : Int := get (cfg.recipe r).complete i * (u : Int)

/-- `open(&c.status) && Some(c.id) != skip`. -/
def inEnv (skip : Option Nat) (c : Rec) : Bool := c.status.isOpen && (skip != some c.id)

/-- `Σ f(complete_i·units)` over the records the envelope applies. -/
def envS (f : Int → Int) (cfg : Cfg A) (recs : List Rec) (skip : Option Nat) (i : Nat) : Int :=
  sumI (fun c => if inEnv skip c then f (dlt cfg c.recipe c.units i) else 0) recs

/-- The `extra` record's term. -/
def extraD (f : Int → Int) (cfg : Cfg A) : Option (Nat × Nat) → Nat → Int
  | none, _ => 0
  | some (r, u), i => f (dlt cfg r u i)

def low (cfg : Cfg A) (recs : List Rec) (v : List Int) (extra : Option (Nat × Nat))
    (skip : Option Nat) (i : Nat) : Int :=
  get v i + envS (fun x => min 0 x) cfg recs skip i + extraD (fun x => min 0 x) cfg extra i

def high (cfg : Cfg A) (recs : List Rec) (v : List Int) (extra : Option (Nat × Nat))
    (skip : Option Nat) (i : Nat) : Int :=
  get v i + envS (fun x => max 0 x) cfg recs skip i + extraD (fun x => max 0 x) cfg extra i

/-- `envelope(..)` returns `Arithmetic`. -/
def envFail (cfg : Cfg A) (recs : List Rec) (v : List Int) (extra : Option (Nat × Nat))
    (skip : Option Nat) : Bool :=
  anyLt v.length fun i =>
    !(decide (Bounded (low cfg recs v extra skip i)) && decide (Bounded (high cfg recs v extra skip i)))

/-- EV_i: the envelope's violation of metric `i`. -/
def ev (cfg : Cfg A) (recs : List Rec) (v : List Int) (extra : Option (Nat × Nat))
    (skip : Option Nat) (i : Nat) : Int :=
  max 0 ((cfg.metric i).min - low cfg recs v extra skip i) +
    max 0 (high cfg recs v extra skip i - (cfg.metric i).max)

/-- `check_bounds` returns `Bounds` (once `envelope` succeeded). -/
def boundsFail (cfg : Cfg A) (s : State) (v : List Int) (extra : Option (Nat × Nat))
    (skip : Option Nat) : Bool :=
  anyLt cfg.n fun i => decide (viol cfg s.values i < ev cfg s.records v extra skip i)

/-! ## Energy (lib.rs 151-175) -/

def resid : Shape → Int → Nat
  | .target, d => d.natAbs
  | .excess, d => (max d 0).toNat
  | .deficit, d => (max (-d) 0).toNat

def termE (v : List Int) (t : Term) : Nat :=
  let r := resid t.shape (get v t.metric - t.target)
  r * r * t.weight

def energy (cfg : Cfg A) (v : List Int) : Nat := sumN (termE v) cfg.terms

/-- `energy_terms` returns `Bounds`. -/
def energyBad (cfg : Cfg A) (v : List Int) : Bool :=
  decide (v.length ≠ cfg.n) || !decide (AllB v)

/-! ## Prerequisites (lib.rs 264) -/

/-- A record's units if it is a completed record of recipe `p`. -/
def doneF (p : Nat) (c : Rec) : Nat := if c.recipe = p ∧ c.status = .completed then c.units else 0

/-- Units of recipe `p` in `Completed` records. -/
def doneUnits (recs : List Rec) (p : Nat) : Nat := sumN (doneF p) recs

def prereqFail (rc : Recipe A) (recs : List Rec) : Bool :=
  rc.requires.any fun pu => decide (doneUnits recs pu.1 < pu.2)

/-! ## Guards, in the code's order -/

/-- What a guard yields when it fires. -/
inductive Out where
  | err (e : Err)
  | noop
  deriving DecidableEq, Repr

abbrev Guard := Out × Bool

/-- The first guard that fires. -/
def firstFail : List Guard → Option Out
  | [] => none
  | (o, b) :: gs => if b then some o else firstFail gs

/-- `add(base, d, u)?` (lib.rs 59). -/
def addGuards (base d : List Int) (u : Nat) : List Guard :=
  [(.err .invalidConfig, decide (base.length ≠ d.length)),
   (.err .arithmetic, !decide (AllB (addv base d u)))]

/-- `check_bounds(next, extra, skip)?` (lib.rs 216). -/
def boundsGuards (cfg : Cfg A) (s : State) (next : List Int) (extra : Option (Nat × Nat))
    (skip : Option Nat) : List Guard :=
  [(.err .arithmetic, envFail cfg s.records next extra skip),
   (.err .bounds, boundsFail cfg s next extra skip)]

/-- `self.version.checked_add(1)?` / `bump()?`. -/
def verGuard (s : State) : Guard := (.err .arithmetic, decide (U32_MAX ≤ s.version))

/-- `self.record(id)?` (lib.rs 339). -/
def foundGuard (s : State) (id : Nat) : Guard := (.err .notFound, decide (s.records.length ≤ id))

/-- The record `id` (`default` when absent; every guard reading it comes after `foundGuard`). -/
def State.record (s : State) (id : Nat) : Rec := s.records.getD id default

def snapshotOld (cfg : Cfg A) (s : State) (now : Nat) : Bool :=
  decide (0 < cfg.maxAge ∧ satAdd s.observedAt cfg.maxAge < now)

/-- `candidate` + `submit` (lib.rs 232, 324). -/
def submitGuards (cfg : Cfg A) (s : State) (caller : A) (r u ver exp now : Nat) : List Guard :=
  let rc := cfg.recipe r
  let next := addv s.values rc.reserve u
  let post := addv next rc.complete u
  let bad := violating cfg s.values
  [(.err .paused, s.paused),
   (.err .stale, decide (ver ≠ s.version)),
   (.err .expired, decide (exp ≤ now ∨ satAdd now DAY < exp)),
   (.err .snapshotExpired, snapshotOld cfg s now),
   (.err .full, decide (MAX_RECORDS ≤ s.records.length)),
   (.err .invalidRecipe, decide (cfg.recipes.length ≤ r)),
   (.err .unauthorized, decide (caller ≠ rc.actor)),
   (.err .invalidUnits, decide (u = 0 ∨ rc.maxUnits < u)),
   (.err .prerequisite, prereqFail rc s.records)] ++
  addGuards s.values rc.reserve u ++
  boundsGuards cfg s next (some (r, u)) none ++
  [(.err .bounds, energyBad cfg s.values),
   (.err .bounds, energyBad cfg next),
   (.err .energy, decide (energy cfg s.values < energy cfg next))] ++
  (addGuards next rc.complete u).map (fun g => (g.1, bad && g.2)) ++
  [(.err .bounds, bad && energyBad cfg post),
   (.err .energy, bad && decide (energy cfg s.values ≤ energy cfg post)),
   verGuard s]

/-- `dispatch` (lib.rs 346). -/
def dispatchGuards (cfg : Cfg A) (s : State) (caller : A) (id now : Nat) : List Guard :=
  let c := s.record id
  [foundGuard s id,
   (.err .unauthorized, decide (caller ≠ (cfg.recipe c.recipe).actor)),
   (.err .paused, s.paused),
   (.err .invalidState, decide (c.status ≠ .reserved)),
   (.err .expired, decide (c.expiresAt ≤ now)),
   (.err .snapshotExpired, snapshotOld cfg s now),
   verGuard s]

/-- `acknowledge`'s target status. -/
def ackStatus (accepted : Bool) : Status := if accepted then .active else .unknown

/-- `acknowledge` (lib.rs 374). -/
def ackGuards (s : State) (id : Nat) (accepted : Bool) : List Guard :=
  let c := s.record id
  [foundGuard s id,
   (.noop, decide (c.status ≠ .dispatched ∧ c.status ≠ .unknown)),
   (.noop, decide (c.status = ackStatus accepted)),
   verGuard s]

/-- `release`'s new values. -/
def releaseNext (cfg : Cfg A) (s : State) (id : Nat) : List Int :=
  addv s.values (neg (cfg.recipe (s.record id).recipe).reserve) (s.record id).units

/-- `release` (lib.rs 408). -/
def releaseGuards (cfg : Cfg A) (s : State) (id : Nat) : List Guard :=
  let c := s.record id
  [foundGuard s id] ++
  addGuards s.values (neg (cfg.recipe c.recipe).reserve) c.units ++
  boundsGuards cfg s (releaseNext cfg s id) none (some id) ++
  [verGuard s]

/-- `cancel` (lib.rs 393). -/
def cancelGuards (cfg : Cfg A) (s : State) (caller : A) (id : Nat) : List Guard :=
  let c := s.record id
  [foundGuard s id,
   (.err .unauthorized, decide (caller ≠ (cfg.recipe c.recipe).actor ∧ caller ≠ cfg.owner)),
   (.noop, decide (c.status = .cancelled)),
   (.err .pending, decide (c.status ≠ .reserved))] ++
  releaseGuards cfg s id

/-- `settle(.., true)`'s new values. -/
def completeNext (cfg : Cfg A) (s : State) (id : Nat) : List Int :=
  addv s.values (cfg.recipe (s.record id).recipe).complete (s.record id).units

/-- Status in `Dispatched | Active | Unknown`. -/
def inFlight : Status → Bool
  | .dispatched => true
  | .active => true
  | .unknown => true
  | _ => false

/-- `settle` (lib.rs 423). -/
def settleGuards (cfg : Cfg A) (s : State) (caller : A) (id : Nat) (done : Bool) : List Guard :=
  let c := s.record id
  [foundGuard s id,
   (.err .unauthorized, decide (caller ≠ (cfg.recipe c.recipe).executor)),
   (.noop, decide ((done = true ∧ c.status = .completed) ∨ (done = false ∧ c.status = .cancelled))),
   (.err .invalidState, !inFlight c.status)] ++
  (if done then
    addGuards s.values (cfg.recipe c.recipe).complete c.units ++
    boundsGuards cfg s (completeNext cfg s id) none (some id) ++
    [verGuard s]
  else releaseGuards cfg s id)

/-- `set_paused` (lib.rs 450). -/
def pauseGuards (cfg : Cfg A) (s : State) (caller : A) : List Guard :=
  [(.err .unauthorized, decide (caller ≠ cfg.owner)), verGuard s]

/-- `observe` (lib.rs 460). -/
def observeGuards (cfg : Cfg A) (s : State) (caller : A) (vals : List Int) : List Guard :=
  [(.err .unauthorized, decide (caller ≠ cfg.owner)),
   (.err .pending, s.records.any (fun c => c.status.isOpen)),
   (.err .bounds, decide (vals.length ≠ s.values.length) || !decide (AllB vals)),
   (.err .bounds, energyBad cfg vals),
   verGuard s]

/-- The guards of each call, in the code's order. -/
def guards (cfg : Cfg A) (s : State) : Op A → List Guard
  | .submit c r u ver exp now => submitGuards cfg s c r u ver exp now
  | .dispatch c id now => dispatchGuards cfg s c id now
  | .ack id acc => ackGuards s id acc
  | .cancel c id _ => cancelGuards cfg s c id
  | .settle c id done => settleGuards cfg s c id done
  | .pause c _ => pauseGuards cfg s c
  | .observe c vals _ => observeGuards cfg s c vals

def outcome (cfg : Cfg A) (s : State) (op : Op A) : Option Out := firstFail (guards cfg s op)

/-! ## Effects -/

/-- `self.records[id].status = st`. -/
def setStatus (recs : List Rec) (id : Nat) (st : Status) : List Rec :=
  recs.set id { recs.getD id default with status := st }

/-- `release`'s effect. -/
def release (cfg : Cfg A) (s : State) (id : Nat) : State :=
  { s with values := releaseNext cfg s id, records := setStatus s.records id .cancelled,
           version := s.version + 1 }

/-- Each call's post-state, given that no guard fired. -/
def effect (cfg : Cfg A) (s : State) : Op A → State
  | .submit _ r u _ exp _ =>
    { s with records := s.records ++ [⟨s.records.length, r, u, exp, .reserved⟩],
             values := addv s.values (cfg.recipe r).reserve u,
             version := s.version + 1 }
  | .dispatch _ id _ =>
    { s with records := setStatus s.records id .dispatched, version := s.version + 1 }
  | .ack id acc =>
    { s with records := setStatus s.records id (ackStatus acc), version := s.version + 1 }
  | .cancel _ id _ => release cfg s id
  | .settle _ id done =>
    if done then
      { s with values := completeNext cfg s id, records := setStatus s.records id .completed,
               version := s.version + 1 }
    else release cfg s id
  | .pause _ b => { s with paused := b, version := s.version + 1 }
  | .observe _ vals now =>
    { s with values := vals, observedAt := now, version := s.version + 1,
             base := vals, k0 := s.records.length }

/-- A call's result. -/
inductive Res where
  | ok
  | okId (id : Nat)
  | err (e : Err)
  deriving DecidableEq, Repr

/-- An effective call's result: `submit` returns the new record's id. -/
def okRes (s : State) : Op A → Res
  | .submit .. => .okId s.records.length
  | _ => .ok

/-- One call: its result and the post-state. A rejected call and a no-op
leave the state unchanged (TX-0, TX-NOOP); an effective call applies
`effect` and counts one more effective transition (ghost `eff`). -/
def exec (cfg : Cfg A) (s : State) (op : Op A) : Res × State :=
  match outcome cfg s op with
  | some (.err e) => (.err e, s)
  | some .noop => (.ok, s)
  | none => (okRes s op, { effect cfg s op with eff := s.eff + 1 })

def step (cfg : Cfg A) (s : State) (op : Op A) : State := (exec cfg s op).2

/-- `Pool::new` (lib.rs 139), for a config `validate` accepts. -/
def init (cfg : Cfg A) (now : Nat) : State :=
  let v := cfg.metrics.map (·.initial)
  { values := v, version := 0, observedAt := now, paused := false, records := [],
    base := v, k0 := 0, eff := 0 }

def run (cfg : Cfg A) (s : State) (ops : List (Op A)) : State := ops.foldl (step cfg) s

inductive Reach (cfg : Cfg A) : State → Prop where
  | init (now : Nat) : Reach cfg (init cfg now)
  | step {s : State} (op : Op A) : Reach cfg s → Reach cfg (step cfg s op)

/-! ## `Config::validate` (lib.rs 78), names aside -/

/-- One recipe's checks, `k` its index. -/
structure RecipeOk (cfg : Cfg A) (k : Nat) (r : Recipe A) : Prop where
  reserveLen : r.reserve.length = cfg.n
  completeLen : r.complete.length = cfg.n
  unitsPos : 0 < r.maxUnits
  unitsLe : r.maxUnits ≤ MAX_UNITS
  reqLen : r.requires.length ≤ MAX_RECIPES
  req : ∀ pu ∈ r.requires, pu.1 < k ∧ 0 < pu.2 ∧ pu.2 ≤ MAX_UNITS
  reserveB : AllB r.reserve
  completeB : AllB r.complete
  reqNodup : (r.requires.map Prod.fst).Nodup

/-- CFG-2: what `validate` establishes (string checks aside). -/
structure Valid (cfg : Cfg A) : Prop where
  nPos : 0 < cfg.n
  nLe : cfg.n ≤ MAX_METRICS
  rPos : 0 < cfg.recipes.length
  rLe : cfg.recipes.length ≤ MAX_RECIPES
  tPos : 0 < cfg.terms.length
  tLe : cfg.terms.length ≤ MAX_TERMS
  metric : ∀ m ∈ cfg.metrics,
    Bounded m.min ∧ Bounded m.max ∧ m.min ≤ m.max ∧ m.min ≤ m.initial ∧ m.initial ≤ m.max
  term : ∀ t ∈ cfg.terms,
    t.metric < cfg.n ∧ Bounded t.target ∧ 0 < t.weight ∧ t.weight ≤ MAX_WEIGHT
  recipe : ∀ k (h : k < cfg.recipes.length), RecipeOk cfg k cfg.recipes[k]

end Pool
