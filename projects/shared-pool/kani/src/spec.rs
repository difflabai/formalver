//! Executable specification of `pool-core` (shared-pool brief, "Exact core
//! semantics"; property IDs from its catalogue).
//!
//! Upstream: difflabai/shared-pool-controls `crates/core/src/lib.rs`
//! Pin:      a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7 (PR #1 head; core, contract and executor byte-identical to v1.0.0)
//! sha256:   9a4eb36cc9690d353f8ec78e4eec6e389a895caccab24ced54994b8a8e7505c4
//! Covers:   Config::validate, Pool::new, energy_terms, energy, submit
//!           (candidate, envelope, check_bounds, add), dispatch, acknowledge,
//!           cancel (release), settle, set_paused, observe, preview,
//!           best_quantity.
//!
//! Everything here is written from the brief, not from the core: the guard
//! order, the exact results and post-states, and the invariants. The core is
//! only ever *called* (in `apply`) and compared against it. Arithmetic is
//! exact (`Z`, `u128`, see [`Z`]): no checked, saturating or wrapping operation of the
//! code is reused, so the overflow behaviour of the code is checked against
//! the mathematical value, not against itself.
//!
//! Simplifications:
//! - At most [`M`] metrics (the harness bound is 2): value vectors are fixed
//!   arrays `[Z; M]` with the length taken from the configuration.
//! - `expected` needs no invariant: it is total on well-formed states (every
//!   record's recipe in range, values of length `n` and bounded), which every
//!   generated state is. Energy errors of the code are not modelled: on
//!   bounded values energy cannot fail (NUM-1, `h_energy`), and every
//!   energy evaluation of the code is on bounded values.

use pool_core::*;

/// Accounts: short distinct strings. 4 values realise every equality pattern
/// among the at most 3 role holders one step compares (owner, the touched
/// recipe's actor and executor) and the caller. They stand for the brief's
/// `o, a1, x1, z`; all four are 2 bytes long, because a symbolic choice among
/// strings of different lengths is a `String` of symbolic length, which CBMC
/// pays for at every clone and comparison (RESULTS.md, cost ladder). The core
/// only compares accounts for equality (and `validate` checks `1..=128`
/// bytes), so the names themselves carry no meaning.
pub const ACCTS: [&str; 4] = ["o_", "a1", "x1", "z_"];

/// Most metrics the spec's fixed arrays hold.
pub const M: usize = 2;

/// The spec's integers. `i64` with overflow checks on (Kani checks every
/// arithmetic overflow; plain mode runs with `overflow-checks = true`), so
/// spec arithmetic is exact: a wrap would be a failed check, never a silent
/// value. Every spec quantity fits by a wide margin: `|d·u| ≤ 1e6·100`,
/// envelope and ledger sums `≤ 1e6 + 256·1e8`, energy `≤ 64·1000·(2e6)²`
/// `= 2.56e17` (RESULTS.md, deviation 2: `i128` doubled every multiplier).
pub type Z = i64;
pub type Vals = [Z; M];

pub const MAXV: Z = 1_000_000;
pub const DAY: u128 = 86_400;

/// `d·u` for a delta `|d| ≤ 1e6` and units `u ≤ 100` (validated configs and
/// guarded units: every call site). The preconditions are asserted, so the
/// product (`|d·u| ≤ 1e8 < 2^31`) is exact in 32 bits; this keeps the
/// multiplier at a quarter of the 64-bit one with its overflow check.
pub fn mul_du(d: i64, u: u32) -> Z {
    assert!(-1_000_000 <= d && d <= 1_000_000 && u <= 100, "spec: |d| <= 1e6, u <= 100");
    (d as i32).wrapping_mul(u as i32) as Z
}

pub fn bounded(x: Z) -> bool {
    -MAXV <= x && x <= MAXV
}

pub fn short(s: &str) -> bool {
    !s.is_empty() && s.len() <= 128
}

/// Longest string the step harnesses compare (accounts are 2 bytes, other
/// names 1; `gen`).
pub const STR_MAX: usize = 2;

/// String equality. Plain mode: `==`. Under Kani, `==` on `str` is a
/// `memcmp` whose length CBMC cannot fold, and every byte it reads is a case
/// split over every string object of the state (17k clauses a byte; half the
/// clauses of a step harness, RESULTS.md cost ladder). So the lengths are
/// compared first and then at most `STR_MAX` bytes, which is the same
/// function on strings of at most `STR_MAX` bytes; a longer string fails
/// the harness on the assertion, it is never compared partially.
pub fn eq_str(a: &str, b: &str) -> bool {
    eq_text::<STR_MAX>(a, b)
}

/// [`eq_str`] for strings of at most `K` bytes under Kani. (`preview`'s
/// strings use [`Text`] and [`is_dec`], which read the heap string once.)
pub fn eq_text<const K: usize>(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    #[cfg(kani)]
    {
        kani::assert(a.len() <= K, "harness bound: strings within the compared length");
        let mut eq = true;
        for i in 0..K {
            if i < a.len() && a[i] != b[i] {
                eq = false;
            }
        }
        eq
    }
    #[cfg(not(kani))]
    {
        a == b
    }
}

/// `s == x.to_string()`: `s` is the canonical decimal numeral of `x`
/// (1 to 20 digits, no leading zero unless it is "0") and its value is `x`.
/// Under Kani `s` is parsed (multiplications by 10: shifts and adds) instead
/// of formatting `x` (a 64-bit division per digit pair); the canonical
/// numeral of a number is unique, so the two are equal.
pub fn is_dec(s: &str, x: u64) -> bool {
    #[cfg(kani)]
    {
        parse_dec(s, x)
    }
    #[cfg(not(kani))]
    {
        let r = s == x.to_string();
        assert!(parse_dec(s, x) == r, "spec: is_dec agrees with to_string");
        r
    }
}

fn parse_dec(s: &str, x: u64) -> bool {
    let t = Text::<24>::of(s);
    if t.len == 0 || t.len > 20 || (t.len > 1 && t.b[0] == b'0') {
        return false;
    }
    let mut digits = true;
    let mut n: u128 = 0;
    for i in 0..20 {
        if i < t.len {
            let d = t.b[i].wrapping_sub(b'0');
            if d > 9 {
                digits = false;
            }
            n = n * 10 + d as u128;
        }
    }
    digits && n == x as u128
}

/// A string of at most `K` bytes copied into a local array (under Kani each
/// byte of a heap string is read once, not once per comparison: a read is a
/// case split over every string object the pointer may refer to).
pub struct Text<const K: usize> {
    len: usize,
    b: [u8; K],
}

impl<const K: usize> Text<K> {
    pub fn of(s: &str) -> Self {
        let s = s.as_bytes();
        assert!(s.len() <= K, "harness bound: strings within the compared length");
        let mut b = [0u8; K];
        for i in 0..K {
            if i < s.len() {
                b[i] = s[i];
            }
        }
        Text { len: s.len(), b }
    }

    /// Equality with `t` (any length).
    pub fn eq(&self, t: &str) -> bool {
        let t = t.as_bytes();
        if t.len() != self.len {
            return false;
        }
        let mut eq = true;
        for i in 0..K {
            if i < t.len() && self.b[i] != t[i] {
                eq = false;
            }
        }
        eq
    }
}

/// `a == b` on `i64` vectors, element by element (`==` is a byte-wise
/// `memcmp` over the same imprecise pointers as [`eq_str`]).
pub fn eq_i64s(a: &[i64], b: &[i64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut eq = true;
    for i in 0..M + 2 {
        if i < a.len() && a[i] != b[i] {
            eq = false;
        }
    }
    assert!(a.len() <= M + 2, "spec: vectors of at most M + 2 values");
    eq
}

/// `a == b` on [`Vals`] (`==` on `[i64; M]` is a 16-byte `memcmp` loop).
pub fn eq_vals(a: &Vals, b: &Vals) -> bool {
    let mut eq = true;
    for i in 0..M {
        if a[i] != b[i] {
            eq = false;
        }
    }
    eq
}

/// `a == b` on configurations (field by field, with [`eq_str`]).
pub fn same_config(a: &Config, b: &Config) -> bool {
    let mut ok = eq_str(&a.name, &b.name)
        && eq_str(&a.owner, &b.owner)
        && a.max_age_seconds == b.max_age_seconds
        && a.metrics.len() == b.metrics.len()
        && a.terms.len() == b.terms.len()
        && a.recipes.len() == b.recipes.len()
        && a.terms == b.terms;
    if !ok {
        return false;
    }
    for (x, y) in a.metrics.iter().zip(&b.metrics) {
        if !(eq_str(&x.name, &y.name) && eq_str(&x.unit, &y.unit))
            || x.initial != y.initial
            || x.min != y.min
            || x.max != y.max
        {
            ok = false;
        }
    }
    for (x, y) in a.recipes.iter().zip(&b.recipes) {
        if !(eq_str(&x.name, &y.name) && eq_str(&x.actor, &y.actor) && eq_str(&x.executor, &y.executor))
            || !eq_i64s(&x.reserve, &y.reserve)
            || !eq_i64s(&x.complete, &y.complete)
            || x.max_units != y.max_units
            || x.requires != y.requires
        {
            ok = false;
        }
    }
    ok
}

/// `a == b` on everything a step may change. The configuration is compared
/// too in plain mode; under Kani it is left to the frame assertion of
/// [`post_matches`] (the `_post` parts prove that no step changes it), as
/// comparing it costs more than the step itself (RESULTS.md, cost ladder).
pub fn same_state(a: &Pool, b: &Pool) -> bool {
    #[cfg(not(kani))]
    if !same_config(&a.config, &b.config) {
        return false;
    }
    eq_i64s(&a.values, &b.values)
        && a.version == b.version
        && a.observed_at == b.observed_at
        && a.paused == b.paused
        && a.records == b.records
}

pub fn open(s: &Status) -> bool {
    !matches!(s, Status::Completed | Status::Cancelled)
}

pub fn terminal(s: &Status) -> bool {
    !open(s)
}

fn max0(x: Z) -> Z {
    if x > 0 {
        x
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

/// One public mutating call. Callers are drawn from [`ACCTS`].
#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    Submit {
        caller: &'static str,
        req: Request,
        now: u64,
    },
    Dispatch {
        caller: &'static str,
        id: u32,
        now: u64,
    },
    Ack {
        id: u32,
        accepted: bool,
    },
    Cancel {
        caller: &'static str,
        id: u32,
        now: u64,
    },
    Settle {
        caller: &'static str,
        id: u32,
        completed: bool,
    },
    Pause {
        caller: &'static str,
        paused: bool,
    },
    Observe {
        caller: &'static str,
        vals: Vec<i64>,
        now: u64,
    },
}

/// Result of an operation: `Ok(Some(id))` for submit, `Ok(None)` otherwise.
pub type Res = Result<Option<u32>, Error>;

/// Runs `op` through the real core.
pub fn apply(p: &mut Pool, op: &Op) -> Res {
    match op {
        Op::Submit { caller, req, now } => p.submit(caller, req.clone(), *now).map(Some),
        Op::Dispatch { caller, id, now } => p.dispatch(caller, *id, *now).map(|_| None),
        Op::Ack { id, accepted } => p.acknowledge(*id, *accepted).map(|_| None),
        Op::Cancel { caller, id, now } => p.cancel(caller, *id, *now).map(|_| None),
        Op::Settle {
            caller,
            id,
            completed,
        } => p.settle(caller, *id, *completed).map(|_| None),
        Op::Pause { caller, paused } => p.set_paused(caller, *paused).map(|_| None),
        Op::Observe { caller, vals, now } => p
            .observe(caller, crate::gen::copy_vec(vals, M + 1), *now)
            .map(|_| None),
    }
}

// ---------------------------------------------------------------------------
// Notation
// ---------------------------------------------------------------------------

/// `cfg.recipes[k]`, read over concrete slots. Every lookup by a symbolic
/// index goes through this or [`rec`]: an index into a heap buffer is a
/// symbolic byte offset, which CBMC encodes as a mux over every byte of the
/// buffer (RESULTS.md, deviation 3).
pub fn rcp(cfg: &Config, k: u32) -> Option<&Recipe> {
    let mut out = None;
    for (j, r) in cfg.recipes.iter().enumerate() {
        if j as u64 == k as u64 {
            out = Some(r);
        }
    }
    out
}

/// [`rcp`] for an index known to be in range (well-formed states).
pub fn rcp_of(cfg: &Config, k: u32) -> &Recipe {
    match rcp(cfg, k) {
        Some(r) => r,
        None => panic!("spec: recipe index in range"),
    }
}

/// `recs[id]`, read over concrete slots.
pub fn rec(recs: &[Commitment], id: u32) -> Option<&Commitment> {
    let mut out = None;
    for (j, c) in recs.iter().enumerate() {
        if j as u64 == id as u64 {
            out = Some(c);
        }
    }
    out
}

pub fn n(cfg: &Config) -> usize {
    cfg.metrics.len()
}

/// Values of a well-formed state as exact integers.
pub fn vals(cfg: &Config, v: &[i64]) -> Vals {
    let mut out = [0; M];
    let k = n(cfg);
    assert!(k <= M && v.len() == k, "spec: values of length n <= M");
    for i in 0..M {
        if i < k {
            out[i] = v[i] as Z;
        }
    }
    out
}

/// `PV_i(v) = max(0, min_i − v) + max(0, v − max_i)`.
pub fn pv(m: &Metric, v: Z) -> Z {
    max0(m.min as Z - v) + max0(v - m.max as Z)
}

/// Is any metric of `v` outside its `[min, max]`?
pub fn violating(cfg: &Config, v: &Vals) -> bool {
    let mut any = false;
    for i in 0..M {
        if i < n(cfg) && pv(&cfg.metrics[i], v[i]) > 0 {
            any = true;
        }
    }
    any
}

/// `base + d·u`, or `None` (Arithmetic) if some component leaves ±1e6.
pub fn add(cfg: &Config, base: &Vals, d: &[i64], u: u32) -> Option<Vals> {
    let mut out = [0; M];
    let mut ok = true;
    for i in 0..M {
        if i < n(cfg) {
            let x = base[i] + mul_du(d[i], u);
            if !bounded(x) {
                ok = false;
            }
            out[i] = x;
        }
    }
    if ok {
        Some(out)
    } else {
        None
    }
}

/// Envelope over open records (minus `skip`, plus `extra = (recipe, units)`):
/// `low_i = v_i + Σ min(0, complete_i·u)`, `high_i = v_i + Σ max(0, complete_i·u)`.
/// `None` (Arithmetic) if a final bound leaves ±1e6: the partial sums are
/// monotone from a bounded start, so this is the same as the code's check
/// after every record.
pub fn envelope(
    cfg: &Config,
    recs: &[Commitment],
    v: &Vals,
    extra: Option<(u32, u32)>,
    skip: Option<u32>,
) -> Option<(Vals, Vals)> {
    let mut lo = *v;
    let mut hi = *v;
    let k = n(cfg);
    for c in recs {
        if open(&c.status) && Some(c.id) != skip {
            let r = rcp_of(cfg, c.recipe);
            for i in 0..M {
                if i < k {
                    let d = mul_du(r.complete[i], c.units);
                    lo[i] += if d < 0 { d } else { 0 };
                    hi[i] += if d > 0 { d } else { 0 };
                }
            }
        }
    }
    if let Some((rid, u)) = extra {
        let r = rcp_of(cfg, rid);
        for i in 0..M {
            if i < k {
                let d = mul_du(r.complete[i], u);
                lo[i] += if d < 0 { d } else { 0 };
                hi[i] += if d > 0 { d } else { 0 };
            }
        }
    }
    for i in 0..M {
        if i < k && (!bounded(lo[i]) || !bounded(hi[i])) {
            return None;
        }
    }
    Some((lo, hi))
}

/// `EV_i = max(0, min_i − low_i) + max(0, high_i − max_i)`.
pub fn ev(m: &Metric, lo: Z, hi: Z) -> Z {
    max0(m.min as Z - lo) + max0(hi - m.max as Z)
}

/// Which guard decided a result: distinguishes the several `Arithmetic`,
/// `Bounds`, `Energy`, `InvalidState` and no-op sites for the covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// A plain guard, or an effective `Ok`.
    Plain,
    /// `add` left ±1e6.
    Add,
    /// The envelope left ±1e6.
    Envelope,
    /// The recovery `add(next, complete, units)` left ±1e6.
    RecoveryAdd,
    /// `version = u32::MAX`.
    Version,
    /// Energy increased (`after > before`).
    EnergyUp,
    /// Recovery rule: completion does not strictly decrease energy.
    Recovery,
    /// A no-op `Ok` (state unchanged, version included).
    Noop,
    /// settle: the opposite terminal status.
    Opposite,
    /// release (cancel or settle(false)).
    Release,
}

/// `check_bounds(next, extra, skip)` against the current values `cur`.
pub fn check_bounds(
    cfg: &Config,
    recs: &[Commitment],
    cur: &Vals,
    next: &Vals,
    extra: Option<(u32, u32)>,
    skip: Option<u32>,
) -> Result<(), (Error, Why)> {
    let Some((lo, hi)) = envelope(cfg, recs, next, extra, skip) else {
        return Err((Error::Arithmetic, Why::Envelope));
    };
    for i in 0..M {
        if i < n(cfg) {
            let m = &cfg.metrics[i];
            if ev(m, lo[i], hi[i]) > pv(m, cur[i]) {
                return Err((Error::Bounds, Why::Plain));
            }
        }
    }
    Ok(())
}

/// One energy term: `w·r²` with `r = |v − t|`, `max(0, v − t)` or `max(0, t − v)`.
pub fn term(t: &Term, v: Z) -> Z {
    let d = v - t.target as Z;
    let r = match t.shape {
        Shape::Target => {
            if d < 0 {
                -d
            } else {
                d
            }
        }
        Shape::Excess => max0(d),
        Shape::Deficit => max0(-d),
    };
    // `r ≤ 2e6 < 2^21` and `w ≤ 1000 < 2^10` (asserted), so `w·r² < 2^52`
    // is exact in 64 bits without an overflow-checked multiply.
    assert!(r <= 2_000_000 && t.weight <= 1000, "spec: r <= 2e6, w <= 1000");
    let r = r as u64;
    r.wrapping_mul(r).wrapping_mul(t.weight as u64) as Z
}

/// Energy: `Σ_terms w·r²`, exact.
pub fn energy(cfg: &Config, v: &Vals) -> Z {
    let mut e: Z = 0;
    for t in &cfg.terms {
        e += term(t, v[t.metric as usize]);
    }
    e
}

/// Units of Completed records of recipe `p` among `recs`.
pub fn completed_units(recs: &[Commitment], p: u32) -> u64 {
    let mut s = 0u64;
    for c in recs {
        if c.recipe == p && c.status == Status::Completed {
            s += c.units as u64;
        }
    }
    s
}

/// `true` iff every prerequisite of `r` is met by Completed units in `recs`.
pub fn prereqs_met(r: &Recipe, recs: &[Commitment]) -> bool {
    let mut ok = true;
    for (p, u) in &r.requires {
        if completed_units(recs, *p) < *u as u64 {
            ok = false;
        }
    }
    ok
}

/// `submit`'s admission (the code's private `candidate`): the reserved
/// values, or the first failing guard in code order.
pub fn candidate(p: &Pool, caller: &str, req: &Request, now: u64) -> Result<Vals, (Error, Why)> {
    let cfg = &p.config;
    let plain = |e| Err((e, Why::Plain));
    if p.paused {
        return plain(Error::Paused);
    }
    if req.version != p.version {
        return plain(Error::Stale);
    }
    // Exact sums: `now + 86400` and `observed_at + max_age` never wrap here.
    let now_x = now as u128;
    let exp_x = req.expires_at as u128;
    if exp_x <= now_x || exp_x > now_x + DAY {
        return plain(Error::Expired);
    }
    if cfg.max_age_seconds > 0 && now_x > p.observed_at as u128 + cfg.max_age_seconds as u128 {
        return plain(Error::SnapshotExpired);
    }
    if p.records.len() >= 256 {
        return plain(Error::Full);
    }
    let Some(r) = rcp(cfg, req.recipe) else {
        return plain(Error::InvalidRecipe);
    };
    if !eq_str(caller, &r.actor) {
        return plain(Error::Unauthorized);
    }
    if req.units == 0 || req.units > r.max_units {
        return plain(Error::InvalidUnits);
    }
    if !prereqs_met(r, &p.records) {
        return plain(Error::Prerequisite);
    }
    let v = vals(cfg, &p.values);
    let Some(next) = add(cfg, &v, &r.reserve, req.units) else {
        return Err((Error::Arithmetic, Why::Add));
    };
    check_bounds(cfg, &p.records, &v, &next, Some((req.recipe, req.units)), None)?;
    let before = energy(cfg, &v);
    if energy(cfg, &next) > before {
        return Err((Error::Energy, Why::EnergyUp));
    }
    if violating(cfg, &v) {
        let Some(done) = add(cfg, &next, &r.complete, req.units) else {
            return Err((Error::Arithmetic, Why::RecoveryAdd));
        };
        if energy(cfg, &done) >= before {
            return Err((Error::Energy, Why::Recovery));
        }
    }
    Ok(next)
}

// ---------------------------------------------------------------------------
// Expected result and post-state
// ---------------------------------------------------------------------------

/// The expected outcome of one operation from a well-formed pre-state.
#[derive(Clone, Debug, PartialEq)]
pub struct Exp {
    pub res: Res,
    pub why: Why,
    /// Post-state (equal to the pre-state unless `res` is an effective `Ok`).
    pub values: Vals,
    pub version: u32,
    pub observed_at: u64,
    pub paused: bool,
    /// A record appended (submit).
    pub push: Option<Commitment>,
    /// A record whose status changes.
    pub status: Option<(u32, Status)>,
}

impl Exp {
    fn unchanged(p: &Pool, res: Res, why: Why) -> Exp {
        Exp {
            res,
            why,
            values: vals(&p.config, &p.values),
            version: p.version,
            observed_at: p.observed_at,
            paused: p.paused,
            push: None,
            status: None,
        }
    }
    fn err(p: &Pool, e: Error) -> Exp {
        Exp::unchanged(p, Err(e), Why::Plain)
    }
    fn err_at(p: &Pool, (e, why): (Error, Why)) -> Exp {
        Exp::unchanged(p, Err(e), why)
    }
    /// An `Ok` that changes nothing, version included (TX-NOOP).
    pub fn noop(&self) -> bool {
        self.res.is_ok() && self.why == Why::Noop
    }
    /// An `Ok` that is not a no-op: increments the version (TX-VER).
    pub fn effective(&self) -> bool {
        self.res.is_ok() && self.why != Why::Noop
    }
}

/// `release(id)`: undo the reservation, check bounds without `id`, bump.
fn release(p: &Pool, id: u32) -> Exp {
    let cfg = &p.config;
    let c = rec(&p.records, id).expect("spec: release of an existing record");
    let r = rcp_of(cfg, c.recipe);
    let v = vals(cfg, &p.values);
    let mut next = [0; M];
    for i in 0..M {
        if i < n(cfg) {
            next[i] = v[i] - mul_du(r.reserve[i], c.units);
            if !bounded(next[i]) {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Add);
            }
        }
    }
    if let Err(e) = check_bounds(cfg, &p.records, &v, &next, None, Some(id)) {
        return Exp::err_at(p, e);
    }
    if p.version == u32::MAX {
        return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
    }
    let mut x = Exp::unchanged(p, Ok(None), Why::Release);
    x.values = next;
    x.version = p.version + 1;
    x.status = Some((id, Status::Cancelled));
    x
}

/// The exact result in guard order and the exact post-state of `op` from `p`.
pub fn expected(p: &Pool, op: &Op) -> Exp {
    let cfg = &p.config;
    let nrec = p.records.len();
    match op {
        Op::Submit { caller, req, now } => match candidate(p, caller, req, *now) {
            Err(e) => Exp::err_at(p, e),
            Ok(next) => {
                if p.version == u32::MAX {
                    return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
                }
                let mut x = Exp::unchanged(p, Ok(Some(nrec as u32)), Why::Plain);
                x.values = next;
                x.version = p.version + 1;
                x.push = Some(Commitment {
                    id: nrec as u32,
                    recipe: req.recipe,
                    units: req.units,
                    expires_at: req.expires_at,
                    status: Status::Reserved,
                });
                x
            }
        },
        Op::Dispatch { caller, id, now } => {
            let Some(c) = rec(&p.records, *id) else {
                return Exp::err(p, Error::NotFound);
            };
            let r = rcp_of(cfg, c.recipe);
            if !eq_str(caller, &r.actor) {
                return Exp::err(p, Error::Unauthorized);
            }
            if p.paused {
                return Exp::err(p, Error::Paused);
            }
            if c.status != Status::Reserved {
                return Exp::err(p, Error::InvalidState);
            }
            if *now >= c.expires_at {
                return Exp::err(p, Error::Expired);
            }
            if cfg.max_age_seconds > 0
                && *now as u128 > p.observed_at as u128 + cfg.max_age_seconds as u128
            {
                return Exp::err(p, Error::SnapshotExpired);
            }
            if p.version == u32::MAX {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
            }
            let mut x = Exp::unchanged(p, Ok(None), Why::Plain);
            x.version = p.version + 1;
            x.status = Some((*id, Status::Dispatched));
            x
        }
        Op::Ack { id, accepted } => {
            let Some(c) = rec(&p.records, *id) else {
                return Exp::err(p, Error::NotFound);
            };
            let s = &c.status;
            if !matches!(s, Status::Dispatched | Status::Unknown) {
                return Exp::unchanged(p, Ok(None), Why::Noop);
            }
            let next = if *accepted {
                Status::Active
            } else {
                Status::Unknown
            };
            if *s == next {
                return Exp::unchanged(p, Ok(None), Why::Noop);
            }
            if p.version == u32::MAX {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
            }
            let mut x = Exp::unchanged(p, Ok(None), Why::Plain);
            x.version = p.version + 1;
            x.status = Some((*id, next));
            x
        }
        Op::Cancel { caller, id, .. } => {
            let Some(c) = rec(&p.records, *id) else {
                return Exp::err(p, Error::NotFound);
            };
            let r = rcp_of(cfg, c.recipe);
            if !eq_str(caller, &r.actor) && !eq_str(caller, &cfg.owner) {
                return Exp::err(p, Error::Unauthorized);
            }
            if c.status == Status::Cancelled {
                return Exp::unchanged(p, Ok(None), Why::Noop);
            }
            if c.status != Status::Reserved {
                return Exp::err(p, Error::Pending);
            }
            release(p, *id)
        }
        Op::Settle {
            caller,
            id,
            completed,
        } => {
            let Some(c) = rec(&p.records, *id) else {
                return Exp::err(p, Error::NotFound);
            };
            let r = rcp_of(cfg, c.recipe);
            if !eq_str(caller, &r.executor) {
                return Exp::err(p, Error::Unauthorized);
            }
            if (*completed && c.status == Status::Completed)
                || (!*completed && c.status == Status::Cancelled)
            {
                return Exp::unchanged(p, Ok(None), Why::Noop);
            }
            if !matches!(
                c.status,
                Status::Dispatched | Status::Active | Status::Unknown
            ) {
                let why = if terminal(&c.status) {
                    Why::Opposite
                } else {
                    Why::Plain
                };
                return Exp::unchanged(p, Err(Error::InvalidState), why);
            }
            if !*completed {
                return release(p, *id);
            }
            let v = vals(cfg, &p.values);
            let Some(next) = add(cfg, &v, &r.complete, c.units) else {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Add);
            };
            if let Err(e) = check_bounds(cfg, &p.records, &v, &next, None, Some(*id)) {
                return Exp::err_at(p, e);
            }
            if p.version == u32::MAX {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
            }
            let mut x = Exp::unchanged(p, Ok(None), Why::Plain);
            x.values = next;
            x.version = p.version + 1;
            x.status = Some((*id, Status::Completed));
            x
        }
        Op::Pause { caller, paused } => {
            if !eq_str(caller, &cfg.owner) {
                return Exp::err(p, Error::Unauthorized);
            }
            if p.version == u32::MAX {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
            }
            let mut x = Exp::unchanged(p, Ok(None), Why::Plain);
            x.version = p.version + 1;
            x.paused = *paused;
            x
        }
        Op::Observe { caller, vals: obs, now } => {
            if !eq_str(caller, &cfg.owner) {
                return Exp::err(p, Error::Unauthorized);
            }
            let mut any_open = false;
            for c in &p.records {
                if open(&c.status) {
                    any_open = true;
                }
            }
            if any_open {
                return Exp::err(p, Error::Pending);
            }
            if obs.len() != n(cfg) {
                return Exp::err(p, Error::Bounds);
            }
            let mut ok = true;
            for x in obs {
                if !bounded(*x as Z) {
                    ok = false;
                }
            }
            if !ok {
                return Exp::err(p, Error::Bounds);
            }
            if p.version == u32::MAX {
                return Exp::unchanged(p, Err(Error::Arithmetic), Why::Version);
            }
            let mut x = Exp::unchanged(p, Ok(None), Why::Plain);
            x.values = vals(cfg, obs);
            x.version = p.version + 1;
            x.observed_at = *now;
            x
        }
    }
}

/// The status of record `j` after `x` (from `pre`).
pub fn exp_status(pre: &Pool, x: &Exp, j: usize) -> Status {
    match &x.status {
        Some((id, s)) if *id as usize == j => s.clone(),
        _ => pre.records[j].status.clone(),
    }
}

/// TX-*: `post` is exactly the expected post-state: config, values, version,
/// observed_at, paused and records (frame: every other record unchanged).
pub fn post_matches(pre: &Pool, post: &Pool, x: &Exp) -> bool {
    let cfg = &pre.config;
    let mut ok = same_config(&post.config, &pre.config)
        && post.values.len() == n(cfg)
        && post.version == x.version
        && post.observed_at == x.observed_at
        && post.paused == x.paused;
    for i in 0..M {
        if i < n(cfg) && i < post.values.len() && post.values[i] as Z != x.values[i] {
            ok = false;
        }
    }
    let k = pre.records.len();
    let k2 = k + x.push.is_some() as usize;
    if post.records.len() != k2 {
        return false;
    }
    for j in 0..k {
        let a = &pre.records[j];
        let b = &post.records[j];
        if b.id != a.id
            || b.recipe != a.recipe
            || b.units != a.units
            || b.expires_at != a.expires_at
            || b.status != exp_status(pre, x, j)
        {
            ok = false;
        }
    }
    if let Some(c) = &x.push {
        if rec(&post.records, k as u32) != Some(c) {
            ok = false;
        }
    }
    ok
}

// ---------------------------------------------------------------------------
// Lifecycle (LIFE-1)
// ---------------------------------------------------------------------------

/// LIFE-1: the allowed one-step status changes (or none).
pub fn life_step(a: &Status, b: &Status) -> bool {
    use Status::*;
    a == b
        || matches!(
            (a, b),
            (Reserved, Dispatched)
                | (Reserved, Cancelled)
                | (Dispatched, Active)
                | (Dispatched, Unknown)
                | (Unknown, Active)
                | (Dispatched, Completed)
                | (Dispatched, Cancelled)
                | (Active, Completed)
                | (Active, Cancelled)
                | (Unknown, Completed)
                | (Unknown, Cancelled)
        )
}

// ---------------------------------------------------------------------------
// Invariants and ghost
// ---------------------------------------------------------------------------

/// Ghost state: the values and record count at the last `observe` (or
/// `new`), and the number of effective transitions (INV-VER; tracked from
/// `Init` only, `None` in step harnesses).
#[derive(Clone, Debug, PartialEq)]
pub struct Ghost {
    pub base: Vec<i64>,
    pub k0: u32,
    pub eff: Option<u32>,
}

impl Ghost {
    pub fn init(p: &Pool) -> Ghost {
        Ghost {
            base: crate::gen::copy_vec(&p.values, M + 1),
            k0: 0,
            eff: Some(0),
        }
    }
}

/// The ghost after `op` with expected outcome `x` from `pre`.
pub fn ghost_step(g: &Ghost, pre: &Pool, op: &Op, x: &Exp) -> Ghost {
    let mut h = Ghost {
        base: crate::gen::copy_vec(&g.base, M + 1),
        k0: g.k0,
        eff: g.eff,
    };
    if let (Op::Observe { vals, .. }, Ok(_)) = (op, &x.res) {
        h.base = crate::gen::copy_vec(vals, M + 1);
        h.k0 = pre.records.len() as u32;
    }
    if x.effective() {
        h.eff = g.eff.map(|e| e + 1);
    }
    h
}

/// `B_i = PV_i(base)`.
pub fn b_of(cfg: &Config, g: &Ghost) -> Vals {
    let b = vals(cfg, &g.base);
    let mut out = [0; M];
    for i in 0..M {
        if i < n(cfg) {
            out[i] = pv(&cfg.metrics[i], b[i]);
        }
    }
    out
}

/// `B = 0`: the base at the last observation is inside every `[min, max]`.
pub fn healthy_base(cfg: &Config, g: &Ghost) -> bool {
    let b = b_of(cfg, g);
    let mut ok = true;
    for i in 0..M {
        if i < n(cfg) && b[i] != 0 {
            ok = false;
        }
    }
    ok
}

/// CFG-1/CFG-2: `validate`, written from the brief.
pub fn valid(cfg: &Config) -> bool {
    let k = cfg.metrics.len();
    if !short(&cfg.name)
        || !short(&cfg.owner)
        || k == 0
        || k > 32
        || cfg.recipes.is_empty()
        || cfg.recipes.len() > 32
        || cfg.terms.is_empty()
        || cfg.terms.len() > 64
    {
        return false;
    }
    let mut ok = true;
    for m in &cfg.metrics {
        let (lo, hi, x) = (m.min as Z, m.max as Z, m.initial as Z);
        if !short(&m.name) || !short(&m.unit) || !bounded(lo) || !bounded(hi) || !(lo <= x && x <= hi) {
            ok = false;
        }
    }
    for t in &cfg.terms {
        if t.metric as usize >= k || !bounded(t.target as Z) || !(1..=1000).contains(&t.weight) {
            ok = false;
        }
    }
    for (i, r) in cfg.recipes.iter().enumerate() {
        if !short(&r.name)
            || !short(&r.actor)
            || !short(&r.executor)
            || r.reserve.len() != k
            || r.complete.len() != k
            || !(1..=100).contains(&r.max_units)
            || r.requires.len() > 32
        {
            ok = false;
        }
        // Two loops, not one over the chain: each stays within the harness
        // unwind (vectors of at most 3 values in raw configurations).
        for x in r.reserve.iter() {
            if !bounded(*x as Z) {
                ok = false;
            }
        }
        for x in r.complete.iter() {
            if !bounded(*x as Z) {
                ok = false;
            }
        }
        for (j, (p, u)) in r.requires.iter().enumerate() {
            if *p as usize >= i || !(1..=100).contains(u) {
                ok = false;
            }
            for (q, _) in &r.requires[..j] {
                if q == p {
                    ok = false;
                }
            }
        }
    }
    ok
}

/// INV-WF (the parts not fixed by construction): values of length `n` and
/// bounded; `records[j].id = j`; recipe in range; `1 ≤ units ≤ max_units`;
/// at most 256 records; ghost well-formed (`k0 ≤ #records`, base of length
/// `n` and bounded, every record before `k0` terminal).
pub fn inv_wf(p: &Pool, g: &Ghost) -> bool {
    let cfg = &p.config;
    let k = n(cfg);
    if k > M || p.values.len() != k || g.base.len() != k || p.records.len() > 256 {
        return false;
    }
    let mut ok = g.k0 as usize <= p.records.len();
    for i in 0..M {
        if i < k && (!bounded(p.values[i] as Z) || !bounded(g.base[i] as Z)) {
            ok = false;
        }
    }
    for (j, c) in p.records.iter().enumerate() {
        if c.id as usize != j || c.recipe as usize >= cfg.recipes.len() {
            ok = false;
        } else {
            let r = rcp_of(cfg, c.recipe);
            if c.units == 0 || c.units > r.max_units {
                ok = false;
            }
        }
        if j < g.k0 as usize && open(&c.status) {
            ok = false;
        }
    }
    ok
}

/// `base + Σ_{j ≥ k0, ¬Cancelled} reserve_j·u_j + Σ_{j ≥ k0, Completed} complete_j·u_j`.
pub fn ledger(cfg: &Config, base: &[i64], recs: &[Commitment], k0: u32) -> Vals {
    let mut v = vals(cfg, base);
    for c in recs {
        if c.id >= k0 && c.status != Status::Cancelled {
            let r = rcp_of(cfg, c.recipe);
            for i in 0..M {
                if i < n(cfg) {
                    v[i] += mul_du(r.reserve[i], c.units);
                    if c.status == Status::Completed {
                        v[i] += mul_du(r.complete[i], c.units);
                    }
                }
            }
        }
    }
    v
}

/// INV-LEDGER (needs INV-WF).
pub fn inv_ledger(p: &Pool, g: &Ghost) -> bool {
    let cfg = &p.config;
    let l = ledger(cfg, &g.base, &p.records, g.k0);
    let v = vals(cfg, &p.values);
    let mut ok = true;
    for i in 0..M {
        if i < n(cfg) && l[i] != v[i] {
            ok = false;
        }
    }
    ok
}

/// INV-HARD (needs INV-WF): the envelope over open records is computable and
/// `EV_i ≤ B_i`.
pub fn inv_hard(p: &Pool, g: &Ghost) -> bool {
    let cfg = &p.config;
    let v = vals(cfg, &p.values);
    let Some((lo, hi)) = envelope(cfg, &p.records, &v, None, None) else {
        return false;
    };
    let b = b_of(cfg, g);
    let mut ok = true;
    for i in 0..M {
        if i < n(cfg) && ev(&cfg.metrics[i], lo[i], hi[i]) > b[i] {
            ok = false;
        }
    }
    ok
}

/// INV-HEALTHY (corollary of INV-HARD): with `B = 0`, every subset of the
/// open records' completions lands inside every `[min, max]`.
pub fn inv_healthy(p: &Pool, g: &Ghost) -> bool {
    let cfg = &p.config;
    if !healthy_base(cfg, g) {
        return true;
    }
    let v = vals(cfg, &p.values);
    let k = p.records.len();
    // Each slot's completion, read once (the harness bound is 3 records,
    // plus one push): reading the records and recipes inside the subset
    // loop below costs 16 times as many heap reads (RESULTS.md, cost ladder).
    let mut live = [false; 4];
    let mut d = [[0 as Z; M]; 4];
    for j in 0..4 {
        if j < k && open(&p.records[j].status) {
            let c = &p.records[j];
            let r = rcp_of(cfg, c.recipe);
            live[j] = true;
            for i in 0..M {
                if i < n(cfg) {
                    d[j][i] = mul_du(r.complete[i], c.units);
                }
            }
        }
    }
    let mut ok = true;
    // Subsets of the 4 slots, as four 2-iteration loops so every loop stays
    // within the harness unwind. A subset with a closed or missing slot is
    // not a subset of the open records and is skipped.
    for b0 in 0..2u32 {
    for b1 in 0..2u32 {
    for b2 in 0..2u32 {
    for b3 in 0..2u32 {
        let mask = b0 | (b1 << 1) | (b2 << 2) | (b3 << 3);
        let mut x = v;
        let mut subset = true;
        for j in 0..4 {
            if mask & (1 << j) != 0 {
                if !live[j] {
                    subset = false;
                } else {
                    for i in 0..M {
                        x[i] += d[j][i];
                    }
                }
            }
        }
        if subset {
            for i in 0..M {
                if i < n(cfg) && pv(&cfg.metrics[i], x[i]) != 0 {
                    ok = false;
                }
            }
        }
    }
    }
    }
    }
    ok
}

/// INV-DEP: every record's prerequisites are met by Completed records of
/// lower index.
pub fn inv_dep(p: &Pool) -> bool {
    let cfg = &p.config;
    let mut ok = true;
    for (j, c) in p.records.iter().enumerate() {
        let r = rcp_of(cfg, c.recipe);
        if !prereqs_met(r, &p.records[..j]) {
            ok = false;
        }
    }
    ok
}

/// INV-VER: version = number of effective transitions (from `Init` only).
pub fn inv_ver(p: &Pool, g: &Ghost) -> bool {
    match g.eff {
        Some(e) => p.version == e,
        None => true,
    }
}

/// The whole invariant (with the configuration's validity, CFG).
pub fn inv(p: &Pool, g: &Ghost) -> bool {
    valid(&p.config) && inv_wf(p, g) && inv_ledger(p, g) && inv_hard(p, g) && inv_dep(p) && inv_ver(p, g)
}

/// Debug name of an error (`preview`'s reason), written out.
pub fn reason(e: &Error) -> &'static str {
    match e {
        Error::InvalidConfig => "InvalidConfig",
        Error::Unauthorized => "Unauthorized",
        Error::Paused => "Paused",
        Error::Stale => "Stale",
        Error::Expired => "Expired",
        Error::SnapshotExpired => "SnapshotExpired",
        Error::InvalidRecipe => "InvalidRecipe",
        Error::InvalidUnits => "InvalidUnits",
        Error::Prerequisite => "Prerequisite",
        Error::Full => "Full",
        Error::Arithmetic => "Arithmetic",
        Error::Bounds => "Bounds",
        Error::Energy => "Energy",
        Error::InvalidState => "InvalidState",
        Error::NotFound => "NotFound",
        Error::Pending => "Pending",
    }
}
