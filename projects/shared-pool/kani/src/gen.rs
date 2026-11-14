//! Bounded state and operation builders.
//!
//! Bounds (RESULTS.md, "Bounds"): at most 2 metrics, 2 terms, 2 recipes and
//! 3 records; accounts from [`ACCTS`]; values from the harness's [`Dom`].
//! Times, versions, ids, request recipes and units are free (`u64`/`u32`);
//! they are only compared, so leaving them free costs little.
//!
//! `inv_state` builds a state together with its ghost `(base, k0)` and fixes
//! the values by INV-LEDGER (`values = ledger(base, records, k0)`): under
//! the assumption `inv` this loses nothing, and it is far cheaper than
//! drawing the values and assuming the equation. `raw_config` builds any
//! configuration of bounded size (for `validate` and `new`).

use crate::spec::{self, Ghost, Op, ACCTS};
use crate::src::{assume, Cfg, Dom, Src};
use pool_core::*;

pub const MAX_M: u8 = 2;
pub const MAX_T: u8 = 2;
pub const MAX_R: u8 = 2;
pub const MAX_C: u8 = 3;

pub fn acct(src: &mut impl Src) -> &'static str {
    match src.below(4) {
        0 => ACCTS[0],
        1 => ACCTS[1],
        2 => ACCTS[2],
        _ => ACCTS[3],
    }
}

/// A value from the domain `d` (always within ±1e6).
pub fn val(src: &mut impl Src, d: Dom) -> i64 {
    match d {
        Dom::Small(k) => src.range(-k, k),
        Dom::Anchored(k) => {
            let a = match src.anchor() {
                0 => -1_000_000,
                1 => 0,
                _ => 1_000_000,
            };
            let v = a + src.range(-k, k);
            if v > 1_000_000 {
                1_000_000
            } else if v < -1_000_000 {
                -1_000_000
            } else {
                v
            }
        }
        Dom::Full => src.range(-1_000_000, 1_000_000),
    }
}

/// A weight: any `1..=1000`, or one of `{1, 2, 1000}`.
pub fn weight(src: &mut impl Src, any: bool) -> u32 {
    if any {
        1 + src.below(1000)
    } else {
        match src.below(3) {
            0 => 1,
            1 => 2,
            _ => 1000,
        }
    }
}

pub fn shape_of(src: &mut impl Src) -> Shape {
    match src.below(3) {
        0 => Shape::Target,
        1 => Shape::Excess,
        _ => Shape::Deficit,
    }
}

pub fn status(src: &mut impl Src) -> Status {
    match src.below(6) {
        0 => Status::Reserved,
        1 => Status::Dispatched,
        2 => Status::Active,
        3 => Status::Unknown,
        4 => Status::Completed,
        _ => Status::Cancelled,
    }
}

fn size(src: &mut impl Src, fixed: Option<u8>, max: u8, min: u8) -> usize {
    match fixed {
        Some(k) => k as usize,
        None => (min as u32 + src.below((max - min) as u32 + 1)) as usize,
    }
}

/// A valid configuration within the bounds (CFG holds by construction;
/// `h_init` and `h_validate` cover arbitrary ones).
pub fn config(src: &mut impl Src, c: &Cfg) -> Config {
    let nm = size(src, c.shape.metrics, MAX_M, 1);
    let nt = size(src, c.shape.terms, MAX_T, 1);
    let nr = size(src, c.shape.recipes, MAX_R, 1);
    let mut metrics = Vec::with_capacity(MAX_M as usize);
    for i in 0..MAX_M as usize {
        if i < nm {
            let lo = val(src, c.val);
            let hi = val(src, c.val);
            let lo2 = if lo <= hi { lo } else { hi };
            let hi2 = if lo <= hi { hi } else { lo };
            metrics.push(Metric {
                name: "m".into(),
                unit: "u".into(),
                // Only `new` reads `initial`; see `init_config` for that case.
                initial: lo2,
                min: lo2,
                max: hi2,
            });
        }
    }
    let mut terms = Vec::with_capacity(MAX_T as usize);
    for i in 0..MAX_T as usize {
        if i < nt {
            terms.push(Term {
                metric: src.below(nm as u32),
                target: val(src, c.val),
                weight: weight(src, c.any_weight),
                shape: shape_of(src),
            });
        }
    }
    let mut recipes = Vec::with_capacity(MAX_R as usize);
    for i in 0..MAX_R as usize {
        if i < nr {
            let mut reserve = Vec::with_capacity(MAX_M as usize);
            let mut complete = Vec::with_capacity(MAX_M as usize);
            for k in 0..MAX_M as usize {
                if k < nm {
                    reserve.push(val(src, c.delta));
                    complete.push(val(src, c.delta));
                }
            }
            let mut requires = Vec::with_capacity(1);
            if i > 0 && src.bool() {
                let p = src.below(i as u32);
                let cap = if src.hint(70) { 4 } else { 100 };
                requires.push((p, 1 + src.below(cap)));
            }
            recipes.push(Recipe {
                name: "r".into(),
                actor: acct(src).into(),
                executor: acct(src).into(),
                reserve,
                complete,
                max_units: 1 + src.below(c.max_units),
                requires,
            });
        }
    }
    let max_age_seconds = if src.hint(50) { 0 } else { src.u32() };
    Config {
        name: "p".into(),
        owner: acct(src).into(),
        metrics,
        terms,
        recipes,
        max_age_seconds,
    }
}

/// `Pool::new(cfg, 0)` for a valid `cfg` (its `Ok` value by CFG-1), without
/// the validation.
pub fn pool_of(cfg: Config) -> Pool {
    let mut values = Vec::with_capacity(MAX_M as usize);
    for i in 0..MAX_M as usize {
        if i < cfg.metrics.len() {
            values.push(cfg.metrics[i].initial);
        }
    }
    Pool {
        config: cfg,
        values,
        version: 0,
        observed_at: 0,
        paused: false,
        records: Vec::new(),
    }
}

/// A valid configuration whose initial values are free within `[min, max]`.
pub fn init_config(src: &mut impl Src, c: &Cfg) -> Config {
    let mut cfg = config(src, c);
    for m in cfg.metrics.iter_mut() {
        let x = val(src, c.val);
        let x = if x < m.min {
            m.min
        } else if x > m.max {
            m.max
        } else {
            x
        };
        m.initial = x;
    }
    cfg
}

/// The records and ghost of a generated state: `nc` records, the first `k0`
/// terminal; values by INV-LEDGER. `None` if the values leave ±1e6.
pub fn state_from(src: &mut impl Src, c: &Cfg, cfg: Config) -> Option<(Pool, Ghost)> {
    let nm = cfg.metrics.len();
    let nr = cfg.recipes.len() as u32;
    let mut base = Vec::with_capacity(MAX_M as usize);
    for i in 0..MAX_M as usize {
        if i < nm {
            base.push(val(src, c.val));
        }
    }
    let nc = size(src, c.shape.records, MAX_C, 0);
    let k0 = src.below(nc as u32 + 1);
    // All MAX_C records are written at concrete offsets, then truncated: a
    // conditional push writes at a symbolic offset (RESULTS.md, deviation 3).
    let mut records = Vec::with_capacity(MAX_C as usize + 1);
    for j in 0..MAX_C as usize {
        let recipe = src.below(nr);
        let units = 1 + src.below(spec::rcp_of(&cfg, recipe).max_units);
        let st = if (j as u32) < k0 {
            if src.bool() {
                Status::Completed
            } else {
                Status::Cancelled
            }
        } else {
            status(src)
        };
        records.push(Commitment {
            id: j as u32,
            recipe,
            units,
            expires_at: src.u64(),
            status: st,
        });
    }
    records.truncate(nc);
    let l = spec::ledger(&cfg, &base, &records, k0);
    let mut values = Vec::with_capacity(MAX_M as usize);
    for i in 0..MAX_M as usize {
        if i < nm {
            if !assume(spec::bounded(l[i])) {
                return None;
            }
            values.push(l[i] as i64);
        }
    }
    let g = Ghost {
        base,
        k0,
        eff: None,
    };
    let p = Pool {
        config: cfg,
        values,
        version: if c.version_max { u32::MAX } else { src.u32() },
        observed_at: src.u64(),
        paused: src.bool(),
        records,
    };
    Some((p, g))
}

/// An INV state within the bounds, with its ghost: in plain mode often a
/// random-walk state from `Pool::new`; otherwise built and filtered by
/// `assume(inv)`.
pub fn inv_state(src: &mut impl Src, c: &Cfg) -> Option<(Pool, Ghost)> {
    if !c.version_max {
        if let Some((p, mut g)) = src.reach() {
            g.eff = None;
            return Some((p, g));
        }
    }
    let cfg = config(src, c);
    let (p, g) = state_from(src, c, cfg)?;
    // INV-WF and INV-LEDGER hold by construction; the rest is assumed.
    if !assume(spec::inv_hard(&p, &g)) || !assume(spec::inv_dep(&p)) {
        return None;
    }
    #[cfg(not(kani))]
    assert!(spec::inv(&p, &g), "gen: state is not INV");
    Some((p, g))
}

// ---------------------------------------------------------------------------
// Fixed-capacity copies
// ---------------------------------------------------------------------------

/// `v.clone()` into a buffer of capacity `cap` (≥ `v.len()` at every call
/// site). `Clone` allocates exactly `len`, and a symbolic `len` is an
/// allocation of symbolic size, which CBMC encodes with the array theory at
/// every later read and write (RESULTS.md, cost ladder). Same value as
/// `clone`; only the capacity differs, and `Pool`'s equality ignores it.
pub fn copy_vec<T: Clone>(v: &[T], cap: usize) -> Vec<T> {
    let mut out = Vec::with_capacity(cap);
    for x in v {
        out.push(x.clone());
    }
    out
}

/// `cfg.clone()` with fixed capacities (see [`copy_vec`]).
pub fn copy_config(cfg: &Config) -> Config {
    let mut recipes = Vec::with_capacity(MAX_R as usize + 1);
    for r in &cfg.recipes {
        recipes.push(Recipe {
            name: r.name.clone(),
            actor: r.actor.clone(),
            executor: r.executor.clone(),
            reserve: copy_vec(&r.reserve, MAX_M as usize + 1),
            complete: copy_vec(&r.complete, MAX_M as usize + 1),
            max_units: r.max_units,
            requires: copy_vec(&r.requires, 2),
        });
    }
    Config {
        name: cfg.name.clone(),
        owner: cfg.owner.clone(),
        metrics: copy_vec(&cfg.metrics, MAX_M as usize + 1),
        terms: copy_vec(&cfg.terms, MAX_T as usize + 1),
        recipes,
        max_age_seconds: cfg.max_age_seconds,
    }
}

/// `p.clone()` with fixed capacities; `cap` bounds the record count.
pub fn copy_pool(p: &Pool, cap: usize) -> Pool {
    Pool {
        config: copy_config(&p.config),
        values: copy_vec(&p.values, MAX_M as usize + 1),
        version: p.version,
        observed_at: p.observed_at,
        paused: p.paused,
        records: copy_vec(&p.records, cap),
    }
}

/// [`copy_pool`] for the generated states (at most `MAX_C` records, plus
/// one push).
pub fn copy(p: &Pool) -> Pool {
    copy_pool(p, MAX_C as usize + 1)
}

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

pub const SUBMIT: u32 = 0;
pub const DISPATCH: u32 = 1;
pub const ACK: u32 = 2;
pub const CANCEL: u32 = 3;
pub const SETTLE: u32 = 4;
pub const PAUSE: u32 = 5;
pub const OBSERVE: u32 = 6;
pub const KINDS: u32 = 7;

/// A time: free, or (plain mode) near `observed_at` / an expiry.
fn time(src: &mut impl Src, p: &Pool) -> u64 {
    if src.hint(70) {
        p.observed_at.saturating_add(src.below(3) as u64)
    } else {
        src.u64()
    }
}

/// A record id: one that exists (plain mode, mostly), any `u32` (plain
/// mode), or one in `0..8` (Kani: at most 4 records, so `4..8` are the
/// NotFound ids).
fn id(src: &mut impl Src, p: &Pool) -> u32 {
    if !p.records.is_empty() && src.hint(85) {
        src.below(p.records.len() as u32)
    } else if src.wide() {
        src.u32()
    } else {
        src.below(8)
    }
}

/// A caller: any account, or (plain mode) the role `want`.
fn caller(src: &mut impl Src, want: &str) -> &'static str {
    for a in ACCTS {
        if a == want {
            return a;
        }
    }
    acct(src)
}

fn record_role<'a>(p: &'a Pool, id: u32, executor: bool) -> &'a str {
    match spec::rec(&p.records, id) {
        Some(c) => {
            let r = spec::rcp_of(&p.config, c.recipe);
            if executor {
                &r.executor
            } else {
                &r.actor
            }
        }
        None => "",
    }
}

/// An operation of kind `k` (one of the constants above) with free
/// arguments (Kani) or arguments steered toward passing guards (plain).
pub fn op(src: &mut impl Src, p: &Pool, k: u32, d: Dom) -> Op {
    match k {
        SUBMIT => {
            // Kani: recipe in 0..4 (2 recipes, so 2 and 3 are InvalidRecipe).
            let recipe = if src.hint(90) {
                src.below(p.config.recipes.len() as u32)
            } else if src.wide() {
                src.u32()
            } else {
                src.below(4)
            };
            let caller = if src.hint(70) {
                let actor = spec::rcp(&p.config, recipe).map(|r| r.actor.clone()).unwrap_or_default();
                caller(src, &actor)
            } else {
                acct(src)
            };
            let now = time(src, p);
            // Kani: units in 0..8 (max_units <= 3, so 0 and 4..8 are
            // InvalidUnits; units reach arithmetic only after that guard).
            let units = if src.hint(80) {
                1 + src.below(3)
            } else if src.wide() {
                src.u32()
            } else {
                src.below(8)
            };
            let version = if src.hint(85) { p.version } else { src.u32() };
            let expires_at = if src.hint(80) {
                now.saturating_add(1 + src.below(86_400) as u64)
            } else {
                src.u64()
            };
            Op::Submit {
                caller,
                req: Request {
                    recipe,
                    units,
                    version,
                    expires_at,
                },
                now,
            }
        }
        DISPATCH => {
            let id = id(src, p);
            let caller = if src.hint(70) {
                let actor = record_role(p, id, false).to_string();
                caller(src, &actor)
            } else {
                acct(src)
            };
            let now = if src.hint(60) {
                match spec::rec(&p.records, id) {
                    Some(c) => c.expires_at.saturating_sub(1 + src.below(2) as u64),
                    None => src.u64(),
                }
            } else {
                time(src, p)
            };
            Op::Dispatch { caller, id, now }
        }
        ACK => Op::Ack {
            id: id(src, p),
            accepted: src.bool(),
        },
        CANCEL => {
            let id = id(src, p);
            let caller = if src.hint(70) {
                let want = if src.bool() {
                    record_role(p, id, false).to_string()
                } else {
                    p.config.owner.clone()
                };
                caller(src, &want)
            } else {
                acct(src)
            };
            Op::Cancel {
                caller,
                id,
                now: src.u64(),
            }
        }
        SETTLE => {
            let id = id(src, p);
            let caller = if src.hint(70) {
                let ex = record_role(p, id, true).to_string();
                caller(src, &ex)
            } else {
                acct(src)
            };
            Op::Settle {
                caller,
                id,
                completed: src.bool(),
            }
        }
        PAUSE => {
            let caller = if src.hint(70) {
                let owner = p.config.owner.clone();
                caller(src, &owner)
            } else {
                acct(src)
            };
            Op::Pause {
                caller,
                paused: src.bool(),
            }
        }
        _ => {
            let caller = if src.hint(70) {
                let owner = p.config.owner.clone();
                caller(src, &owner)
            } else {
                acct(src)
            };
            let nm = p.config.metrics.len();
            let len = if src.hint(0) || src.bool() {
                nm
            } else {
                src.below(MAX_M as u32 + 2) as usize
            };
            let mut vals = Vec::with_capacity(MAX_M as usize + 1);
            for i in 0..MAX_M as usize + 1 {
                if i < len {
                    let x = match src.below(8) {
                        0 => -1_000_001,
                        1 => 1_000_001,
                        2 => i64::MIN,
                        3 => i64::MAX,
                        _ => val(src, d),
                    };
                    let x = if src.hint(90) { val(src, d) } else { x };
                    vals.push(x);
                }
            }
            Op::Observe {
                caller,
                vals,
                now: src.u64(),
            }
        }
    }
}

/// Plain mode: a random walk of `steps` operations from `Pool::new` over a
/// random small configuration, with its ghost.
#[cfg(not(kani))]
pub fn random_walk(src: &mut crate::src::Rng, steps: usize) -> (Pool, Ghost) {
    let c = src.cfg();
    let cfg = init_config(src, &c);
    let now = src.u64() % 1000;
    let mut p = Pool::new(cfg, now).expect("valid config");
    let mut g = Ghost::init(&p);
    for _ in 0..steps {
        let k = src.below(KINDS);
        let o = op(src, &p, k, c.val);
        if p.records.len() >= MAX_C as usize && k == SUBMIT {
            continue;
        }
        let x = spec::expected(&p, &o);
        let pre = copy(&p);
        let _ = spec::apply(&mut p, &o);
        g = spec::ghost_step(&g, &pre, &o, &x);
    }
    (p, g)
}

// ---------------------------------------------------------------------------
// Raw configurations (h_validate, h_init)
// ---------------------------------------------------------------------------

/// A string for `short`: empty, a short account, or (with `long`) 128 bytes
/// (the longest allowed) or 129 (too long).
pub fn raw_str(src: &mut impl Src, long: bool) -> String {
    const LONG: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const MAXLEN: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    if src.hint(97) {
        return acct(src).into();
    }
    match src.below(8) {
        0 => String::new(),
        1 if long => LONG.into(),
        2 if long => MAXLEN.into(),
        _ => acct(src).into(),
    }
}

/// An `i64` for a raw configuration: in range, just outside, or extreme.
pub fn raw_i64(src: &mut impl Src, d: Dom) -> i64 {
    if src.hint(97) {
        return val(src, d);
    }
    match src.below(8) {
        0 => -1_000_001,
        1 => 1_000_001,
        2 => i64::MIN,
        3 => i64::MAX,
        _ => val(src, d),
    }
}

fn raw_u32(src: &mut impl Src, edges: &[u32]) -> u32 {
    if src.hint(90) {
        return edges[1];
    }
    if src.bool() {
        edges[src.below(edges.len() as u32) as usize]
    } else {
        src.u32()
    }
}

/// Most metrics (and values per delta vector) of a raw configuration:
/// `MAX_M`+1 in plain mode, `MAX_M` under Kani (RESULTS.md, deviation 23).
pub const RAW_M: u8 = if cfg!(kani) { MAX_M } else { MAX_M + 1 };

/// Any configuration with at most [`RAW_M`] metrics, `MAX_T` terms,
/// `MAX_R`+1 recipes and 2 requirements per recipe; every field free
/// (strings from [`raw_str`], 128 and 129 bytes long only with `long`).
pub fn raw_config(src: &mut impl Src, c: &Cfg, long: bool) -> Config {
    // Every slot is written at a concrete offset and the vectors are then
    // truncated to their drawn lengths: a conditional push writes at a
    // symbolic offset (deviation 3), and with them `h_init` and `h_validate`
    // ran out of 40 GB in the propositional encoding.
    let nm = size(src, None, RAW_M, 0);
    let nt = size(src, None, MAX_T, 0);
    let nr = size(src, None, MAX_R + 1, 0);
    let mut metrics = Vec::with_capacity(RAW_M as usize);
    for _ in 0..RAW_M as usize {
        metrics.push(Metric {
            name: raw_str(src, long),
            unit: raw_str(src, long),
            initial: raw_i64(src, c.val),
            min: raw_i64(src, c.val),
            max: raw_i64(src, c.val),
        });
    }
    metrics.truncate(nm);
    let mut terms = Vec::with_capacity(MAX_T as usize);
    for _ in 0..MAX_T as usize {
        terms.push(Term {
            metric: if src.hint(90) && nm > 0 { src.below(nm as u32) } else { raw_u32(src, &[0, 1, 2, 3]) },
            target: raw_i64(src, c.val),
            weight: raw_u32(src, &[0, 1, 1000, 1001]),
            shape: shape_of(src),
        });
    }
    terms.truncate(nt);
    let mut recipes = Vec::with_capacity(MAX_R as usize + 1);
    for i in 0..MAX_R as usize + 1 {
        let lr = if src.hint(95) { nm } else { size(src, None, RAW_M, 0) };
        let lc = if src.hint(95) { nm } else { size(src, None, RAW_M, 0) };
        let mut reserve = Vec::with_capacity(RAW_M as usize);
        let mut complete = Vec::with_capacity(RAW_M as usize);
        for _ in 0..RAW_M as usize {
            reserve.push(raw_i64(src, c.delta));
            complete.push(raw_i64(src, c.delta));
        }
        reserve.truncate(lr);
        complete.truncate(lc);
        let nq = size(src, None, 2, 0);
        let mut requires = Vec::with_capacity(2);
        for j in 0..2u32 {
            let p = if src.hint(80) && i > 0 { j % i as u32 } else { raw_u32(src, &[0, 1, 2]) };
            requires.push((p, raw_u32(src, &[0, 1, 100, 101])));
        }
        requires.truncate(nq);
        recipes.push(Recipe {
            name: raw_str(src, long),
            actor: raw_str(src, long),
            executor: raw_str(src, long),
            reserve,
            complete,
            max_units: raw_u32(src, &[0, 1, 100, 101]),
            requires,
        });
    }
    recipes.truncate(nr);
    Config {
        name: raw_str(src, long),
        owner: raw_str(src, long),
        metrics,
        terms,
        recipes,
        max_age_seconds: src.u32(),
    }
}
