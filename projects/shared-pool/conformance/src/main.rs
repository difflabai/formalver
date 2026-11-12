//! Conformance traces of the real `pool-core` (strategy.md section 10).
//!
//! One generator, several replayers: every trace in `traces/core.txt` is
//! replayed by the Prolog reference semantics (MC-2), the TLA+ model (REF-5)
//! and the Lean machine (REF-5L). The format is Prolog terms, one per line:
//!
//! ```text
//! trace(N).
//! config(Owner, MaxAge, [m(Min,Max,Initial),..], [t(Metric,Target,Weight,Shape),..],
//!        [r(Actor,Executor,[Reserve..],[Complete..],MaxUnits,[p(Recipe,Units),..]),..]).
//! init(Now, State).
//! call(Op, Result, State).          % one per step
//! end.
//!
//! Shape  = target | excess | deficit
//! Op     = submit(Caller,Recipe,Units,Version,ExpiresAt,Now) | dispatch(Caller,Id,Now)
//!        | ack(Id,Accepted) | cancel(Caller,Id,Now) | settle(Caller,Id,Completed)
//!        | pause(Caller,Paused) | observe(Caller,[Values..],Now)
//! Result = ok | ok(Id) | err(Error)   Error = snake_case of pool_core::Error
//! State  = s([Values..], Version, ObservedAt, Paused, [c(Recipe,Units,ExpiresAt,Status),..])
//! Status = reserved | dispatched | active | unknown | completed | cancelled
//! ```
//!
//! Accounts are the atoms `o`, `a1`, `a2`, `x1`, `x2`, `z`; fixture account
//! names are renamed to these. Booleans are `true`/`false`. A record's id is
//! its index. `ok(Id)` is `submit`'s result; every other success is `ok`.
//!
//! usage: shared-pool-conformance [--traces N] [--len L] [--seed S] [--out FILE] [--check FILE]
//! `--check FILE` regenerates and fails if FILE differs (CI: the checked-in
//! traces are current).

use pool_core::*;
use std::collections::BTreeMap;
use std::fmt::Write as _;

const ACCOUNTS: [&str; 6] = ["o", "a1", "a2", "x1", "x2", "z"];

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    /// Uniform in `lo..=hi`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
    fn pct(&mut self, p: u64) -> bool {
        self.next() % 100 < p
    }
    fn pick<'a>(&mut self, xs: &[&'a str]) -> &'a str {
        xs[(self.next() % xs.len() as u64) as usize]
    }
}

fn err_name(e: &Error) -> String {
    let d = format!("{e:?}");
    let mut s = String::new();
    for (i, ch) in d.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if i > 0 {
                s.push('_');
            }
            s.push(ch.to_ascii_lowercase());
        } else {
            s.push(ch);
        }
    }
    s
}
fn status_name(s: &Status) -> &'static str {
    match s {
        Status::Reserved => "reserved",
        Status::Dispatched => "dispatched",
        Status::Active => "active",
        Status::Unknown => "unknown",
        Status::Completed => "completed",
        Status::Cancelled => "cancelled",
    }
}
fn shape_name(s: &Shape) -> &'static str {
    match s {
        Shape::Target => "target",
        Shape::Excess => "excess",
        Shape::Deficit => "deficit",
    }
}
fn ints(v: &[i64]) -> String {
    let parts: Vec<String> = v.iter().map(|x| x.to_string()).collect();
    format!("[{}]", parts.join(","))
}
fn state(p: &Pool) -> String {
    let recs: Vec<String> = p
        .records
        .iter()
        .map(|c| format!("c({},{},{},{})", c.recipe, c.units, c.expires_at, status_name(&c.status)))
        .collect();
    format!(
        "s({},{},{},{},[{}])",
        ints(&p.values),
        p.version,
        p.observed_at,
        p.paused,
        recs.join(",")
    )
}
fn config_term(c: &Config) -> String {
    let ms: Vec<String> = c
        .metrics
        .iter()
        .map(|m| format!("m({},{},{})", m.min, m.max, m.initial))
        .collect();
    let ts: Vec<String> = c
        .terms
        .iter()
        .map(|t| format!("t({},{},{},{})", t.metric, t.target, t.weight, shape_name(&t.shape)))
        .collect();
    let rs: Vec<String> = c
        .recipes
        .iter()
        .map(|r| {
            let req: Vec<String> = r.requires.iter().map(|(p, u)| format!("p({p},{u})")).collect();
            format!(
                "r({},{},{},{},{},[{}])",
                r.actor,
                r.executor,
                ints(&r.reserve),
                ints(&r.complete),
                r.max_units,
                req.join(",")
            )
        })
        .collect();
    format!(
        "config({},{},[{}],[{}],[{}]).",
        c.owner,
        c.max_age_seconds,
        ms.join(","),
        ts.join(","),
        rs.join(",")
    )
}

/// A random small configuration that `Config::validate` accepts.
fn random_config(rng: &mut Rng) -> Config {
    loop {
        let n = rng.range(1, 3) as usize;
        let metrics: Vec<Metric> = (0..n)
            .map(|i| {
                let min = rng.range(-5, 0);
                let max = min + rng.range(2, 10);
                Metric {
                    name: format!("m{i}"),
                    unit: "u".into(),
                    initial: rng.range(min, max),
                    min,
                    max,
                }
            })
            .collect();
        let terms = (0..rng.range(1, 3))
            .map(|_| {
                let metric = rng.range(0, n as i64 - 1) as u32;
                let m = &metrics[metric as usize];
                Term {
                    metric,
                    target: rng.range(m.min - 2, m.max + 2),
                    weight: rng.range(1, 3) as u32,
                    shape: match rng.range(0, 2) {
                        0 => Shape::Target,
                        1 => Shape::Excess,
                        _ => Shape::Deficit,
                    },
                }
            })
            .collect();
        let nr = rng.range(1, 3) as usize;
        let vec = |rng: &mut Rng| -> Vec<i64> {
            (0..n)
                .map(|_| if rng.pct(40) { 0 } else { rng.range(-3, 3) })
                .collect()
        };
        let recipes = (0..nr)
            .map(|i| {
                let requires = if i > 0 && rng.pct(30) {
                    vec![(rng.range(0, i as i64 - 1) as u32, rng.range(1, 3) as u32)]
                } else {
                    vec![]
                };
                Recipe {
                    name: format!("r{i}"),
                    actor: rng.pick(&["a1", "a2"]).into(),
                    executor: rng.pick(&["x1", "x2"]).into(),
                    reserve: vec(rng),
                    complete: vec(rng),
                    max_units: rng.range(1, 3) as u32,
                    requires,
                }
            })
            .collect();
        let c = Config {
            name: "rand".into(),
            owner: "o".into(),
            metrics,
            terms,
            recipes,
            max_age_seconds: if rng.pct(25) { rng.range(20, 60) as u32 } else { 0 },
        };
        if c.validate().is_ok() {
            return c;
        }
    }
}

/// A fixture with its account names renamed to the trace atoms.
fn fixture(name: &str) -> Config {
    let mut c = fixtures::config(name).expect("fixture");
    let mut actors: BTreeMap<String, &str> = BTreeMap::new();
    let mut execs: BTreeMap<String, &str> = BTreeMap::new();
    c.owner = "o".into();
    for r in &mut c.recipes {
        let n = actors.len();
        let a = *actors.entry(r.actor.clone()).or_insert(["a1", "a2"][n.min(1)]);
        let n = execs.len();
        let x = *execs.entry(r.executor.clone()).or_insert(["x1", "x2"][n.min(1)]);
        r.actor = a.into();
        r.executor = x.into();
    }
    c
}

/// F-1: a recovery hedge admitted in a disturbed state that can never settle.
fn wedge() -> (Config, Vec<Op>) {
    let m = |min, max, initial| Metric { name: "m".into(), unit: "u".into(), initial, min, max };
    let c = Config {
        name: "wedge".into(),
        owner: "o".into(),
        metrics: vec![m(0, 10, 5), m(-100, 100, 5)],
        terms: vec![Term { metric: 1, target: 0, weight: 1, shape: Shape::Target }],
        recipes: vec![Recipe {
            name: "hedge".into(),
            actor: "a1".into(),
            executor: "x1".into(),
            reserve: vec![-2, 0],
            complete: vec![2, -5],
            max_units: 1,
            requires: vec![],
        }],
        max_age_seconds: 0,
    };
    let ops = vec![
        Op::Observe("o".into(), vec![12, 5], 100),
        Op::Submit("a1".into(), Request { recipe: 0, units: 1, version: 1, expires_at: 200 }, 100),
        Op::Dispatch("a1".into(), 0, 101),
        Op::Ack(0, true),
        Op::Settle("x1".into(), 0, true),
        Op::Settle("x1".into(), 0, false),
        Op::Cancel("o".into(), 0, 102),
        Op::Observe("o".into(), vec![5, 5], 103),
    ];
    (c, ops)
}

#[derive(Clone, Debug)]
enum Op {
    Submit(String, Request, u64),
    Dispatch(String, u32, u64),
    Ack(u32, bool),
    Cancel(String, u32, u64),
    Settle(String, u32, bool),
    Pause(String, bool),
    Observe(String, Vec<i64>, u64),
}

fn op_term(op: &Op) -> String {
    match op {
        Op::Submit(c, r, now) => format!(
            "submit({c},{},{},{},{},{now})",
            r.recipe, r.units, r.version, r.expires_at
        ),
        Op::Dispatch(c, id, now) => format!("dispatch({c},{id},{now})"),
        Op::Ack(id, a) => format!("ack({id},{a})"),
        Op::Cancel(c, id, now) => format!("cancel({c},{id},{now})"),
        Op::Settle(c, id, done) => format!("settle({c},{id},{done})"),
        Op::Pause(c, p) => format!("pause({c},{p})"),
        Op::Observe(c, v, now) => format!("observe({c},{},{now})", ints(v)),
    }
}

fn apply(p: &mut Pool, op: &Op) -> String {
    let unit = |r: Result<(), Error>| match r {
        Ok(()) => "ok".to_string(),
        Err(e) => format!("err({})", err_name(&e)),
    };
    match op.clone() {
        Op::Submit(c, r, now) => match p.submit(&c, r, now) {
            Ok(id) => format!("ok({id})"),
            Err(e) => format!("err({})", err_name(&e)),
        },
        Op::Dispatch(c, id, now) => unit(p.dispatch(&c, id, now)),
        Op::Ack(id, a) => unit(p.acknowledge(id, a)),
        Op::Cancel(c, id, now) => unit(p.cancel(&c, id, now)),
        Op::Settle(c, id, done) => unit(p.settle(&c, id, done)),
        Op::Pause(c, b) => unit(p.set_paused(&c, b)),
        Op::Observe(c, v, now) => unit(p.observe(&c, v, now)),
    }
}

/// A random next call, biased toward calls whose guards pass.
fn random_op(rng: &mut Rng, p: &Pool, now: u64) -> Op {
    let cfg = &p.config;
    let nrec = p.records.len() as i64;
    let other = |rng: &mut Rng| rng.pick(&ACCOUNTS).to_string();
    let id = |rng: &mut Rng| -> u32 {
        if nrec == 0 || rng.pct(5) {
            rng.range(0, nrec + 1) as u32
        } else {
            // Prefer recent and open records.
            let open: Vec<u32> = p
                .records
                .iter()
                .filter(|c| !matches!(c.status, Status::Completed | Status::Cancelled))
                .map(|c| c.id)
                .collect();
            if !open.is_empty() && rng.pct(80) {
                open[(rng.next() % open.len() as u64) as usize]
            } else {
                rng.range(0, nrec - 1) as u32
            }
        }
    };
    let k = rng.range(0, 99);
    if k < 30 {
        let recipe = if rng.pct(95) { rng.range(0, cfg.recipes.len() as i64 - 1) } else { cfg.recipes.len() as i64 } as u32;
        let r = cfg.recipes.get(recipe as usize);
        let caller = match r {
            Some(r) if rng.pct(85) => r.actor.clone(),
            _ => other(rng),
        };
        let maxu = r.map_or(3, |r| r.max_units) as i64;
        let units = if rng.pct(90) { rng.range(1, maxu) } else { rng.range(0, maxu + 1) } as u32;
        let version = if rng.pct(90) { p.version } else { p.version.wrapping_add(rng.range(0, 2) as u32).wrapping_sub(1) };
        let expires_at = if rng.pct(92) {
            now + rng.range(1, 60) as u64
        } else if rng.pct(50) {
            now
        } else {
            now + 86_401
        };
        Op::Submit(caller, Request { recipe, units, version, expires_at }, now)
    } else if k < 48 {
        let i = id(rng);
        let caller = match p.records.get(i as usize) {
            Some(c) if rng.pct(85) => cfg.recipes[c.recipe as usize].actor.clone(),
            _ => other(rng),
        };
        Op::Dispatch(caller, i, now)
    } else if k < 60 {
        Op::Ack(id(rng), rng.pct(60))
    } else if k < 68 {
        let i = id(rng);
        let caller = match p.records.get(i as usize) {
            Some(c) if rng.pct(80) => {
                if rng.pct(70) { cfg.recipes[c.recipe as usize].actor.clone() } else { cfg.owner.clone() }
            }
            _ => other(rng),
        };
        Op::Cancel(caller, i, now)
    } else if k < 88 {
        let i = id(rng);
        let caller = match p.records.get(i as usize) {
            Some(c) if rng.pct(85) => cfg.recipes[c.recipe as usize].executor.clone(),
            _ => other(rng),
        };
        Op::Settle(caller, i, rng.pct(70))
    } else if k < 93 {
        let caller = if rng.pct(85) { cfg.owner.clone() } else { other(rng) };
        let b = if p.paused { rng.pct(20) } else { rng.pct(30) };
        Op::Pause(caller, b)
    } else {
        let caller = if rng.pct(90) { cfg.owner.clone() } else { other(rng) };
        let mut v: Vec<i64> = cfg
            .metrics
            .iter()
            .map(|m| if rng.pct(70) { rng.range(m.min, m.max) } else { rng.range(m.min - 3, m.max + 3) })
            .collect();
        if rng.pct(4) {
            v.pop();
        } else if rng.pct(3) {
            v[0] = MAX_VALUE + 1;
        }
        Op::Observe(caller, v, now)
    }
}

fn emit(out: &mut String, n: usize, cfg: &Config, ops: impl IntoIterator<Item = Op>, now0: u64) {
    let mut p = Pool::new(cfg.clone(), now0).expect("valid config");
    writeln!(out, "trace({n}).").unwrap();
    writeln!(out, "{}", config_term(cfg)).unwrap();
    writeln!(out, "init({now0},{}).", state(&p)).unwrap();
    for op in ops {
        let r = apply(&mut p, &op);
        writeln!(out, "call({},{r},{}).", op_term(&op), state(&p)).unwrap();
    }
    writeln!(out, "end.").unwrap();
}

fn generate(traces: usize, len: usize, seed: u64) -> (String, BTreeMap<String, usize>) {
    let mut out = String::new();
    let mut n = 0;
    let (c, ops) = wedge();
    emit(&mut out, n, &c, ops, 100);
    n += 1;
    for name in fixtures::NAMES {
        let c = fixture(name);
        let mut rng = Rng(seed ^ (0x9e37_79b9_7f4a_7c15 + n as u64));
        let mut p = Pool::new(c.clone(), 100).unwrap();
        let mut ops = vec![];
        let mut now = 100;
        // The fixture's own scenario trace first, then random calls.
        for (r, u) in fixtures::trace(name) {
            let actor = c.recipes[r as usize].actor.clone();
            let op = Op::Submit(actor, Request { recipe: r, units: u, version: p.version, expires_at: now + 50 }, now);
            apply(&mut p, &op);
            ops.push(op);
        }
        for _ in 0..len {
            now += rng.range(0, 2) as u64;
            let op = random_op(&mut rng, &p, now);
            apply(&mut p, &op);
            ops.push(op);
        }
        emit(&mut out, n, &c, ops, 100);
        n += 1;
    }
    for t in 0..traces {
        let mut rng = Rng(seed.wrapping_mul(t as u64 + 1) ^ 0x2545_f491_4f6c_dd1d);
        for _ in 0..4 {
            rng.next();
        }
        let c = random_config(&mut rng);
        let mut p = Pool::new(c.clone(), 100).unwrap();
        let mut ops = vec![];
        let mut now = 100;
        for _ in 0..len {
            now += rng.range(0, 3) as u64;
            let op = random_op(&mut rng, &p, now);
            apply(&mut p, &op);
            ops.push(op);
        }
        emit(&mut out, n, &c, ops, 100);
        n += 1;
    }
    let mut hits = BTreeMap::new();
    for line in out.lines().filter(|l| l.starts_with("call(")) {
        let op = line[5..].split('(').next().unwrap().to_string();
        let res = if let Some(i) = line.find(",err(") {
            line[i + 5..].split(')').next().unwrap().to_string()
        } else {
            "ok".into()
        };
        *hits.entry(format!("{op}:{res}")).or_insert(0) += 1;
    }
    (out, hits)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |flag: &str, d: u64| -> u64 {
        args.iter()
            .position(|a| a == flag)
            .and_then(|i| args.get(i + 1))
            .map_or(d, |v| v.parse().expect("number"))
    };
    let path = |flag: &str| args.iter().position(|a| a == flag).and_then(|i| args.get(i + 1)).cloned();
    let (out, hits) = generate(get("--traces", 200) as usize, get("--len", 40) as usize, get("--seed", 0x5eed));
    // Coverage the replayers rely on: every reachable error of every call.
    let required = [
        "submit:ok", "submit:paused", "submit:stale", "submit:expired", "submit:snapshot_expired",
        "submit:invalid_recipe", "submit:unauthorized", "submit:invalid_units", "submit:prerequisite",
        "submit:bounds", "submit:energy", "dispatch:ok", "dispatch:not_found", "dispatch:unauthorized",
        "dispatch:paused", "dispatch:invalid_state", "dispatch:expired", "dispatch:snapshot_expired",
        "ack:ok", "ack:not_found", "cancel:ok", "cancel:not_found", "cancel:unauthorized", "cancel:pending",
        "cancel:bounds", "settle:ok", "settle:not_found", "settle:unauthorized", "settle:invalid_state",
        "settle:bounds", "pause:ok", "pause:unauthorized", "observe:ok", "observe:unauthorized",
        "observe:pending", "observe:bounds",
    ];
    let missing: Vec<&str> = required.iter().copied().filter(|k| !hits.contains_key(*k)).collect();
    for (k, v) in &hits {
        eprintln!("{k:32} {v}");
    }
    if !missing.is_empty() {
        eprintln!("coverage: missing {missing:?}");
        std::process::exit(1);
    }
    if let Some(f) = path("--check") {
        let have = std::fs::read_to_string(&f).unwrap_or_default();
        if have != out {
            eprintln!("{f} is stale: regenerate with --out {f}");
            std::process::exit(1);
        }
        eprintln!("{f} is current");
    } else if let Some(f) = path("--out") {
        std::fs::write(&f, &out).expect("write");
    } else {
        print!("{out}");
    }
}
