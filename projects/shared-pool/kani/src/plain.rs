//! Plain mode: every harness body with the random source. **Not a proof.**
//! Each test also requires every cover it evaluated to have fired, the
//! plain-mode counterpart of Kani's cover check.

use crate::checks::{self, PART_ALL};
use crate::src::{take_covers, Cfg, Dom, Rng, Shape};

const BASE: Cfg = Cfg {
    val: Dom::Small(6),
    delta: Dom::Small(4),
    max_units: 3,
    any_weight: false,
    shape: Shape::ANY,
    version_max: false,
    part: PART_ALL,
};

fn run_with(name: &str, seed: u64, iters: u32, base: Cfg, reach_pct: u8, body: &dyn Fn(&mut Rng)) {
    let _ = take_covers();
    let mut rng = Rng::new(seed, base);
    rng.reach_pct = reach_pct;
    for _ in 0..iters {
        body(&mut rng);
    }
    let covers = take_covers();
    let missed: Vec<_> = covers.iter().filter(|(_, (_, hit))| *hit == 0).collect();
    assert!(missed.is_empty(), "{name}: unsatisfied covers {missed:?}");
}

fn run(name: &str, seed: u64, iters: u32, body: fn(&mut Rng)) {
    run_with(name, seed, iters, BASE, 50, &body)
}

#[test]
fn h_init() {
    run("h_init", 0x11, 20_000, checks::init);
}

#[test]
fn h_init_inv() {
    run("h_init_inv", 0x15, 20_000, checks::init_inv);
}

#[test]
fn h_validate() {
    run("h_validate", 0x12, 200_000, checks::validate);
}

#[test]
fn h_energy() {
    run("h_energy", 0x13, 50_000, checks::energy);
    run("h_energy_max", 0x14, 1, checks::energy_max);
}

#[test]
fn h_step_submit() {
    run("h_step_submit", 0x21, 300_000, checks::step_submit);
}

#[test]
fn h_step_dispatch() {
    run("h_step_dispatch", 0x22, 100_000, checks::step_dispatch);
}

#[test]
fn h_step_ack() {
    run("h_step_ack", 0x23, 100_000, checks::step_ack);
}

#[test]
fn h_step_cancel() {
    run("h_step_cancel", 0x24, 2_000_000, checks::step_cancel);
}

#[test]
fn h_step_settle() {
    run("h_step_settle", 0x25, 2_000_000, checks::step_settle);
}

#[test]
fn h_step_pause() {
    run("h_step_pause", 0x26, 50_000, checks::step_pause);
}

#[test]
fn h_step_observe() {
    run("h_step_observe", 0x27, 100_000, checks::step_observe);
}

#[test]
fn h_version_max() {
    let base = Cfg {
        version_max: true,
        ..BASE
    };
    run_with("h_version_max", 0x28, 100_000, base, 0, &|s: &mut Rng| checks::version_max(s, None));
}

#[test]
fn h_preview() {
    run("h_preview", 0x31, 100_000, checks::preview);
}

#[test]
fn h_best() {
    run("h_best", 0x32, 100_000, checks::best);
}

#[test]
fn h_live1() {
    run("h_live1", 0x41, 200_000, checks::live1);
}

#[test]
fn h_wedge() {
    run_with("h_wedge", 0x42, 200_000, BASE, 0, &checks::wedge);
}

#[test]
fn h_wedge_healthy() {
    run_with("h_wedge_healthy", 0x46, 200_000, BASE, 0, &checks::wedge_healthy);
}

#[test]
fn h_bmc_from_init() {
    run_with("h_bmc_from_init", 0x43, 1_000_000, BASE, 0, &|r: &mut Rng| checks::bmc_from_init(r, 5));
}

/// The Kani instance of `h_bmc_from_init_*` (two operations, the first a
/// submit or a pause or observe; deviation 20) with the random source.
#[test]
fn h_bmc_two() {
    run_with("h_bmc_two", 0x47, 500_000, BASE, 0, &|r: &mut Rng| {
        let first = if r.next() % 2 == 0 { crate::gen::SUBMIT } else { crate::gen::PAUSE };
        checks::bmc_two(r, first, None)
    });
}

#[test]
fn h_full() {
    run_with("h_full", 0x44, 20_000, BASE, 0, &|s: &mut Rng| checks::full(s, None));
}

/// `h_slot_cycle_0`, `h_slot_cycle_2` (F-3): the cycle from `Pool::new`
/// and from INV states (random shapes, up to 3 records, often reached from
/// `Pool::new` by a random walk).
#[test]
fn h_slot_cycle() {
    run_with("h_slot_cycle_0", 0x48, 100_000, BASE, 0, &|s: &mut Rng| checks::slot_cycle(s, true));
    run_with("h_slot_cycle", 0x49, 300_000, BASE, 50, &|s: &mut Rng| checks::slot_cycle(s, false));
}

/// F-3 end to end on the brief's configuration, from `Pool::new`: 256
/// submit/cancel cycles by one actor (each free: the values return to the
/// start), then every submit fails `Full`, also after an `observe`, which
/// does not prune records.
#[test]
fn f3_slot_exhaustion() {
    use pool_core::*;
    let m = |min, max| Metric { name: "m".into(), unit: "u".into(), initial: 5, min, max };
    let cfg = Config {
        name: "p".into(),
        owner: "o".into(),
        metrics: vec![m(0, 10), m(-100, 100)],
        terms: vec![Term { metric: 1, target: 0, weight: 1, shape: Shape::Target }],
        recipes: vec![Recipe {
            name: "r".into(),
            actor: "a1".into(),
            executor: "x1".into(),
            reserve: vec![-2, 0],
            complete: vec![2, -5],
            max_units: 1,
            requires: vec![],
        }],
        max_age_seconds: 0,
    };
    let mut p = Pool::new(cfg, 100).unwrap();
    let start = p.values.clone();
    let req = |p: &Pool| Request { recipe: 0, units: 1, version: p.version, expires_at: 200 };
    for k in 0..256u32 {
        assert_eq!(p.submit("a1", req(&p), 100), Ok(k));
        assert_eq!(p.cancel("a1", k, 100), Ok(()));
        assert_eq!(p.values, start);
    }
    assert_eq!(p.records.len(), 256);
    assert!(p.records.iter().all(|c| c.status == Status::Cancelled));
    assert_eq!(p.submit("a1", req(&p), 100), Err(Error::Full));
    assert_eq!(p.observe("o", start.clone(), 101), Ok(()));
    assert_eq!(p.records.len(), 256);
    assert_eq!(p.submit("a1", req(&p), 101), Err(Error::Full));
}

#[test]
#[should_panic(expected = "canary")]
fn h_canary() {
    run("h_canary", 0x45, 2_000, checks::canary);
}

/// F-1 exactly as in the brief (trace 0 of conformance/traces/core.txt).
#[test]
fn f1_brief_instance() {
    use pool_core::*;
    let m = |min, max| Metric { name: "m".into(), unit: "u".into(), initial: 5, min, max };
    let cfg = Config {
        name: "p".into(),
        owner: "o".into(),
        metrics: vec![m(0, 10), m(-100, 100)],
        terms: vec![Term { metric: 1, target: 0, weight: 1, shape: Shape::Target }],
        recipes: vec![Recipe {
            name: "r".into(),
            actor: "a1".into(),
            executor: "x1".into(),
            reserve: vec![-2, 0],
            complete: vec![2, -5],
            max_units: 1,
            requires: vec![],
        }],
        max_age_seconds: 0,
    };
    let mut p = Pool::new(cfg, 100).unwrap();
    p.observe("o", vec![12, 5], 100).unwrap();
    let req = Request { recipe: 0, units: 1, version: p.version, expires_at: 200 };
    assert_eq!(p.submit("a1", req, 100), Ok(0));
    p.dispatch("a1", 0, 100).unwrap();
    let before = p.clone();
    assert_eq!(p.settle("x1", 0, true), Err(Error::Bounds));
    assert_eq!(p.settle("x1", 0, false), Err(Error::Bounds));
    assert_eq!(p.cancel("o", 0, 100), Err(Error::Pending));
    assert_eq!(p.observe("o", vec![12, 5], 100), Err(Error::Pending));
    assert_eq!(p, before);
}

/// A small F-2 instance (`checks::f2_instance`) wedges from `Pool::new`,
/// and passes every check of `h_wedge_healthy`'s body on the way.
#[test]
fn f2_small_instance() {
    let _ = take_covers();
    assert!(checks::wedge_healthy_on(checks::f2_instance()), "the F-2 instance wedges");
    let _ = take_covers();
}

/// F-2 on the supplied `risk` fixture (no observe): a credit position and a
/// selloff hedge relying on its reservation; the hedge completes, then the
/// executor's honest settle(cancelled) of the position fails Bounds forever.
#[test]
fn f2_risk_fixture() {
    use pool_core::*;
    let cfg = fixtures::config("risk").unwrap();
    let owner = cfg.owner.clone();
    let credit = cfg.recipes[0].actor.clone();
    let hedge = cfg.recipes[3].actor.clone();
    let exec = cfg.recipes[0].executor.clone();
    let mut p = Pool::new(cfg, 100).unwrap();
    let req = |recipe, units, p: &Pool| Request { recipe, units, version: p.version, expires_at: 1000 };
    let id0 = p.submit(&credit, req(0, 1, &p), 100).unwrap();
    let id1 = p.submit(&hedge, req(3, 8, &p), 100).unwrap();
    p.dispatch(&credit, id0, 101).unwrap();
    p.dispatch(&hedge, id1, 101).unwrap();
    p.settle(&exec, id1, true).unwrap();
    let before = p.clone();
    assert_eq!(p.settle(&exec, id0, false), Err(Error::Bounds));
    assert_eq!(p.cancel(&owner, id0, 102), Err(Error::Pending));
    let v = p.values.clone();
    assert_eq!(p.observe(&owner, v, 103), Err(Error::Pending));
    assert_eq!(p, before);
    // LIVE-1 is unaffected: completion is still accepted.
    assert_eq!(p.settle(&exec, id0, true), Ok(()));
}
