//! Harness bodies, generic over [`Src`].
//!
//! Each body is the proof under Kani (`proofs.rs`) and a random test in plain
//! mode (`plain.rs`). Property IDs are tagged `PROP:` where they are checked.

use crate::gen::{self, ACK, CANCEL, DISPATCH, OBSERVE, PAUSE, SETTLE, SUBMIT};
use crate::spec::{self, *};
use crate::src::Src;
use pool_core::*;

/// `_tx`: exact result, TX-0, TX-NOOP, TX-VER, AUTH-1, STALE-1, ADM-1/2,
/// DEP-1, PAUSE-1 (blocked ops), OBS-1.
pub const PART_TX: u8 = 1;
/// `_post`: exact post-state and frame, LIFE-1, ASYNC-1, TERM-1, HARD-STEP,
/// PAUSE-1 (unaffected ops).
pub const PART_POST: u8 = 2;
/// `_inv`: INV-* after the step (with the ghost update).
pub const PART_INV: u8 = 4;
/// `_cov`: the covers only. Each SATISFIED cover is one more SAT call, and
/// with the assertions in the same run every call carries the full
/// equivalence proof (RESULTS.md, cost ladder).
pub const PART_COV: u8 = 8;
/// `h_ref_*`: REF-1..3, one step of the core refines the TLA+ model
/// (`tla.rs`). Alone in the `h_ref_*` harnesses (the spec's outcome is not
/// computed there), so the other parts keep their cost; plain mode runs it
/// inside every step test (`PART_ALL`).
pub const PART_REF: u8 = 16;
pub const PART_ALL: u8 = PART_TX | PART_POST | PART_INV | PART_COV | PART_REF;

// ---------------------------------------------------------------------------
// Shared checks
// ---------------------------------------------------------------------------

/// Every state invariant, asserted one by one so Kani reports each.
pub fn assert_inv(p: &Pool, g: &Ghost) {
    assert!(spec::valid(&p.config), "INV-WF: config valid"); // PROP: INV-WF
    assert!(spec::inv_wf(p, g), "INV-WF"); // PROP: INV-WF
    assert!(spec::inv_ledger(p, g), "INV-LEDGER"); // PROP: INV-LEDGER
    assert!(spec::inv_hard(p, g), "INV-HARD"); // PROP: INV-HARD
    assert!(spec::inv_healthy(p, g), "INV-HEALTHY"); // PROP: INV-HARD (corollary INV-HEALTHY)
    assert!(spec::inv_dep(p), "INV-DEP"); // PROP: INV-DEP
    assert!(spec::inv_ver(p, g), "INV-VER"); // PROP: INV-VER
}

fn vals_of(p: &Pool) -> Vals {
    spec::vals(&p.config, &p.values)
}

/// The role that may make `op` effective (AUTH-1), or `None` (ack: the shell
/// makes it private; out-of-range ids).
fn authorized(pre: &Pool, op: &Op) -> bool {
    let cfg = &pre.config;
    let rec_recipe = |id: u32| spec::rec(&pre.records, id).map(|c| spec::rcp_of(cfg, c.recipe));
    match op {
        Op::Submit { caller, req, .. } => match spec::rcp(cfg, req.recipe) {
            Some(r) => spec::eq_str(caller, &r.actor),
            None => false,
        },
        Op::Dispatch { caller, id, .. } => match rec_recipe(*id) {
            Some(r) => spec::eq_str(caller, &r.actor),
            None => false,
        },
        Op::Ack { .. } => true,
        Op::Cancel { caller, id, .. } => match rec_recipe(*id) {
            Some(r) => spec::eq_str(caller, &r.actor) || spec::eq_str(caller, &cfg.owner),
            None => false,
        },
        Op::Settle { caller, id, .. } => match rec_recipe(*id) {
            Some(r) => spec::eq_str(caller, &r.executor),
            None => false,
        },
        Op::Pause { caller, .. } | Op::Observe { caller, .. } => spec::eq_str(caller, &cfg.owner),
    }
}

/// `PART_TX` assertions for one step `pre --op--> post` with result `res`.
pub fn check_tx(pre: &Pool, post: &Pool, op: &Op, res: &Res, x: &Exp) {
    // PROP: TX-SUBMIT TX-DISPATCH TX-ACK TX-CANCEL TX-SETTLE TX-PAUSE TX-OBSERVE (result) NUM-2 (`add`'s Arithmetic exits, `Why::Add`)
    assert!(*res == x.res, "TX: exact result in guard order");
    let same = spec::same_state(post, pre);
    if res.is_err() {
        assert!(same, "TX-0: an error leaves the pool unchanged"); // PROP: TX-0
    }
    if x.noop() {
        assert!(same, "TX-NOOP: idempotent Ok changes nothing"); // PROP: TX-NOOP
    }
    if res.is_ok() && x.effective() {
        // PROP: TX-VER
        assert!(
            post.version as u64 == pre.version as u64 + 1,
            "TX-VER: effective Ok increments version by 1"
        );
    }
    let changed = !same;
    if changed {
        assert!(authorized(pre, op), "AUTH-1: effective call by the authorized role"); // PROP: AUTH-1
    }
    match op {
        Op::Submit { req, .. } => {
            if pre.paused {
                assert!(!changed, "PAUSE-1: paused blocks submit"); // PROP: PAUSE-1
            }
            if res.is_ok() {
                // PROP: STALE-1
                assert!(req.version == pre.version, "STALE-1: accepted request is at the current version");
                assert!(post.version > pre.version, "STALE-1: version strictly increases");
                let cfg = &pre.config;
                let r = spec::rcp_of(cfg, req.recipe);
                let e0 = spec::energy(cfg, &vals_of(pre));
                let v1 = vals_of(post);
                assert!(spec::energy(cfg, &v1) <= e0, "ADM-1: energy does not increase"); // PROP: ADM-1
                if spec::violating(cfg, &vals_of(pre)) {
                    // PROP: ADM-2
                    match spec::add(cfg, &v1, &r.complete, req.units) {
                        Some(done) => assert!(
                            spec::energy(cfg, &done) < e0,
                            "ADM-2: completion strictly decreases energy"
                        ),
                        None => panic!("ADM-2: completion leaves the value range"),
                    }
                }
                // PROP: DEP-1
                assert!(spec::prereqs_met(r, &pre.records), "DEP-1: prerequisites met by Completed units");
            }
        }
        Op::Dispatch { .. } => {
            if pre.paused {
                assert!(!changed, "PAUSE-1: paused blocks dispatch"); // PROP: PAUSE-1
            }
        }
        Op::Observe { .. } => {
            if res.is_ok() {
                // PROP: OBS-1
                let mut any_open = false;
                for c in &pre.records {
                    if spec::open(&c.status) {
                        any_open = true;
                    }
                }
                assert!(!any_open, "OBS-1: observe only with no open record");
                assert!(spec::same_config(&post.config, &pre.config), "OBS-1: config unchanged");
            }
        }
        Op::Settle { completed: true, .. } => {
            // PROP: INV-HARD (corollary): from an INV state, completing a
            // record never fails Arithmetic except at version u32::MAX.
            if *res == Err(Error::Arithmetic) {
                assert!(pre.version == u32::MAX, "INV-HARD: settle(completed) Arithmetic only at version MAX");
            }
        }
        _ => {}
    }
}

/// `PART_POST` assertions.
pub fn check_post(pre: &Pool, post: &Pool, op: &Op, res: &Res, x: &Exp) {
    // PROP: TX-SUBMIT TX-DISPATCH TX-ACK TX-CANCEL TX-SETTLE TX-PAUSE TX-OBSERVE (post-state, frame)
    assert!(spec::post_matches(pre, post, x), "TX: exact post-state and frame");

    // PROP: LIFE-1
    let k = pre.records.len();
    assert!(
        post.records.len() == k || post.records.len() == k + 1,
        "LIFE-1: records are append-only, at most one per step"
    );
    if post.records.len() == k + 1 {
        assert!(matches!(op, Op::Submit { .. }), "LIFE-1: only submit appends");
        let c = &post.records[k];
        assert!(c.id as usize == k && c.status == Status::Reserved, "LIFE-1: new record Reserved at id = index");
    }
    for j in 0..k {
        if j < post.records.len() {
            let (a, b) = (&pre.records[j], &post.records[j]);
            assert!(
                a.id == b.id && a.recipe == b.recipe && a.units == b.units && a.expires_at == b.expires_at,
                "LIFE-1: id, recipe, units, expires_at immutable"
            );
            assert!(spec::life_step(&a.status, &b.status), "LIFE-1: status graph");
            if spec::terminal(&a.status) {
                assert!(a.status == b.status, "LIFE-1: terminal is absorbing");
            }
            // PROP: ASYNC-1
            if matches!(a.status, Status::Active | Status::Unknown) && b.status == Status::Cancelled {
                assert!(
                    matches!(op, Op::Settle { completed: false, .. }) && authorized(pre, op),
                    "ASYNC-1: an acknowledged or unknown record is released only by the executor"
                );
            }
        }
    }
    match op {
        Op::Ack { .. } => {
            assert!(spec::eq_i64s(&post.values, &pre.values), "ASYNC-1: acknowledge never changes values"); // PROP: ASYNC-1
        }
        Op::Cancel { id, .. } => {
            if let Some(c) = spec::rec(&pre.records, *id) {
                if authorized(pre, op) && matches!(c.status, Status::Dispatched | Status::Active | Status::Unknown) {
                    // PROP: ASYNC-1
                    assert!(*res == Err(Error::Pending), "ASYNC-1: in-flight records keep their reservation");
                }
            }
        }
        Op::Settle { id, completed, .. } => {
            if let Some(c) = spec::rec(&pre.records, *id) {
                if authorized(pre, op) && spec::terminal(&c.status) {
                    // PROP: TERM-1
                    let same = (*completed && c.status == Status::Completed)
                        || (!*completed && c.status == Status::Cancelled);
                    if same {
                        assert!(*res == Ok(None) && spec::same_state(post, pre), "TERM-1: same terminal is an Ok no-op");
                    } else {
                        assert!(*res == Err(Error::InvalidState), "TERM-1: opposite terminal is InvalidState");
                    }
                }
            }
        }
        _ => {}
    }
    // PROP: HARD-STEP
    if res.is_ok() && !matches!(op, Op::Observe { .. }) {
        let cfg = &pre.config;
        let (a, b) = (vals_of(pre), vals_of(post));
        for i in 0..M {
            if i < spec::n(cfg) {
                let m = &cfg.metrics[i];
                assert!(spec::pv(m, b[i]) <= spec::pv(m, a[i]), "HARD-STEP: no metric's violation grows");
            }
        }
    }
    // PROP: PAUSE-1: settle, acknowledge, cancel and observe are unaffected
    // by `paused`. Under Kani: the spec's outcome from the pre-state with
    // `paused` flipped is the same (with the flag kept flipped), and `_tx` and
    // `_post` show that the code's result and post-state are the spec's from
    // every state of the domain, `paused` either way; so the code's outcome
    // does not depend on `paused` either. Calling the code a second time here
    // doubled the formula (cancel ran out of 32 GB; RESULTS.md, cost ladder).
    // Plain mode also calls the code again.
    if matches!(op, Op::Ack { .. } | Op::Cancel { .. } | Op::Settle { .. } | Op::Observe { .. }) {
        let mut q = gen::copy(pre);
        q.paused = !q.paused;
        let y = spec::expected(&q, op);
        assert!(
            y.res == x.res
                && y.why == x.why
                && spec::eq_vals(&y.values, &x.values)
                && y.version == x.version
                && y.observed_at == x.observed_at
                && y.paused == !x.paused
                && y.push == x.push
                && y.status == x.status,
            "PAUSE-1: the spec's outcome is independent of paused"
        );
        #[cfg(not(kani))]
        {
            let r2 = spec::apply(&mut q, op);
            q.paused = !q.paused;
            assert!(r2 == *res && spec::same_state(&q, post), "PAUSE-1: result and effect independent of paused");
        }
    }
}

// ---------------------------------------------------------------------------
// Covers (in the `_cov` part only; one family per step)
// ---------------------------------------------------------------------------

fn covers(pre: &Pool, op: &Op, res: &Res, x: &Exp, g: &Ghost) {
    use Error::*;
    let w = x.why;
    let healthy = spec::healthy_base(&pre.config, g);
    match op {
        Op::Submit { .. } => {
            cover!(res.is_ok() && !spec::violating(&pre.config, &vals_of(pre)), "submit: Ok");
            cover!(res.is_ok() && spec::violating(&pre.config, &vals_of(pre)), "submit: Ok in a violating state (recovery)");
            cover!(res.is_ok() && pre.records.len() >= 2, "submit: Ok with 2 earlier records");
            cover!(*res == Err(Paused), "submit: Paused");
            cover!(*res == Err(Stale), "submit: Stale");
            cover!(*res == Err(Expired), "submit: Expired");
            cover!(*res == Err(SnapshotExpired), "submit: SnapshotExpired");
            cover!(*res == Err(InvalidRecipe), "submit: InvalidRecipe");
            cover!(*res == Err(Unauthorized), "submit: Unauthorized");
            cover!(*res == Err(InvalidUnits), "submit: InvalidUnits");
            cover!(*res == Err(Prerequisite), "submit: Prerequisite");
            cover!(*res == Err(Arithmetic) && w == Why::Add, "submit: Arithmetic (reserve)");
            cover!(*res == Err(Arithmetic) && w == Why::Envelope, "submit: Arithmetic (envelope)");
            cover!(*res == Err(Arithmetic) && w == Why::Version, "submit: Arithmetic (version)");
            cover!(*res == Err(Bounds), "submit: Bounds");
            cover!(*res == Err(Energy) && w == Why::EnergyUp, "submit: Energy (increase)");
            cover!(*res == Err(Energy) && w == Why::Recovery, "submit: Energy (recovery rule)");
        }
        Op::Dispatch { .. } => {
            cover!(res.is_ok(), "dispatch: Ok");
            cover!(*res == Err(NotFound), "dispatch: NotFound");
            cover!(*res == Err(Unauthorized), "dispatch: Unauthorized");
            cover!(*res == Err(Paused), "dispatch: Paused");
            cover!(*res == Err(InvalidState), "dispatch: InvalidState");
            cover!(*res == Err(Expired), "dispatch: Expired");
            cover!(*res == Err(SnapshotExpired), "dispatch: SnapshotExpired");
            cover!(*res == Err(Arithmetic), "dispatch: Arithmetic (version)");
        }
        Op::Ack { id, accepted } => {
            let st = spec::rec(&pre.records, *id).map(|c| c.status.clone());
            cover!(res.is_ok() && w != Why::Noop && st == Some(Status::Dispatched) && *accepted, "ack: Dispatched -> Active");
            cover!(res.is_ok() && w != Why::Noop && st == Some(Status::Dispatched) && !*accepted, "ack: Dispatched -> Unknown");
            cover!(res.is_ok() && w != Why::Noop && st == Some(Status::Unknown), "ack: Unknown -> Active");
            cover!(x.noop() && st == Some(Status::Unknown), "ack: no-op Unknown -> Unknown");
            cover!(x.noop() && st == Some(Status::Active), "ack: no-op on Active (late ack)");
            cover!(x.noop() && st == Some(Status::Completed), "ack: no-op on a terminal record");
            cover!(*res == Err(NotFound), "ack: NotFound");
            cover!(*res == Err(Arithmetic), "ack: Arithmetic (version)");
        }
        Op::Cancel { .. } => {
            cover!(res.is_ok() && w == Why::Release, "cancel: Ok (released)");
            cover!(x.noop(), "cancel: no-op on Cancelled");
            cover!(*res == Err(NotFound), "cancel: NotFound");
            cover!(*res == Err(Unauthorized), "cancel: Unauthorized");
            cover!(*res == Err(Pending), "cancel: Pending");
            cover!(*res == Err(Arithmetic) && w == Why::Add, "cancel: Arithmetic (release)");
            cover!(*res == Err(Arithmetic) && w == Why::Envelope, "cancel: Arithmetic (envelope)");
            cover!(*res == Err(Arithmetic) && w == Why::Version, "cancel: Arithmetic (version)");
            cover!(*res == Err(Bounds), "cancel: Bounds (a dependent reservation blocks release)");
        }
        Op::Settle { completed, .. } => {
            cover!(res.is_ok() && *completed && w != Why::Noop, "settle: Ok completed");
            cover!(res.is_ok() && *completed && w != Why::Noop && !healthy, "settle: Ok completed after a disturbing observe");
            cover!(res.is_ok() && !*completed && w == Why::Release, "settle: Ok cancelled (released)");
            cover!(x.noop() && *completed, "settle: no-op Completed again");
            cover!(x.noop() && !*completed, "settle: no-op Cancelled again");
            cover!(*res == Err(NotFound), "settle: NotFound");
            cover!(*res == Err(Unauthorized), "settle: Unauthorized");
            cover!(*res == Err(InvalidState) && w == Why::Plain, "settle: InvalidState (Reserved)");
            cover!(*res == Err(InvalidState) && w == Why::Opposite, "settle: InvalidState (opposite terminal)");
            cover!(*res == Err(Bounds) && *completed, "settle: Bounds (completion)");
            cover!(*res == Err(Bounds) && !*completed, "settle: Bounds (release)");
            cover!(*res == Err(Arithmetic) && !*completed && w == Why::Add, "settle: Arithmetic (release)");
            cover!(*res == Err(Arithmetic) && w == Why::Version, "settle: Arithmetic (version)");
        }
        Op::Pause { paused, .. } => {
            cover!(res.is_ok() && *paused, "pause: Ok pause");
            cover!(res.is_ok() && !*paused, "pause: Ok unpause");
            cover!(res.is_ok() && *paused == pre.paused, "pause: Ok without change still bumps");
            cover!(*res == Err(Error::Unauthorized), "pause: Unauthorized");
            cover!(*res == Err(Error::Arithmetic), "pause: Arithmetic (version)");
        }
        Op::Observe { vals, .. } => {
            let viol = vals.len() == spec::n(&pre.config)
                && vals.iter().all(|v| spec::bounded(*v as spec::Z))
                && spec::violating(&pre.config, &spec::vals(&pre.config, vals));
            cover!(res.is_ok() && !viol, "observe: Ok");
            cover!(res.is_ok() && viol, "observe: Ok exposing a violation");
            cover!(res.is_ok() && !pre.records.is_empty(), "observe: Ok after terminal records");
            cover!(*res == Err(Unauthorized), "observe: Unauthorized");
            cover!(*res == Err(Pending), "observe: Pending");
            cover!(*res == Err(Bounds) && vals.len() != spec::n(&pre.config), "observe: Bounds (length)");
            cover!(*res == Err(Bounds) && vals.len() == spec::n(&pre.config), "observe: Bounds (value)");
            cover!(*res == Err(Arithmetic), "observe: Arithmetic (version)");
        }
    }
}

// ---------------------------------------------------------------------------
// Step harness bodies
// ---------------------------------------------------------------------------

/// One operation of kind `kind` from an INV state.
pub fn step(src: &mut impl Src, kind: u32) {
    let c = src.cfg();
    let Some((mut p, g)) = gen::inv_state(src, &c) else {
        return;
    };
    let op = gen::op(src, &p, kind, c.val);
    let pre = gen::copy(&p);
    let x = spec::expected(&pre, &op);
    let res = spec::apply(&mut p, &op); // PROP: ROB-1 (Kani's panic, overflow and bounds checks, in every harness that calls the core)
    if c.part & PART_TX != 0 {
        check_tx(&pre, &p, &op, &res, &x);
    }
    if c.part & PART_COV != 0 {
        covers(&pre, &op, &res, &x, &g);
    }
    if c.part & PART_POST != 0 {
        check_post(&pre, &p, &op, &res, &x);
    }
    if c.part & PART_INV != 0 {
        let h = spec::ghost_step(&g, &pre, &op, &x);
        assert_inv(&p, &h);
    }
    // Plain mode only (the Kani step harnesses' code is unchanged; under
    // Kani REF-1..3 are `step_ref`'s, the `h_ref_*` harnesses).
    #[cfg(not(kani))]
    {
        if c.part & PART_REF != 0 {
            refines(&pre, &g, &op, &res, &p);
        }
    }
}

/// `h_ref_*`: the step's state and operation (the same generators, `Cfg`
/// and bounds as `step`), the real core applied, then REF-1..3 alone (no
/// spec outcome).
pub fn step_ref(src: &mut impl Src, kind: u32) {
    let c = src.cfg();
    let Some((mut p, g)) = gen::inv_state(src, &c) else {
        return;
    };
    let op = gen::op(src, &p, kind, c.val);
    let pre = gen::copy(&p);
    let res = spec::apply(&mut p, &op);
    refines(&pre, &g, &op, &res, &p);
}

/// REF-1..3 for the step `pre --op--> post` (`tla::assert_refines` with
/// the step bounds' image, `tla::TK`), and the `h_ref` covers.
pub fn refines(pre: &Pool, g: &Ghost, op: &Op, res: &Res, post: &Pool) {
    let w = crate::tla::assert_refines::<2, 2, 2, 2, 4>(pre, &g.base, g.k0, op, res, post); // PROP: REF-1 REF-2 REF-3
    ref_covers(op, w);
}

/// The `h_ref` cover family: every value of each TLA+ error operator that
/// the step domains reach ("Ok": the action is enabled, REF-2; "Noop" and
/// every error: a stutter, REF-3). `Full` needs 256 records (`h_full_*`).
fn ref_covers(op: &Op, w: crate::tla::TErr) {
    use crate::tla::TErr as W;
    match op {
        Op::Submit { .. } => {
            cover!(w == W::Ok, "ref submit: Ok (Submit enabled)");
            cover!(w == W::Paused, "ref submit: Paused");
            cover!(w == W::Stale, "ref submit: Stale");
            cover!(w == W::Expired, "ref submit: Expired");
            cover!(w == W::SnapshotExpired, "ref submit: SnapshotExpired");
            cover!(w == W::InvalidRecipe, "ref submit: InvalidRecipe");
            cover!(w == W::Unauthorized, "ref submit: Unauthorized");
            cover!(w == W::InvalidUnits, "ref submit: InvalidUnits");
            cover!(w == W::Prerequisite, "ref submit: Prerequisite");
            cover!(w == W::Arithmetic, "ref submit: Arithmetic");
            cover!(w == W::Bounds, "ref submit: Bounds");
            cover!(w == W::Energy, "ref submit: Energy");
        }
        Op::Dispatch { .. } => {
            cover!(w == W::Ok, "ref dispatch: Ok (Dispatch enabled)");
            cover!(w == W::NotFound, "ref dispatch: NotFound");
            cover!(w == W::Unauthorized, "ref dispatch: Unauthorized");
            cover!(w == W::Paused, "ref dispatch: Paused");
            cover!(w == W::InvalidState, "ref dispatch: InvalidState");
            cover!(w == W::Expired, "ref dispatch: Expired");
            cover!(w == W::SnapshotExpired, "ref dispatch: SnapshotExpired");
            cover!(w == W::Arithmetic, "ref dispatch: Arithmetic");
        }
        Op::Ack { .. } => {
            cover!(w == W::Ok, "ref ack: Ok (Ack enabled)");
            cover!(w == W::Noop, "ref ack: Noop");
            cover!(w == W::NotFound, "ref ack: NotFound");
            cover!(w == W::Arithmetic, "ref ack: Arithmetic");
        }
        Op::Cancel { .. } => {
            cover!(w == W::Ok, "ref cancel: Ok (Cancel enabled)");
            cover!(w == W::Noop, "ref cancel: Noop");
            cover!(w == W::NotFound, "ref cancel: NotFound");
            cover!(w == W::Unauthorized, "ref cancel: Unauthorized");
            cover!(w == W::Pending, "ref cancel: Pending");
            cover!(w == W::Arithmetic, "ref cancel: Arithmetic");
            cover!(w == W::Bounds, "ref cancel: Bounds");
        }
        Op::Settle { .. } => {
            cover!(w == W::Ok, "ref settle: Ok (Settle enabled)");
            cover!(w == W::Noop, "ref settle: Noop");
            cover!(w == W::NotFound, "ref settle: NotFound");
            cover!(w == W::Unauthorized, "ref settle: Unauthorized");
            cover!(w == W::InvalidState, "ref settle: InvalidState");
            cover!(w == W::Arithmetic, "ref settle: Arithmetic");
            cover!(w == W::Bounds, "ref settle: Bounds");
        }
        Op::Pause { .. } => {
            cover!(w == W::Ok, "ref pause: Ok (SetPaused enabled)");
            cover!(w == W::Unauthorized, "ref pause: Unauthorized");
            cover!(w == W::Arithmetic, "ref pause: Arithmetic");
        }
        Op::Observe { .. } => {
            cover!(w == W::Ok, "ref observe: Ok (Observe enabled)");
            cover!(w == W::Unauthorized, "ref observe: Unauthorized");
            cover!(w == W::Pending, "ref observe: Pending");
            cover!(w == W::Bounds, "ref observe: Bounds");
            cover!(w == W::Arithmetic, "ref observe: Arithmetic");
        }
    }
}

pub fn step_submit(src: &mut impl Src) {
    step(src, SUBMIT)
}
pub fn step_dispatch(src: &mut impl Src) {
    step(src, DISPATCH)
}
pub fn step_ack(src: &mut impl Src) {
    step(src, ACK)
}
pub fn step_cancel(src: &mut impl Src) {
    step(src, CANCEL)
}
pub fn step_settle(src: &mut impl Src) {
    step(src, SETTLE)
}
pub fn step_pause(src: &mut impl Src) {
    step(src, PAUSE)
}
pub fn step_observe(src: &mut impl Src) {
    step(src, OBSERVE)
}

/// `h_version_max_<op>`: an operation of kind `kind` (any kind if `None`)
/// from an INV state at `version = u32::MAX`. PROP: TX-VER (no wrap: every
/// effective transition fails Arithmetic), TX-NOOP (idempotent paths still
/// succeed), TX-0. Under Kani one harness per kind: all seven kinds in one
/// formula did not finish in 30 minutes (RESULTS.md, cost ladder).
pub fn version_max(src: &mut impl Src, kind: Option<u32>) {
    let c = src.cfg();
    let Some((mut p, _g)) = gen::inv_state(src, &c) else {
        return;
    };
    assume!(p.version == u32::MAX);
    let kind = match kind {
        Some(k) => k,
        None => src.below(gen::KINDS),
    };
    let op = gen::op(src, &p, kind, c.val);
    let pre = gen::copy(&p);
    let x = spec::expected(&pre, &op);
    let res = spec::apply(&mut p, &op);
    // Plain mode only (the Kani harnesses' code is unchanged).
    #[cfg(not(kani))]
    {
        if c.part & PART_REF != 0 {
            let w = crate::tla::assert_refines::<2, 2, 2, 2, 4>(&pre, &_g.base, _g.k0, &op, &res, &p); // PROP: REF-1 REF-2 REF-3
            assert!(w != crate::tla::TErr::Ok, "REF: no action is enabled at version MAX");
        }
    }
    assert!(res == x.res, "TX: exact result at version MAX");
    assert!(spec::same_state(&p, &pre), "TX-VER: at version MAX nothing changes (no wrap)"); // PROP: TX-VER TX-0
    if res.is_ok() {
        assert!(x.noop(), "TX-NOOP: only idempotent paths succeed at version MAX"); // PROP: TX-NOOP
    }
    let ar = res == Err(Error::Arithmetic);
    cover!(ar && kind == SUBMIT, "version max: submit Arithmetic");
    cover!(ar && kind == DISPATCH, "version max: dispatch Arithmetic");
    cover!(ar && kind == ACK, "version max: ack Arithmetic");
    cover!(ar && kind == CANCEL, "version max: cancel Arithmetic");
    cover!(ar && kind == SETTLE, "version max: settle Arithmetic");
    cover!(ar && kind == PAUSE, "version max: pause Arithmetic");
    cover!(ar && kind == OBSERVE, "version max: observe Arithmetic");
    cover!(res.is_ok() && kind == ACK, "version max: ack no-op Ok");
    cover!(res.is_ok() && kind == CANCEL, "version max: cancel no-op Ok");
    cover!(res.is_ok() && kind == SETTLE, "version max: settle no-op Ok");
}

// ---------------------------------------------------------------------------
// Configuration and numerics
// ---------------------------------------------------------------------------

/// Strings of 128 and 129 bytes in the raw configurations of `h_init` and
/// `h_validate`: plain mode only. Under Kani both run with the capacity
/// model (24-byte strings): copying and comparing a string of symbolic
/// length up to 129 bytes made `h_init` run out of time, and without the
/// model `h_validate` ran out of 40 GB (RESULTS.md, cost ladder). `validate`
/// reads only the length of a string (`short`: 1 to 128 bytes).
const INIT_LONG: bool = !cfg!(kani);

/// `h_init`: CFG-1. `Pool::new` succeeds iff `validate` does (and the spec's
/// validity), and the initial pool is as specified and satisfies INV. Under
/// Kani `validate` is a stub with a free result (`model::validate`;
/// `h_validate` shows that the real one is the spec's validity), and the
/// INV of the initial pool is `h_init_inv`'s: the raw configuration, the
/// real `validate`, the spec's validity and the invariants in one formula
/// ran out of 40 GB (RESULTS.md, cost ladder).
pub fn init(src: &mut impl Src) {
    let c = src.cfg();
    // Plain mode: half the samples a valid configuration with free initial
    // values (raw ones are rarely valid). Under Kani the raw configurations
    // include every valid one of the domain, and a second builder doubled
    // the heap objects every pointer may refer to.
    let cfg = if cfg!(kani) || src.bool() {
        gen::raw_config(src, &c, INIT_LONG)
    } else {
        gen::init_config(src, &c)
    };
    let now = src.u64();
    #[cfg(kani)]
    crate::model::VALIDATED.store(0, std::sync::atomic::Ordering::SeqCst);
    let r = Pool::new(gen::copy_config(&cfg), now);
    // PROP: CFG-1. `new` is Ok iff `validate` is; with CFG-2 (`h_validate`:
    // `validate` = spec), iff the configuration is valid.
    #[cfg(kani)]
    {
        let v = crate::model::VALIDATED.load(std::sync::atomic::Ordering::SeqCst);
        assert!(v != 0, "CFG-1: new calls validate");
        assert!(r.is_ok() == (v == 1), "CFG-1: new Ok iff validate Ok");
    }
    #[cfg(not(kani))]
    {
        assert!(r.is_ok() == spec::valid(&cfg), "CFG-1: new Ok iff the configuration is valid");
        assert!(r.is_ok() == cfg.validate().is_ok(), "CFG-1: new Ok iff validate Ok");
    }
    match &r {
        Err(e) => assert!(*e == Error::InvalidConfig, "CFG-1: new fails only InvalidConfig"),
        Ok(p) => {
            assert!(
                spec::same_config(&p.config, &cfg) && p.version == 0 && p.observed_at == now && !p.paused && p.records.is_empty(),
                "CFG-1: initial pool"
            );
            let mut ok = p.values.len() == cfg.metrics.len();
            for (i, m) in cfg.metrics.iter().enumerate() {
                if i < p.values.len() && p.values[i] != m.initial {
                    ok = false;
                }
            }
            assert!(ok, "CFG-1: initial values");
            #[cfg(not(kani))]
            if cfg.metrics.len() <= M {
                assert_inv(p, &Ghost::init(p)); // PROP: CFG-1 (init satisfies INV)
            }
        }
    }
    cover!(r.is_ok(), "init: Ok");
    cover!(r.is_err(), "init: InvalidConfig");
}

/// `h_init_inv`: CFG-1 on valid configurations (up to 2 metrics, 2 terms, 2
/// recipes, free initial values) with the real `validate`: `Pool::new` is
/// `Ok`, and the initial pool satisfies every INV with the initial ghost.
pub fn init_inv(src: &mut impl Src) {
    let c = src.cfg();
    let cfg = gen::init_config(src, &c);
    let now = src.u64();
    // Under Kani `new`'s `Ok` value is built directly (`pool_of`): `h_init`
    // shows that `new` is `Ok` iff `validate` is and builds exactly this
    // pool, and `h_validate` that `validate` is `valid` (asserted here). With
    // the core's `validate` and symbolic shapes in the formula, CBMC did not
    // reach the solver in 20 minutes (RESULTS.md, cost ladder).
    #[cfg(kani)]
    let r: Result<Pool, Error> = {
        assert!(spec::valid(&cfg), "CFG-1: the generated configuration is valid");
        let mut p = gen::pool_of(cfg);
        p.observed_at = now;
        Ok(p)
    };
    #[cfg(not(kani))]
    let r = Pool::new(cfg, now);
    // PROP: CFG-1
    assert!(r.is_ok(), "CFG-1: a valid configuration is accepted");
    if let Ok(p) = &r {
        assert_inv(p, &Ghost::init(p)); // PROP: CFG-1 (init satisfies INV)
    }
    cover!(r.is_ok(), "init inv: Ok");
}

/// `h_validate`: CFG-2. `validate` agrees with the spec on any configuration
/// within the bounds, and an accepted configuration has every reference in
/// range, vectors of length `n`, requirements strictly earlier and distinct,
/// and bounded values.
pub fn validate(src: &mut impl Src) {
    let c = src.cfg();
    // 128- and 129-byte strings: plain mode only (as `h_init`, deviation 23).
    let cfg = gen::raw_config(src, &c, INIT_LONG);
    let v = cfg.validate();
    let ok = v.is_ok();
    // PROP: CFG-2
    assert!(ok == spec::valid(&cfg), "CFG-2: validate = spec");
    if let Err(e) = v {
        assert!(e == Error::InvalidConfig, "CFG-2: only InvalidConfig");
    }
    if ok {
        let n = cfg.metrics.len();
        assert!(n >= 1 && !cfg.terms.is_empty() && !cfg.recipes.is_empty(), "CFG-2: nonempty");
        for t in &cfg.terms {
            assert!((t.metric as usize) < n, "CFG-2: term metric in range");
            assert!(spec::bounded(t.target as spec::Z) && t.weight >= 1 && t.weight <= 1000, "CFG-2: term values");
        }
        for m in &cfg.metrics {
            assert!(
                spec::bounded(m.min as spec::Z) && spec::bounded(m.max as spec::Z) && m.min <= m.initial && m.initial <= m.max,
                "CFG-2: metric bounds"
            );
        }
        for (i, r) in cfg.recipes.iter().enumerate() {
            assert!(r.reserve.len() == n && r.complete.len() == n, "CFG-2: vectors of length n");
            for x in r.reserve.iter() {
                assert!(spec::bounded(*x as spec::Z), "CFG-2: deltas bounded");
            }
            for x in r.complete.iter() {
                assert!(spec::bounded(*x as spec::Z), "CFG-2: deltas bounded");
            }
            assert!(r.max_units >= 1 && r.max_units <= 100, "CFG-2: max_units");
            for (j, (p, u)) in r.requires.iter().enumerate() {
                assert!((*p as usize) < i && *u >= 1 && *u <= 100, "CFG-2: requires strictly earlier");
                for (q, _) in &r.requires[..j] {
                    assert!(q != p, "CFG-2: requires distinct");
                }
            }
        }
    }
    cover!(ok, "validate: Ok");
    // F-4: `validate` accepts a recipe whose actor is its executor.
    cover!(
        ok && !cfg.recipes.is_empty() && spec::eq_str(&cfg.recipes[0].actor, &cfg.recipes[0].executor),
        "validate: Ok with actor = executor (F-4)"
    );
    cover!(ok && cfg.recipes.len() == 3 && cfg.recipes[2].requires.len() == 2, "validate: Ok with two requirements");
    cover!(!ok && cfg.name.is_empty(), "validate: empty name");
    #[cfg(not(kani))]
    cover!(!ok && cfg.name.len() == 129, "validate: name too long");
    cover!(!ok && cfg.metrics.is_empty(), "validate: no metrics");
    cover!(!ok && cfg.terms.is_empty() && !cfg.metrics.is_empty(), "validate: no terms");
    cover!(!ok && cfg.recipes.is_empty() && !cfg.metrics.is_empty() && !cfg.terms.is_empty(), "validate: no recipes");
    cover!(
        !ok && spec::short(&cfg.name)
            && spec::short(&cfg.owner)
            && cfg.metrics.len() == 1
            && cfg.metrics[0].min > cfg.metrics[0].max,
        "validate: min > max"
    );
    cover!(
        !ok && cfg.recipes.len() >= 2 && cfg.recipes[1].requires.len() == 2 && cfg.recipes[1].requires[0].0 == cfg.recipes[1].requires[1].0,
        "validate: duplicate requirement"
    );
    cover!(!ok && cfg.recipes.len() >= 1 && cfg.recipes[0].requires.len() == 1, "validate: requirement not earlier");
}

/// `h_energy`: NUM-1. For a valid configuration and bounded values of
/// length `n`, `energy_terms` and `energy` succeed, each term is exactly
/// `w·r²` (≤ 4e15) and `energy` is their exact sum; other vectors fail Bounds.
pub fn energy(src: &mut impl Src) {
    let c = src.cfg();
    let cfg = gen::config(src, &c);
    let n = cfg.metrics.len();
    // Under Kani, `Pool::new`'s result (CFG-1, `h_init`) is built directly:
    // validating a configuration that is valid by construction costs more
    // than the energy itself (RESULTS.md, cost ladder).
    #[cfg(kani)]
    let p = gen::pool_of(cfg);
    #[cfg(not(kani))]
    let p = Pool::new(cfg, 0).expect("generated config is valid");
    let len = if src.bool() { n } else { src.below(gen::MAX_M as u32 + 2) as usize };
    let mut v = Vec::with_capacity(gen::MAX_M as usize + 1);
    let mut in_range = true;
    for i in 0..gen::MAX_M as usize + 1 {
        if i < len {
            let x = if src.bool() {
                gen::val(src, c.val)
            } else {
                gen::raw_i64(src, c.val)
            };
            if !spec::bounded(x as spec::Z) {
                in_range = false;
            }
            v.push(x);
        }
    }
    let t = p.energy_terms(&v);
    let e = p.energy(&v);
    if len == n && in_range {
        if c.part & PART_TX != 0 {
            // PROP: NUM-1
            assert!(t.is_ok() && e.is_ok(), "NUM-1: energy cannot fail on bounded values");
        }
        let (Ok(t), Ok(e)) = (t, e) else { return };
        if c.part & PART_TX != 0 {
            assert!(t.len() == p.config.terms.len(), "NUM-1: one value per term");
        }
        if c.part & PART_POST != 0 {
            // PROP: NUM-1
            let x = spec::vals(&p.config, &v);
            let mut sum: u128 = 0;
            for (k, tm) in p.config.terms.iter().enumerate() {
                let want = spec::term(tm, x[tm.metric as usize]);
                assert!(want <= 4_000_000_000_000_000, "NUM-1: term <= 1000 * (2e6)^2");
                #[cfg(not(kani))]
                assert!(t[k] as spec::Z == want, "NUM-1: term exact");
                #[cfg(kani)]
                exact_term(t[k], tm, x[tm.metric as usize]);
                sum += t[k] as u128;
            }
            assert!(e as u128 == sum, "NUM-1: energy = exact sum of terms");
        }
        if c.part & PART_COV != 0 {
            cover!(e > 1_000_000_000_000_000 / 1000, "energy: large energy");
            cover!(e == 0, "energy: zero energy");
        }
    } else {
        if c.part & PART_TX != 0 {
            // PROP: NUM-1
            assert!(t == Err(Error::Bounds) && e == Err(Error::Bounds), "NUM-1: other vectors fail Bounds");
        }
        if c.part & PART_COV != 0 {
            cover!(len != n, "energy: wrong length");
            cover!(len == n && !in_range, "energy: value out of range");
        }
    }
}

/// NUM-1 exactness of one term under Kani, without multiplier equivalence
/// (an `i128` product against the code's `u64` product does not finish in 30
/// minutes over the full range, RESULTS.md): the code's term equals `w·r²`
/// modulo 2^64 (a wrapping product, the same circuit), and `w·r² ≤ 4e15 <
/// 2^64` because `r ≤ 2e6` and `w ≤ 1000` (asserted linearly), so equality
/// modulo 2^64 is equality.
#[cfg(kani)]
fn exact_term(got: u64, t: &Term, v: spec::Z) {
    let d = v - t.target as spec::Z;
    let r = match t.shape {
        Shape::Target => {
            if d < 0 {
                -d
            } else {
                d
            }
        }
        Shape::Excess => {
            if d > 0 {
                d
            } else {
                0
            }
        }
        Shape::Deficit => {
            if d < 0 {
                -d
            } else {
                0
            }
        }
    };
    assert!(r >= 0 && r <= 2_000_000 && t.weight <= 1000, "NUM-1: r <= 2e6, w <= 1000");
    let r = r as u64;
    let m = r.wrapping_mul(r).wrapping_mul(t.weight as u64);
    assert!(got == m, "NUM-1: term exact (mod 2^64, and below 2^64)");
}

/// `h_energy_max`: NUM-1 at the largest configuration: 64 terms of weight
/// 1000 at distance 2e6, energy = 64·1000·(2e6)² = 2.56e17, exact.
pub fn energy_max(_src: &mut impl Src) {
    let mut cfg = Config {
        name: "p".into(),
        owner: "o_".into(),
        metrics: vec![Metric {
            name: "m".into(),
            unit: "u".into(),
            initial: 0,
            min: -1_000_000,
            max: 1_000_000,
        }],
        terms: Vec::with_capacity(64),
        recipes: vec![Recipe {
            name: "r".into(),
            actor: "a1".into(),
            executor: "x1".into(),
            reserve: vec![0],
            complete: vec![0],
            max_units: 1,
            requires: vec![],
        }],
        max_age_seconds: 0,
    };
    for k in 0..64 {
        cfg.terms.push(Term {
            metric: 0,
            target: 1_000_000,
            weight: 1000,
            shape: if k % 2 == 0 { Shape::Target } else { Shape::Deficit },
        });
    }
    // Under Kani, `Pool::new`'s result is built directly (as in `energy`):
    // without the capacity model CBMC does not fold the vector lengths, and
    // `validate` unrolled every requirement loop 66 times inside a recipe
    // loop unrolled 66 times (30 min were not enough).
    #[cfg(kani)]
    let p = gen::pool_of(cfg);
    #[cfg(not(kani))]
    let p = Pool::new(cfg, 0).expect("valid");
    // PROP: NUM-1 (64-term worst case)
    let e = p.energy(&[-1_000_000]);
    assert!(e == Ok(256_000_000_000_000_000), "NUM-1: 64-term worst case exact");
    let t = p.energy_terms(&[-1_000_000]).expect("terms");
    assert!(t.len() == 64 && t[63] == 4_000_000_000_000_000, "NUM-1: worst term exact");
    cover!(e.is_ok(), "energy max: Ok");
}

// ---------------------------------------------------------------------------
// Reads
// ---------------------------------------------------------------------------

/// `h_preview`: RD-PREVIEW. `allowed` iff the spec's admission accepts;
/// `reason`, `candidate`, `before`, `after` and the term strings as coded;
/// no mutation; allowed and version < MAX implies submit succeeds with the
/// previewed candidate.
pub fn preview(src: &mut impl Src) {
    let c = src.cfg();
    let Some((p, _g)) = gen::inv_state(src, &c) else {
        return;
    };
    let Op::Submit { caller, req, now } = gen::op(src, &p, SUBMIT, c.val) else {
        return;
    };
    let pre = gen::copy(&p);
    let d = p.preview(caller, &req, now);
    let cfg = &p.config;
    let v = vals_of(&p);
    let raw = match spec::rcp(cfg, req.recipe) {
        Some(r) if req.units <= 100 => spec::add(cfg, &v, &r.reserve, req.units),
        _ => None,
    };
    // `reason` read once into a local array (each read of the heap string is
    // a case split over the string objects; RESULTS.md, cost ladder).
    let rs = spec::Text::<16>::of(if c.part & (PART_TX | PART_COV) != 0 { &d.reason } else { "" });
    if c.part & PART_TX != 0 {
        // PROP: RD-PREVIEW
        assert!(spec::same_state(&p, &pre), "RD-PREVIEW: no mutation");
        let want = spec::candidate(&p, caller, &req, now);
        assert!(d.allowed == want.is_ok(), "RD-PREVIEW: allowed iff candidate Ok");
        let reason = match &want {
            Ok(_) => "Allowed",
            Err((e, _)) => spec::reason(e),
        };
        assert!(rs.eq(reason), "RD-PREVIEW: reason");
        match (&d.candidate, &raw) {
            (None, None) => {}
            (Some(a), Some(b)) => {
                let mut ok = a.len() == spec::n(cfg);
                for i in 0..M {
                    if i < spec::n(cfg) && i < a.len() && a[i] as spec::Z != b[i] {
                        ok = false;
                    }
                }
                assert!(ok, "RD-PREVIEW: candidate values");
            }
            _ => panic!("RD-PREVIEW: candidate presence"),
        }
        if d.allowed && p.version < u32::MAX {
            let mut q = gen::copy(&p);
            let r = q.submit(caller, req.clone(), now);
            assert!(r.is_ok(), "RD-PREVIEW: allowed and version < MAX implies submit Ok");
            assert!(
                matches!(&d.candidate, Some(v) if spec::eq_i64s(&q.values, v)),
                "RD-PREVIEW: submit reserves the previewed candidate"
            );
        }
    }
    if c.part & PART_POST != 0 {
        // The strings are the decimal numerals of the spec's numbers
        // (`spec::is_dec`: parsed, not formatted; RESULTS.md, cost ladder).
        let e0 = spec::energy(cfg, &v) as u64;
        assert!(spec::is_dec(&d.before, e0), "RD-PREVIEW: before");
        assert!(
            match (&d.after, &raw) {
                (Some(a), Some(x)) => spec::is_dec(a, spec::energy(cfg, x) as u64),
                (None, None) => true,
                _ => false,
            },
            "RD-PREVIEW: after"
        );
        let nt = cfg.terms.len();
        let mut ok = d.terms_before.len() == nt && d.terms_after.len() == if raw.is_some() { nt } else { 0 };
        for (i, t) in cfg.terms.iter().enumerate() {
            if i < d.terms_before.len() && !spec::is_dec(&d.terms_before[i], spec::term(t, v[t.metric as usize]) as u64) {
                ok = false;
            }
            if let Some(x) = &raw {
                if i < d.terms_after.len() && !spec::is_dec(&d.terms_after[i], spec::term(t, x[t.metric as usize]) as u64) {
                    ok = false;
                }
            }
        }
        assert!(ok, "RD-PREVIEW: term strings");
    }
    if c.part & PART_COV != 0 {
        cover!(d.allowed, "preview: allowed");
        cover!(!d.allowed && d.candidate.is_some(), "preview: rejected with a candidate");
        cover!(!d.allowed && d.candidate.is_none(), "preview: rejected without a candidate");
        cover!(rs.eq("Energy"), "preview: Energy");
        cover!(rs.eq("Bounds"), "preview: Bounds");
    }
}

/// `h_best`: RD-BEST. `best_quantity` returns the admissible quantity in
/// `1..=min(units, 100)` with least energy after reservation, ties to the
/// larger quantity, or `None`; and it is sound (the result is admitted).
///
/// Under Kani the core's `Pool::candidate` is stubbed by a free result
/// (`model::candidate`, deviation 24): the harness shows that
/// `best_quantity` is exactly this search over whatever `candidate` returns
/// (each quantity evaluated once, with the request's other fields), ranked
/// by whatever `energy` (also stubbed) returns on each `Ok` candidate's
/// values, for requests of up to 7 units; `h_preview`, `h_step_submit_tx`
/// and `h_step_submit_post` show that `candidate` is the spec's, and
/// `h_energy` that `energy` is. With the real
/// `candidate` (two admissions of the core and two of the spec, units ≤ 2)
/// the formula had 161.9M clauses and timed out (RESULTS.md, cost ladder).
/// Plain mode runs the real `candidate` with up to 3 units (`max_units` ≤ 3:
/// larger requests only add `InvalidUnits` candidates) and calls `submit`
/// on the result.
const BEST_UNITS: u32 = if cfg!(kani) { 7 } else { 3 };

/// The candidate values of `r` (`None` if it is not admissible): under Kani
/// the stub's recorded result for `r.units`, in plain mode the spec's.
#[cfg(kani)]
fn best_cand(p: &Pool, _caller: &str, r: &Request, _now: u64) -> Option<Vals> {
    use std::sync::atomic::Ordering::SeqCst;
    let k = &crate::model::CAND[r.units as usize];
    if k.calls.load(SeqCst) == 0 || !k.ok.load(SeqCst) {
        return None;
    }
    let n = spec::n(&p.config);
    let mut v = [0; M];
    for i in 0..M {
        if i < n {
            v[i] = k.vals[i].load(SeqCst);
        }
    }
    Some(v)
}

#[cfg(not(kani))]
fn best_cand(p: &Pool, caller: &str, r: &Request, now: u64) -> Option<Vals> {
    spec::candidate(p, caller, r, now).ok()
}

/// The energy of the candidate values `v` of quantity `u` (`None` if it
/// fails): in plain mode the spec's; under Kani the result the stub of
/// `Pool::energy` returned when the core called it on that candidate
/// (`model::energy`, deviation 24; `h_energy`: the real `energy` is `Ok` and
/// the spec's on every bounded vector, NUM-1). `best` asserts below that
/// the core called it exactly once on each `Ok` candidate, with its values.
#[cfg(kani)]
fn best_energy(_p: &Pool, u: u32, _v: &Vals) -> Option<i128> {
    use std::sync::atomic::Ordering::SeqCst;
    let k = &crate::model::ENERGY[u as usize];
    if k.ok.load(SeqCst) {
        Some(k.e.load(SeqCst) as i128)
    } else {
        None
    }
}

#[cfg(not(kani))]
fn best_energy(p: &Pool, _u: u32, v: &Vals) -> Option<i128> {
    Some(spec::energy(&p.config, v) as i128)
}

pub fn best(src: &mut impl Src) {
    let c = src.cfg();
    let Some((p, _g)) = gen::inv_state(src, &c) else {
        return;
    };
    let Op::Submit { caller, req, now } = gen::op(src, &p, SUBMIT, c.val) else {
        return;
    };
    // Cost ladder: the search runs min(units, 100) admissions.
    assume!(req.units <= BEST_UNITS);
    let got = p.best_quantity(caller, &req, now);
    let mut best: Option<(i128, u32)> = None;
    let mut tie = false;
    for u in 1..=BEST_UNITS {
        if u <= req.units {
            let r2 = Request {
                units: u,
                ..req.clone()
            };
            if let Some(e) = best_cand(&p, caller, &r2, now).and_then(|v| best_energy(&p, u, &v)) {
                match best {
                    None => best = Some((e, u)),
                    Some((be, _)) => {
                        if e <= be {
                            tie = e == be;
                            best = Some((e, u));
                        }
                    }
                }
            }
        }
    }
    let want = best.map(|(_, u)| Request {
        units: u,
        ..req.clone()
    });
    // PROP: RD-BEST
    assert!(got == want, "RD-BEST: least energy, ties to more units");
    // Under Kani: `candidate` was called exactly once for each quantity in
    // `1..=units` (units ≤ 7 < 100), with the caller (the same string), the
    // recipe, version and expiry of the request and the same `now`; `energy`
    // exactly once on each `Ok` candidate's values and on nothing else.
    #[cfg(kani)]
    {
        use std::sync::atomic::Ordering::SeqCst;
        assert!(
            crate::model::CAND_OUT.load(SeqCst) == 0,
            "RD-BEST: candidate only for quantities in 1..=units"
        );
        assert!(
            crate::model::ENERGY[0].calls.load(SeqCst) == 0,
            "RD-BEST: energy only after an admissible candidate"
        );
        for u in 1..crate::model::CAND_N {
            let k = &crate::model::CAND[u];
            let calls = k.calls.load(SeqCst);
            assert!(
                calls == (u as u32 <= req.units) as u8,
                "RD-BEST: candidate evaluated once for each quantity in 1..=units"
            );
            let ek = &crate::model::ENERGY[u];
            assert!(
                ek.calls.load(SeqCst) == (calls == 1 && k.ok.load(SeqCst)) as u8,
                "RD-BEST: energy evaluated once for each admissible quantity"
            );
            assert!(
                ek.calls.load(SeqCst) == 0 || ek.args.load(SeqCst),
                "RD-BEST: energy of the candidate's values"
            );
            if calls == 1 {
                assert!(
                    k.caller.load(SeqCst) == caller.as_ptr() as usize
                        && k.caller_len.load(SeqCst) == caller.len()
                        && k.recipe.load(SeqCst) == req.recipe
                        && k.version.load(SeqCst) == req.version
                        && k.expires_at.load(SeqCst) == req.expires_at
                        && k.now.load(SeqCst) == now,
                    "RD-BEST: candidate called with the request's other fields"
                );
            }
        }
    }
    // Soundness: `got` is a request whose candidate is Ok. Under Kani that
    // is the stub's; with `h_preview` (candidate Ok iff the spec's) and
    // `h_step_submit_tx` (submit is the spec's: Ok below `u32::MAX`) the
    // core's submit accepts it. Plain mode calls submit.
    #[cfg(not(kani))]
    if let Some(r) = &got {
        let mut q = gen::copy(&p);
        if p.version < u32::MAX {
            assert!(q.submit(caller, r.clone(), now).is_ok(), "RD-BEST: sound (submit accepts it)");
        }
    }
    cover!(got.is_none(), "best: None");
    cover!(matches!(&got, Some(r) if r.units == req.units), "best: all requested units");
    cover!(matches!(&got, Some(r) if r.units < req.units), "best: fewer units than requested");
    cover!(tie && got.is_some(), "best: a tie at the least energy, to the larger quantity");
}

// ---------------------------------------------------------------------------
// Liveness, wedge, traces, limits, canary
// ---------------------------------------------------------------------------

/// `h_live1`: LIVE-1. From an INV state with `B = 0` and version < MAX, the
/// executor can complete every Dispatched, Active or Unknown record.
pub fn live1(src: &mut impl Src) {
    let c = src.cfg();
    let Some((mut p, g)) = gen::inv_state(src, &c) else {
        return;
    };
    assume!(spec::healthy_base(&p.config, &g));
    assume!(p.version < u32::MAX);
    assume!(!p.records.is_empty());
    let id = src.below(p.records.len() as u32);
    let c0 = spec::rec(&p.records, id).expect("in range").clone();
    let st = c0.status.clone();
    assume!(matches!(st, Status::Dispatched | Status::Active | Status::Unknown));
    let mut others = 0;
    for c in &p.records {
        if spec::open(&c.status) {
            others += 1;
        }
    }
    let ex = spec::rcp_of(&p.config, c0.recipe).executor.clone();
    let r = p.settle(&ex, id, true);
    // PROP: LIVE-1
    assert!(r.is_ok(), "LIVE-1: the executor can complete an in-flight record");
    cover!(st == Status::Dispatched, "live1: from Dispatched");
    cover!(st == Status::Active, "live1: from Active");
    cover!(st == Status::Unknown, "live1: from Unknown");
    cover!(others >= 3, "live1: with two other open records");
}

/// `h_wedge`: F-1 from `Pool::new`. After a disturbing `observe`, a recovery
/// hedge is admitted and dispatched; then settle(completed), settle(cancelled),
/// cancel and observe all fail, so the record can never become terminal and
/// the pool is frozen for observations. The cover must be SATISFIED.
/// The wedge harnesses' initial pool: `Pool::new(cfg, 100)` for a valid
/// configuration. Under Kani the roles are fixed (owner `o_`, every actor
/// `a1`, every executor `x1`) and `new`'s `Ok` value is built directly
/// (CFG-1, `h_init`): with symbolic roles every `==` on an account is a case
/// split over the four accounts, and validating a configuration that is
/// valid by construction is a formula of its own; with both, `h_wedge` ran
/// out of 40 GB (RESULTS.md, cost ladder). Plain mode keeps both.
fn wedge_new(cfg: Config) -> Pool {
    #[cfg(kani)]
    {
        let mut cfg = cfg;
        cfg.owner = ACCTS[0].into();
        for r in cfg.recipes.iter_mut() {
            r.actor = ACCTS[1].into();
            r.executor = ACCTS[2].into();
        }
        let mut p = gen::pool_of(cfg);
        p.observed_at = 100;
        p
    }
    #[cfg(not(kani))]
    Pool::new(cfg, 100).expect("valid")
}

pub fn wedge(src: &mut impl Src) {
    let c = src.cfg();
    let cfg = gen::init_config(src, &c);
    let mut p = wedge_new(cfg);
    let owner = p.config.owner.clone();
    let actor = p.config.recipes[0].actor.clone();
    let ex = p.config.recipes[0].executor.clone();
    let n = p.config.metrics.len();
    let mut obs = Vec::with_capacity(gen::MAX_M as usize);
    for _ in 0..n {
        obs.push(gen::val(src, c.val));
    }
    let o1 = p.observe(&owner, obs, 100);
    let s = p.submit(
        &actor,
        Request {
            recipe: 0,
            units: 1,
            version: p.version,
            expires_at: 200,
        },
        100,
    );
    let d = p.dispatch(&actor, 0, 100);
    let reached = o1.is_ok() && s == Ok(0) && d.is_ok();
    let before = gen::copy(&p);
    let st = p.settle(&ex, 0, true);
    let sf = p.settle(&ex, 0, false);
    let ca = p.cancel(&owner, 0, 100);
    let vv = gen::copy_vec(&p.values, M + 1);
    let ob = p.observe(&owner, vv, 100);
    let wedged = reached
        && st == Err(Error::Bounds)
        && sf == Err(Error::Bounds)
        && ca == Err(Error::Pending)
        && ob == Err(Error::Pending);
    if wedged {
        assert!(spec::same_state(&p, &before), "F-1: the failed calls change nothing"); // PROP: TX-0
        // The disturbed base, the reservation back inside, the record open.
        assert!(p.records[0].status == Status::Dispatched, "F-1: record still open");
    }
    // F-1 (finding): must be SATISFIED.
    cover!(wedged, "wedge: F-1 reachable (settle both ways Bounds, cancel and observe Pending)");
    cover!(reached, "wedge: disturbed state, hedge admitted and dispatched");
}

/// `h_wedge_healthy`: F-2 from `Pool::new`, with no observe (so `B = 0`
/// throughout). A position (recipe 0) and a hedge (recipe 1) are admitted and
/// dispatched; the hedge completes, relying on the position's reservation.
/// Then the executor's honest `settle(position, cancelled)` fails `Bounds`
/// (its release would push the point outside `[min, max]`), `cancel` fails
/// `Pending` and `observe` fails `Pending`: under an honest executor the
/// position can never become terminal. `settle(completed)` still succeeds
/// (LIVE-1 is unaffected). The cover must be SATISFIED. Under Kani the last
/// three calls run from every healthy INV state with a Dispatched record 0
/// and a Completed record 1 (the state the script reaches).
pub fn wedge_healthy(src: &mut impl Src) {
    let c = src.cfg();
    // Under Kani from a healthy INV state (deviation 19): with the script
    // from `Pool::new` every step's outcome is symbolic, so the record
    // vector's length is too from the first submit on, and the nine calls on
    // the core ran out of 40 GB, even on one concrete configuration. Plain
    // mode runs the script from `Pool::new` on random configurations.
    #[cfg(kani)]
    {
        let Some((mut p, g)) = gen::inv_state(src, &c) else {
            return;
        };
        assume!(spec::healthy_base(&p.config, &g));
        assume!(p.version < u32::MAX);
        assume!(p.records.len() == 2);
        assume!(p.records[0].status == Status::Dispatched && p.records[1].status == Status::Completed);
        let _ = wedge_healthy_tail(&mut p);
    }
    #[cfg(not(kani))]
    {
        let cfg = gen::init_config(src, &c);
        wedge_healthy_on(cfg);
    }
}

/// The calls of F-2 on a state in which record 0 (the position) is open:
/// the executor's honest `settle(cancelled)`, the owner's `cancel`, and
/// `observe`. True iff they fail `Bounds`, `Pending` and `Pending`. Plain
/// mode also asserts TX-0 for them and LIVE-1 for the position; under Kani
/// those are `h_step_{settle,cancel,observe}_tx`'s and `h_live1`'s over the
/// same states (INV, `B = 0`, version < MAX, a Dispatched record).
fn wedge_healthy_tail(p: &mut Pool) -> bool {
    let caller = |s: &str| spec::ACCTS.iter().copied().find(|a| *a == s).unwrap_or("z_");
    let owner = caller(&p.config.owner);
    let x0 = caller(&spec::rcp_of(&p.config, p.records[0].recipe).executor);
    #[cfg(not(kani))]
    let before = gen::copy(p);
    let sf = p.settle(x0, 0, false);
    let ca = p.cancel(owner, 0, 100);
    let vv = gen::copy_vec(&p.values, M + 1);
    let ob = p.observe(owner, vv, 100);
    let wedged = sf == Err(Error::Bounds) && ca == Err(Error::Pending) && ob == Err(Error::Pending);
    #[cfg(not(kani))]
    if wedged {
        assert!(spec::same_state(p, &before), "F-2: the failed calls change nothing"); // PROP: TX-0
        assert!(p.records[0].status == Status::Dispatched, "F-2: position still open");
        // PROP: LIVE-1 (unaffected by F-2): the executor can still complete it.
        let mut q = gen::copy(p);
        assert!(q.settle(x0, 0, true).is_ok(), "LIVE-1: settle(completed) still Ok");
    }
    // F-2 (finding): must be SATISFIED.
    cover!(wedged, "wedge healthy: F-2 reachable (settle(cancelled) Bounds, cancel and observe Pending, B = 0)");
    wedged
}

/// A small F-2 instance (plain mode, `f2_small_instance`): one metric in
/// `[0, 4]` from 2, target 4 (weight 1); a position (recipe 0) reserving +2,
/// and a hedge
/// (recipe 1) reserving nothing and completing -3, which is in bounds only
/// with the position's reservation (4 - 3 = 1, while 2 - 3 = -1 is not).
pub fn f2_instance() -> Config {
    let recipe = |name: &str, reserve: i64, complete: i64| pool_core::Recipe {
        name: name.into(),
        actor: ACCTS[1].into(),
        executor: ACCTS[2].into(),
        reserve: vec![reserve],
        complete: vec![complete],
        max_units: 1,
        requires: vec![],
    };
    Config {
        name: "p".into(),
        owner: ACCTS[0].into(),
        metrics: vec![pool_core::Metric {
            name: "m".into(),
            unit: "u".into(),
            initial: 2,
            min: 0,
            max: 4,
        }],
        terms: vec![Term {
            metric: 0,
            target: 4,
            weight: 1,
            shape: pool_core::Shape::Target,
        }],
        recipes: vec![recipe("c", 2, 0), recipe("h", 0, -3)],
        max_age_seconds: 0,
    }
}

/// The F-2 script from `Pool::new(cfg)`; true iff the wedge is reached.
pub fn wedge_healthy_on(cfg: Config) -> bool {
    if cfg.recipes.len() < 2 {
        return false;
    }
    let mut p = wedge_new(cfg);
    let mut g = Ghost::init(&p);
    let a0 = p.config.recipes[0].actor.clone();
    let (a1, x1) = (p.config.recipes[1].actor.clone(), p.config.recipes[1].executor.clone());
    let caller = |s: &str| spec::ACCTS.iter().copied().find(|a| *a == s).unwrap_or("z_");
    let req = |recipe: u32, v: u32| Request {
        recipe,
        units: 1,
        version: v,
        expires_at: 200,
    };
    let script = [
        Op::Submit { caller: caller(&a0), req: req(0, 0), now: 100 },
        Op::Submit { caller: caller(&a1), req: req(1, 1), now: 100 },
        Op::Dispatch { caller: caller(&a0), id: 0, now: 100 },
        Op::Dispatch { caller: caller(&a1), id: 1, now: 100 },
        Op::Settle { caller: caller(&x1), id: 1, completed: true },
    ];
    // Each step against the spec, and the reached state against INV with
    // its ghost.
    let mut reached = true;
    for op in &script {
        let pre = gen::copy(&p);
        let x = spec::expected(&pre, op);
        let res = spec::apply(&mut p, op);
        assert!(res == x.res, "TX: exact result along the F-2 script");
        g = spec::ghost_step(&g, &pre, op, &x);
        if res.is_err() {
            reached = false;
        }
    }
    if !reached {
        return false;
    }
    // A healthy INV state: no observe, so B = 0 (PROP: INV-HARD).
    assert!(spec::healthy_base(&p.config, &g), "F-2: B = 0 (no observe)");
    assert_inv(&p, &g);
    cover!(true, "wedge healthy: position and hedge dispatched, hedge completed");
    wedge_healthy_tail(&mut p)
}

/// `h_bmc_from_init` (plain mode): up to `depth` operations of any kind
/// from `Pool::new`. INV (with INV-VER) after every step, and STALE-1 over
/// the trace: accepted requests carry strictly increasing versions, so no
/// accepted request can be accepted again. Under Kani the harnesses run
/// [`bmc_two`] (deviation 20).
pub fn bmc_from_init(src: &mut impl Src, depth: usize) {
    let c = src.cfg();
    let cfg = gen::init_config(src, &c);
    let now = src.u64();
    let mut p = Pool::new(cfg, now).expect("valid");
    let mut g = Ghost::init(&p);
    assert_inv(&p, &g);
    let mut accepted: Vec<Request> = Vec::with_capacity(depth);
    let mut completed = false;
    let mut replay_rejected = false;
    let mut observed_after = false;
    for _ in 0..depth {
        let k = src.below(gen::KINDS);
        let op = if src.bool() && !accepted.is_empty() && k == SUBMIT {
            replay(src, &p, &accepted[0])
        } else {
            gen::op(src, &p, k, c.val)
        };
        let x = spec::expected(&p, &op);
        let h = spec::ghost_step(&g, &p, &op, &x);
        let pre = if c.part & PART_REF != 0 { Some(gen::copy(&p)) } else { None };
        let res = spec::apply(&mut p, &op);
        if let Some(pre) = &pre {
            // PROP: REF-1 REF-2 REF-3 (plain mode: this body is plain-only;
            // up to `depth` records, so an image of 8)
            crate::tla::assert_refines::<2, 2, 2, 2, 8>(pre, &g.base, g.k0, &op, &res, &p);
        }
        g = h;
        assert!(res == x.res, "TX: exact result along the trace");
        assert_inv(&p, &g);
        if let Op::Submit { req, .. } = &op {
            let replay = accepted.iter().any(|a| a == req);
            if res.is_ok() {
                // PROP: STALE-1
                assert!(!replay, "STALE-1: an accepted request never replays");
                for a in &accepted {
                    assert!(req.version > a.version, "STALE-1: accepted versions strictly increase");
                }
                accepted.push(req.clone());
            } else if replay {
                replay_rejected = true;
            }
        }
        if res.is_ok() {
            if let Op::Settle { completed: true, .. } = op {
                completed = true;
            }
            if let Op::Observe { .. } = op {
                if completed {
                    observed_after = true;
                }
            }
        }
    }
    cover!(replay_rejected, "bmc: a replayed request is rejected");
    cover!(accepted.len() >= 2, "bmc: two accepted requests");
    cover!(completed, "bmc: a record completes");
    cover!(observed_after, "bmc: observe after a completion");
}

/// A replay of the accepted request `req` by its recipe's actor, at any
/// time.
fn replay(src: &mut impl Src, p: &Pool, req: &Request) -> Op {
    let actor = &spec::rcp_of(&p.config, req.recipe).actor;
    let caller = spec::ACCTS.iter().copied().find(|a| spec::eq_str(a, actor)).unwrap_or("z_");
    Op::Submit {
        caller,
        req: req.clone(),
        now: src.u64(),
    }
}

/// `h_bmc_from_init_*` (deviation 20): two operations from `Pool::new`, the
/// first a submit (`first == SUBMIT`) or a pause or observe (from
/// `Pool::new` there is no record, so every other kind fails `NotFound` or
/// earlier and changes nothing), the second of kind `last` (any if `None`).
/// After the first operation the harness asserts the exact result and the
/// exact post-state (the spec's), then continues from the same state
/// rebuilt with constant shapes: the core's post-state has a record count
/// and value vectors whose lengths depend on the outcome, and every later
/// read of them is a case split (RESULTS.md, cost ladder). After a submit
/// it continues from its `Ok` outcome only: an `Err` leaves the initial
/// pool (asserted), from which the pause/observe harness continues too (a
/// pause by a non-owner fails). INV (with INV-VER from `Init`) after both
/// operations, and STALE-1 across them.
pub fn bmc_two(src: &mut impl Src, first: u32, last: Option<u32>) {
    let c = src.cfg();
    let cfg = gen::init_config(src, &c);
    let now = src.u64();
    // Under Kani `new`'s `Ok` value is built directly (CFG-1: `h_init`,
    // `h_validate`, `h_init_inv`).
    #[cfg(kani)]
    let mut p = {
        let mut p = gen::pool_of(cfg);
        p.observed_at = now;
        p
    };
    #[cfg(not(kani))]
    let mut p = Pool::new(cfg, now).expect("valid");
    let g0 = Ghost::init(&p);
    let k0 = if first == SUBMIT {
        SUBMIT
    } else if src.bool() {
        PAUSE
    } else {
        OBSERVE
    };
    let op0 = gen::op(src, &p, k0, c.val);
    let x0 = spec::expected(&p, &op0);
    let g1 = spec::ghost_step(&g0, &p, &op0, &x0);
    let res0 = spec::apply(&mut p, &op0);
    assert!(res0 == x0.res, "TX: exact result along the trace");
    let n = spec::n(&p.config);
    let mut same = p.values.len() == n
        && p.version == x0.version
        && p.observed_at == x0.observed_at
        && p.paused == x0.paused
        && p.records.len() == x0.push.is_some() as usize;
    for i in 0..M {
        if i < n && i < p.values.len() && p.values[i] as Z != x0.values[i] {
            same = false;
        }
    }
    if let Some(cm) = &x0.push {
        if spec::rec(&p.records, 0) != Some(cm) {
            same = false;
        }
    }
    assert!(same, "TX: exact post-state along the trace");
    let req0 = match &op0 {
        Op::Submit { req, .. } => Some(req.clone()),
        _ => None,
    };
    if first == SUBMIT {
        assume!(res0.is_ok());
    }
    let mut values = Vec::with_capacity(M);
    for i in 0..M {
        if i < n {
            values.push(x0.values[i] as i64);
        }
    }
    let mut records = Vec::with_capacity(2);
    if let (true, Some(r)) = (first == SUBMIT, &req0) {
        records.push(Commitment {
            id: 0,
            recipe: r.recipe,
            units: r.units,
            expires_at: r.expires_at,
            status: Status::Reserved,
        });
    }
    let Pool { config, .. } = p;
    let mut p = Pool {
        config,
        values,
        version: x0.version,
        observed_at: x0.observed_at,
        paused: x0.paused,
        records,
    };
    assert_inv(&p, &g1);
    let k1 = match last {
        Some(k) => k,
        None => src.below(gen::KINDS),
    };
    let op1 = match &req0 {
        Some(r) if k1 == SUBMIT && src.bool() => replay(src, &p, r),
        _ => gen::op(src, &p, k1, c.val),
    };
    let x1 = spec::expected(&p, &op1);
    let g2 = spec::ghost_step(&g1, &p, &op1, &x1);
    let res1 = spec::apply(&mut p, &op1);
    assert!(res1 == x1.res, "TX: exact result along the trace");
    assert_inv(&p, &g2);
    let mut replay_rejected = false;
    let mut two = false;
    if let (Some(r0), Op::Submit { req, .. }) = (&req0, &op1) {
        let replay = req == r0;
        if res1.is_ok() {
            // PROP: STALE-1
            assert!(!replay, "STALE-1: an accepted request never replays");
            assert!(req.version > r0.version, "STALE-1: accepted versions strictly increase");
            two = true;
        } else if replay {
            replay_rejected = true;
        }
    }
    cover!(replay_rejected, "bmc: a replayed request is rejected");
    cover!(two, "bmc: two accepted requests");
}

/// `h_slot_cycle_0`, `h_slot_cycle_2` (F-3, slot exhaustion): one
/// submit/cancel cycle by a recipe's actor from a quiet state (no open
/// record, every metric within `[min, max]`): `Pool::new` (`_0`), or an INV
/// state with 2 records (`_2`). If the submit is accepted and the version is
/// below `u32::MAX - 2`, the actor's cancel of the new record is accepted,
/// the cycle's only lasting effects are one more record, Cancelled, and the
/// version + 2 (values, `paused`, `observed_at` and the older records as
/// before), and the same request at the new version is accepted again with
/// the same reserved values. So an actor can repeat the cycle, each time
/// one record more, until submit fails `Full` (`h_full_255`: still admitted
/// at 255 Cancelled records; `h_full_256`: `Full` at 256), and no step
/// removes a record (LIFE-1, `h_step_*_post`; observe included). As in
/// `bmc_two`, each call after the first runs on the previous call's
/// post-state rebuilt with constant shapes, after asserting that the core's
/// post-state is that state (deviation 20).
pub fn slot_cycle(src: &mut impl Src, from_init: bool) {
    let c = src.cfg();
    let p = if from_init {
        let cfg = gen::init_config(src, &c);
        let now = src.u64();
        // Under Kani `new`'s `Ok` value is built directly (CFG-1).
        #[cfg(kani)]
        let p = {
            let mut p = gen::pool_of(cfg);
            p.observed_at = now;
            p
        };
        #[cfg(not(kani))]
        let p = Pool::new(cfg, now).expect("valid");
        p
    } else {
        let Some((p, _g)) = gen::inv_state(src, &c) else {
            return;
        };
        p
    };
    let k = p.records.len();
    let mut quiet = !spec::violating(&p.config, &vals_of(&p));
    for r in &p.records {
        if spec::open(&r.status) {
            quiet = false;
        }
    }
    assume!(quiet);
    // Three effective calls: the version stays below `u32::MAX` (F-5).
    assume!(p.version < u32::MAX - 2);
    let op = gen::op(src, &p, SUBMIT, c.val);
    let Op::Submit { caller, req, now } = &op else {
        return;
    };
    let (caller, now) = (*caller, *now);
    let pre = gen::copy(&p);
    let x = spec::expected(&pre, &op);
    let mut p = p;
    let res = spec::apply(&mut p, &op);
    // PROP: TX-SUBMIT (the cycle's first call: exact result and post-state)
    assert!(res == x.res, "F-3: submit is the spec's");
    let Some(cm) = x.push.clone() else {
        // Not accepted: no cycle.
        return;
    };
    assume!(res.is_ok());
    let n = spec::n(&pre.config);
    let mut same = p.values.len() == n
        && p.version == pre.version + 1
        && p.records.len() == k + 1
        && p.records.get(k) == Some(&cm);
    for i in 0..M {
        if i < n && i < p.values.len() && p.values[i] as Z != x.values[i] {
            same = false;
        }
    }
    assert!(same, "F-3: submit's post-state is the spec's");
    // The post-state with constant shapes: the old records, the new one.
    let rebuild = |cfg: Config, vals: &Vals, version: u32, last: Status| {
        let mut values = Vec::with_capacity(M);
        for i in 0..M {
            if i < n {
                values.push(vals[i] as i64);
            }
        }
        // `k` is a constant under Kani (the generators' fixed counts).
        let mut records = Vec::with_capacity(k + 1);
        for j in 0..k {
            records.push(pre.records[j].clone());
        }
        records.push(Commitment {
            status: last,
            ..cm.clone()
        });
        Pool {
            config: cfg,
            values,
            version,
            observed_at: pre.observed_at,
            paused: pre.paused,
            records,
        }
    };
    let Pool { config, .. } = p;
    let mut q = rebuild(config, &x.values, x.version, Status::Reserved);
    // The cycle's second call: the same caller (the actor) cancels it.
    let ca = q.cancel(caller, k as u32, now);
    // PROP: F-3 (the cycle completes from a quiet state)
    assert!(ca == Ok(()), "F-3: the actor's cancel of its fresh record is accepted");
    let v0 = vals_of(&pre);
    let mut back = q.values.len() == n
        && q.version as u64 == pre.version as u64 + 2
        && q.paused == pre.paused
        && q.observed_at == pre.observed_at
        && q.records.len() == k + 1
        && q.records.get(k).map(|r| r.status == Status::Cancelled) == Some(true);
    for i in 0..M {
        if i < n && i < q.values.len() && q.values[i] as Z != v0[i] {
            back = false;
        }
    }
    for j in 0..k {
        if q.records.get(j) != Some(&pre.records[j]) {
            back = false;
        }
    }
    assert!(back, "F-3: the cycle leaves one more Cancelled record, version + 2, nothing else");
    // The cycle's third call: the same request at the new version.
    let Pool { config, .. } = q;
    let mut q = rebuild(config, &v0, pre.version + 2, Status::Cancelled);
    let again = q.submit(
        caller,
        Request {
            version: q.version,
            ..req.clone()
        },
        now,
    );
    let mut repeat = again == Ok(k as u32 + 1) && q.values.len() == n;
    for i in 0..M {
        if i < n && i < q.values.len() && q.values[i] as Z != x.values[i] {
            repeat = false;
        }
    }
    assert!(repeat, "F-3: the same request is accepted again, with the same values");
    cover!(true, "slot cycle: submit, cancel and submit again by the actor (F-3)");
}

/// A Cancelled record of recipe 0 with id `j`: the records of `full`.
const fn old_record(j: usize) -> Commitment {
    Commitment {
        id: j as u32,
        recipe: 0,
        units: 1,
        expires_at: 0,
        status: Status::Cancelled,
    }
}

/// `K` Cancelled records of recipe 0 with ids `0..K`, evaluated by the
/// compiler: one constant array.
const fn old_records<const K: usize>() -> [Commitment; K] {
    const C: Commitment = old_record(0);
    let mut a = [C; K];
    let mut j = 0;
    while j < K {
        a[j].id = j as u32;
        j += 1;
    }
    a
}

/// The 257 records `full` starts from (then truncated to 255 or 256, so the
/// buffer keeps room for a 257th record: the core's push never reallocates,
/// on mutant 21 either).
const OLD_RECORDS: [Commitment; 257] = old_records::<257>();

/// `h_full_255`, `h_full_256`: the record limit. With 255 or 256 terminal
/// records (`at_limit`; either if `None`), submit is exactly as specified:
/// Full at 256, admitted (when the guards pass) at 255. Under Kani the count
/// is concrete: with a symbolic count every push was guarded, the length
/// symbolic from the first record on, and 63 of the 256 pushes took 9
/// minutes of symbolic execution (RESULTS.md, cost ladder). The records are
/// one constant array moved into the vector (`Vec::from`, then `truncate`),
/// not 255 pushes: with the field-sensitivity option of `run.sh` (each byte
/// of the buffer its own symbol, so that the scans read constants) every
/// push rewrote all 6,168 bytes of the buffer, and the pushes were most of
/// the 8.05M steps of symbolic execution (RESULTS.md, deviation 21, cost
/// ladder 28j).
pub fn full(src: &mut impl Src, at_limit: Option<bool>) {
    let c = src.cfg();
    let cfg = gen::config(src, &c);
    let nm = cfg.metrics.len();
    let count = match at_limit {
        Some(true) => 256,
        Some(false) => 255,
        None => 255 + src.below(2) as usize,
    };
    let old = old_record;
    let mut records = Vec::from(OLD_RECORDS);
    records.truncate(count);
    let mut base = Vec::with_capacity(gen::MAX_M as usize);
    for _ in 0..nm {
        base.push(gen::val(src, c.val));
    }
    // The ghost only feeds INV-WF below (plain mode).
    #[cfg(not(kani))]
    let g = Ghost {
        base: base.clone(),
        k0: count as u32,
        eff: None,
    };
    let mut p = Pool {
        config: cfg,
        values: base,
        version: src.u32(),
        observed_at: src.u64(),
        paused: src.bool(),
        records,
    };
    // INV-DEP holds by construction: every record is of recipe 0, which has
    // no prerequisite (requirements point to earlier recipes). Under Kani it
    // is not evaluated (quadratic in the 256 records; RESULTS.md, cost
    // ladder).
    #[cfg(not(kani))]
    assert!(spec::inv_dep(&p), "harness: INV-DEP by construction");
    let op = gen::op(src, &p, SUBMIT, c.val);
    // The spec's outcome is computed from the pre-state before the call, and
    // the post-state is compared with it and with the known records: no copy
    // of the pool (a copy reads the 256 records back from the heap, and took
    // most of the symbolic execution; RESULTS.md, cost ladder).
    let x = spec::expected(&p, &op);
    #[cfg(not(kani))]
    let h = spec::ghost_step(&g, &p, &op, &x);
    // Under Kani the configuration is not compared (deviation 6: no step
    // changes it, `h_step_submit_post`); at this harness's unwind of 258 the
    // copy and the slice comparisons were unrolled about 257 times each.
    #[cfg(not(kani))]
    let cfg0 = gen::copy_config(&p.config);
    let res = spec::apply(&mut p, &op);
    // PROP: TX-SUBMIT TX-0 TX-VER at the record limit
    assert!(res == x.res, "TX: exact result at the record limit");
    #[cfg(not(kani))]
    assert!(spec::same_config(&p.config, &cfg0), "TX: configuration unchanged");
    let mut ok = p.values.len() == nm
        && p.version == x.version
        && p.observed_at == x.observed_at
        && p.paused == x.paused
        && p.records.len() == count + x.push.is_some() as usize;
    for i in 0..M {
        if i < nm && i < p.values.len() && p.values[i] as spec::Z != x.values[i] {
            ok = false;
        }
    }
    // A concrete trip count (`count`), not the post-state's length (255 or
    // 256 after the conditional push).
    for j in 0..count {
        if p.records.get(j) != Some(&old(j)) {
            ok = false;
        }
    }
    if let Some(cm) = &x.push {
        if p.records.get(count) != Some(cm) {
            ok = false;
        }
    }
    assert!(ok, "TX: exact post-state at the record limit (unchanged on Err: TX-0)");
    if res.is_ok() {
        assert!(p.records.len() == 256, "TX-VER: 256th record");
        // Under Kani INV-WF of the whole state is not evaluated: the 255
        // old records are unchanged (above) and well formed by
        // construction, the new one is the spec's, and the count is 256.
        // The scan after the conditional push ran at about 4 records a
        // minute (RESULTS.md, cost ladder).
        #[cfg(not(kani))]
        assert!(spec::inv_wf(&p, &h), "INV-WF: at most 256 records");
    }
    cover!(res == Err(Error::Full), "full: Full at 256 records");
    cover!(res.is_ok(), "full: Ok at 255 records");
}

/// `h_canary`: must FAIL (on this assertion only): the generator and the core
/// together do reach an accepted submit, so the harness setup is not vacuous.
pub fn canary(src: &mut impl Src) {
    let c = src.cfg();
    let Some((mut p, _g)) = gen::inv_state(src, &c) else {
        return;
    };
    let op = gen::op(src, &p, SUBMIT, c.val);
    let res = spec::apply(&mut p, &op);
    assert!(res.is_err(), "canary: no submit is ever accepted");
}
