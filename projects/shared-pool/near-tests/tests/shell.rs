//! Exact shell tests of pool-contract (SH-1..SH-7, SH-9, SH-10) and the two
//! findings of this layer (NT-F1, NT-F2).
//!
//! Every scenario runs on three paths: the host path (the `#[near]` methods
//! as Rust functions, reload around every call) and the real wasm in two
//! builds (`Plain` = upstream scripts/build.sh, `Near` = `--cfg near` as
//! cargo-near builds). Each call is compared with the core (`Sim`, through
//! `step` / `wasm_diff_step`: result, panic, events, receipts, Borsh state),
//! and the tests below add explicit expectations on top.
//!
//! Each test carries its own tag line. The findings sit under the property
//! they break: NT-F1 under SH-5, NT-F2 under SH-10, NT-F4 under SH-3.
//! RD-PREVIEW here is the shell half only: the `preview` view equals the
//! core's `preview`.
//!
// PROP: SH-1 SH-2 SH-3 SH-4 SH-5 SH-6 SH-7 SH-9 SH-10 RD-PREVIEW

mod common;
use common::*;
use near_sdk::serde_json::{self, json, Value};
use near_sdk::PromiseResult;
use pool_core::{Commitment, Config, Error as E, Metric, Pool, Recipe, Request, Shape, Status, Term};

fn guest(e: E) -> Fail {
    Fail::Guest(e.to_string())
}

/// open_config with one record of recipe 1 (a2, executor x2, complete -1 per
/// unit) for 3 units, dispatched at t=101.
fn dispatched(path: Path) -> Sim {
    let mut s = Sim::new(path, open_config(), 100);
    let r = s.ok(&Ctx::by(A2, 100), submit(1, 3, 0, 150));
    assert_eq!(r.value()["id"], json!(0));
    s.ok(&Ctx::by(A2, 101), Op::Dispatch { id: 0 });
    assert_eq!(s.status(0), Status::Dispatched);
    s
}

// ---------------------------------------------------------------------------
// SH-1: caller() is the predecessor; now() is the block timestamp in seconds
// ---------------------------------------------------------------------------

// PROP: SH-1
#[test]
fn sh1_caller_is_the_predecessor_not_the_signer() {
    big_stack(|| {
        for path in paths() {
            let t = |s: u64| s * 1_000_000_000 + 5;
            let mut s = Sim::new(path, open_config(), 100);
            // A signature relayed by another account is not the actor's call.
            let r = s.ok(&Ctx::new(RELAY, A1, t(101)), submit(0, 1, 0, 150));
            assert_eq!(r.value()["decision"]["reason"], json!("Unauthorized"), "{path:?}");
            assert_eq!(r.value()["id"], Value::Null);
            assert_eq!(r.event()["actor"], json!(RELAY));
            // The actor's own call counts, whoever signed the transaction.
            let r = s.ok(&Ctx::new(A1, Z, t(101)), submit(0, 1, 0, 150));
            assert_eq!(r.value()["id"], json!(0));
            assert_eq!(r.event()["actor"], json!(A1));
            s.err(&Ctx::new(RELAY, A1, t(102)), Op::Dispatch { id: 0 }, guest(E::Unauthorized));
            s.ok(&Ctx::new(A1, RELAY, t(102)), Op::Dispatch { id: 0 });
            s.err(
                &Ctx::new(A1, X1, t(103)),
                Op::Settle { id: 0, completed: true },
                guest(E::Unauthorized),
            );
            s.ok(&Ctx::new(X1, A1, t(103)), Op::Settle { id: 0, completed: true });
            assert_eq!(s.status(0), Status::Completed);
            s.ok(&Ctx::new(A1, A1, t(104)), submit(0, 1, s.pool.version, 150));
            s.err(&Ctx::new(RELAY, OWNER, t(104)), Op::Cancel { id: 1 }, guest(E::Unauthorized));
            s.ok(&Ctx::new(OWNER, RELAY, t(104)), Op::Cancel { id: 1 });
            s.err(&Ctx::new(RELAY, OWNER, t(105)), Op::Pause { paused: true }, guest(E::Unauthorized));
            s.ok(&Ctx::new(OWNER, RELAY, t(105)), Op::Pause { paused: true });
            s.ok(&Ctx::new(OWNER, Z, t(105)), Op::Pause { paused: false });
            s.err(
                &Ctx::new(RELAY, OWNER, t(106)),
                Op::Observe { values: vec![1] },
                guest(E::Unauthorized),
            );
            s.ok(&Ctx::new(OWNER, RELAY, t(106)), Op::Observe { values: vec![1] });
            // preview's actor is an argument, not the caller.
            let req = Request { recipe: 0, units: 1, version: s.pool.version, expires_at: 150 };
            let d = view(&s.storage, 106, |c| c.preview(acct(A1), req.clone()));
            assert!(d.allowed);
        }
    });
}

// PROP: SH-1
#[test]
fn sh1_now_is_the_block_timestamp_in_whole_seconds() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, open_config(), 100);
            // 149.999999999 s is second 149: a request expiring at 150 is live.
            let r = s.ok(&Ctx::new(A1, A1, 149_999_999_999), submit(0, 1, 0, 150));
            assert_eq!(r.value()["id"], json!(0), "{path:?}");
            // At exactly 150 s it has expired (expires_at <= now), for submit
            // and for dispatch (now >= expires_at).
            let r = s.ok(&Ctx::new(A1, A1, 150_000_000_000), submit(0, 1, 1, 150));
            assert_eq!(r.value()["decision"]["reason"], json!("Expired"));
            s.err(&Ctx::new(A1, A1, 150_000_000_000), Op::Dispatch { id: 0 }, guest(E::Expired));
            // The 24 h horizon is measured from the same second.
            let r = s.ok(&Ctx::new(A1, A1, 160_999_999_999), submit(0, 1, 1, 160 + 86_400));
            assert_eq!(r.value()["decision"]["reason"], json!("Allowed"));
            let r = s.ok(&Ctx::new(A1, A1, 161_000_000_000), submit(0, 1, 2, 161 + 86_401));
            assert_eq!(r.value()["decision"]["reason"], json!("Expired"));
            s.ok(&Ctx::by(OWNER, 162), Op::Cancel { id: 0 });
            s.ok(&Ctx::by(OWNER, 162), Op::Cancel { id: 1 });
            s.ok(&Ctx::new(OWNER, OWNER, 300_999_999_999), Op::Observe { values: vec![3] });
            assert_eq!(pool_of(&s.storage).observed_at, 300);
        }
    });
}

// ---------------------------------------------------------------------------
// SH-2: `new` is private and runs once (wasm wrappers)
// ---------------------------------------------------------------------------

// PROP: SH-2
#[test]
fn sh2_new_is_private_and_initialises_once() {
    big_stack(|| {
        let cfg = open_config();
        let input = serde_json::to_vec(&json!({ "config": cfg })).unwrap();
        let empty = Storage::new();
        // Host path: new() stores exactly Borsh(Pool::new(config, now)).
        assert_eq!(deploy(cfg.clone(), 100), storage_of(&Pool::new(cfg.clone(), 100).unwrap()));
        for b in Build::all() {
            let w = wasm(b, "pool_contract");
            for who in [OWNER, A1, X1, Z] {
                // Any other predecessor, even when the pool's key signed.
                let ctx = Ctx::new(who, POOL, 100_000_000_000);
                let out = wasm_call(w, &ctx, empty.clone(), vec![], "new", &input);
                assert_wasm_fail(b, &out, &Fail::Guest("Method new is private".into()), &empty, "new by other");
                assert!(out.called("predecessor_account_id") && !out.called("input"), "{b:?}: {:?}", out.host_calls);
                assert!(!out.called("storage_write"));
            }
            let out = wasm_call(w, &Ctx::by(POOL, 100), empty.clone(), vec![], "new", &input);
            assert!(out.result.is_ok(), "{b:?}: {:?}", out.result);
            assert_eq!(out.storage, storage_of(&Pool::new(cfg.clone(), 100).unwrap()));
            assert!(out.logs.is_empty() && out.receipts.is_empty());
            // Init once: a second `new` (even a different config) fails.
            let other = serde_json::to_vec(&json!({ "config": wedge_config() })).unwrap();
            let again = wasm_call(w, &Ctx::by(POOL, 200), out.storage.clone(), vec![], "new", &other);
            assert_wasm_fail(
                b,
                &again,
                &Fail::Guest("The contract has already been initialized".into()),
                &out.storage,
                "second new",
            );
            assert!(again.called("storage_has_key") && !again.called("storage_write"));
            // Before init every method fails (PanicOnDefault).
            let get = wasm_call(w, &Ctx::by(Z, 100), empty.clone(), vec![], "get_pool", b"{}");
            assert_wasm_fail(b, &get, &Fail::Guest("The contract is not initialized".into()), &empty, "uninit");
            // An invalid config fails with the core's error...
            let mut bad = cfg.clone();
            bad.metrics.clear();
            let out = wasm_call(
                w,
                &Ctx::by(POOL, 100),
                empty.clone(),
                vec![],
                "new",
                &serde_json::to_vec(&json!({ "config": bad })).unwrap(),
            );
            assert_wasm_fail(b, &out, &guest(E::InvalidConfig), &empty, "invalid config");
            // ...and an invalid account name with the shell's own message.
            for (field, msg) in [("owner", "Invalid owner account"), ("actor", "Invalid actor account"), ("executor", "Invalid executor account")] {
                let mut bad = cfg.clone();
                match field {
                    "owner" => bad.owner = "Not An Account".into(),
                    "actor" => bad.recipes[1].actor = "UPPER.near".into(),
                    _ => bad.recipes[0].executor = "a..b".into(),
                }
                assert!(bad.validate().is_ok(), "the core accepts {field}");
                let out = wasm_call(
                    w,
                    &Ctx::by(POOL, 100),
                    empty.clone(),
                    vec![],
                    "new",
                    &serde_json::to_vec(&json!({ "config": bad })).unwrap(),
                );
                let f = out.fail();
                assert_eq!(out.storage, empty);
                match b {
                    Build::Plain => assert_eq!(f.panic_msg, None),
                    Build::Near => assert!(
                        f.panic_msg.as_deref().unwrap_or("").contains(msg),
                        "{field}: {:?}",
                        f.panic_msg
                    ),
                }
            }
        }
    });
}

// ---------------------------------------------------------------------------
// SH-3: on_result is private, and maps the executor's status string
// ---------------------------------------------------------------------------

// PROP: SH-3
#[test]
fn sh3_on_result_is_private() {
    big_stack(|| {
        for b in Build::all() {
            let s = dispatched(Path::Wasm(b));
            let w = wasm(b, "pool_contract");
            for (pred, signer) in [(Z, Z), (X2, X2), (A2, A2), (OWNER, OWNER), (Z, POOL)] {
                for result in ["completed", "cancelled", "active"] {
                    let out = wasm_call(
                        w,
                        &Ctx::new(pred, signer, 102_000_000_000),
                        s.storage.clone(),
                        vec![PromiseResult::Successful(serde_json::to_vec(result).unwrap())],
                        "on_result",
                        br#"{"id":0}"#,
                    );
                    assert_wasm_fail(
                        b,
                        &out,
                        &Fail::Guest("Method on_result is private".into()),
                        &s.storage,
                        &format!("on_result by {pred}"),
                    );
                    assert!(!out.called("input") && !out.called("promise_result"));
                }
            }
            // The pool itself (its own callback) may.
            let out = wasm_call(
                w,
                &Ctx::by(POOL, 102),
                s.storage.clone(),
                vec![PromiseResult::Successful(br#""active""#.to_vec())],
                "on_result",
                br#"{"id":0}"#,
            );
            assert!(out.result.is_ok());
            assert_eq!(pool_of(&out.storage).records[0].status, Status::Active);
        }
    });
}

// PROP: SH-3
#[test]
fn sh3_on_result_maps_the_status_string() {
    big_stack(|| {
        // (promise result, status after, outcome in the event)
        let table: &[(Option<&str>, Status)] = &[
            (Some("completed"), Status::Completed),
            (Some("cancelled"), Status::Cancelled),
            (Some("active"), Status::Active),
            (Some("unknown"), Status::Unknown),
            (Some("garbage"), Status::Unknown),
            (Some(""), Status::Unknown),
            (Some("Completed"), Status::Unknown),
            (Some(" completed"), Status::Unknown),
            (None, Status::Unknown), // PromiseError (execute panicked)
        ];
        for path in paths() {
            for (result, after) in table {
                let mut s = dispatched(path);
                let v0 = s.pool.version;
                let r = s.ok(
                    &Ctx::by(POOL, 102),
                    Op::OnResult { id: 0, result: result.map(String::from) },
                );
                assert_eq!(s.status(0), *after, "{path:?} {result:?}");
                assert_eq!(
                    *r.event(),
                    json!({ "id": 0, "outcome": result.unwrap_or("unknown"), "error": null })
                );
                let p = pool_of(&s.storage);
                assert_eq!(p.version, v0 + 1);
                match after {
                    Status::Completed => assert_eq!(p.values, vec![-3]),
                    _ => assert_eq!(p.values, vec![0]),
                }
                assert!(r.calls.is_empty());
            }
            // Later results: idempotent and conflicting outcomes.
            let mut s = dispatched(path);
            s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: Some("active".into()) });
            let v = s.pool.version;
            // Active ignores a later unknown/active (no version bump: reconcile is
            // permissionless).
            for later in [Some("unknown"), Some("active"), None, Some("garbage")] {
                let r = s.ok(&Ctx::by(POOL, 103), Op::OnResult { id: 0, result: later.map(String::from) });
                assert_eq!(r.event()["error"], Value::Null);
                assert_eq!(s.status(0), Status::Active);
                assert_eq!(pool_of(&s.storage).version, v);
            }
            s.ok(&Ctx::by(POOL, 104), Op::OnResult { id: 0, result: Some("completed".into()) });
            assert_eq!(s.status(0), Status::Completed);
            let v = s.pool.version;
            s.ok(&Ctx::by(POOL, 104), Op::OnResult { id: 0, result: Some("completed".into()) });
            // The opposite terminal outcome is refused inside the callback: the
            // error goes to the event only, the call itself succeeds.
            let r = s.ok(&Ctx::by(POOL, 105), Op::OnResult { id: 0, result: Some("cancelled".into()) });
            assert_eq!(r.event()["error"], json!("InvalidState"));
            assert_eq!((s.status(0), pool_of(&s.storage).version), (Status::Completed, v));
            // Unknown -> Active -> settled through the callback.
            let mut s = dispatched(path);
            s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: None });
            assert_eq!(s.status(0), Status::Unknown);
            s.ok(&Ctx::by(POOL, 103), Op::OnResult { id: 0, result: None });
            s.ok(&Ctx::by(POOL, 103), Op::OnResult { id: 0, result: Some("active".into()) });
            assert_eq!(s.status(0), Status::Active);
            s.ok(&Ctx::by(POOL, 104), Op::OnResult { id: 0, result: Some("cancelled".into()) });
            assert_eq!(s.status(0), Status::Cancelled);
            // A callback for a record that does not exist panics.
            s.err(&Ctx::by(POOL, 104), Op::OnResult { id: 7, result: Some("active".into()) }, Fail::Rust("NotFound".into()));
        }
    });
}

/// A promise result that is not a JSON string fails the callback (the
/// wrapper cannot deserialize it): the record stays as it was.
// PROP: SH-3
#[test]
fn sh3_non_string_promise_results_fail_the_callback() {
    big_stack(|| {
        for b in Build::all() {
            let s = dispatched(Path::Wasm(b));
            let w = wasm(b, "pool_contract");
            for raw in [&b"completed"[..], b"", b"null", b"42", br#"["completed"]"#, br#"{"status":"completed"}"#] {
                let out = wasm_call(
                    w,
                    &Ctx::by(POOL, 102),
                    s.storage.clone(),
                    vec![PromiseResult::Successful(raw.to_vec())],
                    "on_result",
                    br#"{"id":0}"#,
                );
                let f = out.fail();
                assert_eq!(out.storage, s.storage, "{:?}", String::from_utf8_lossy(raw));
                assert!(out.logs.is_empty());
                assert!(out.called("promise_result"));
                match b {
                    Build::Plain => assert_eq!(f.panic_msg, None),
                    Build::Near => assert!(
                        f.panic_msg.as_deref().unwrap_or("").starts_with("Failed to deserialize callback using JSON"),
                        "{:?}",
                        f.panic_msg
                    ),
                }
            }
            // The record is still Dispatched and reconcile can retry.
            assert_eq!(s.status(0), Status::Dispatched);
        }
    });
}

// ---------------------------------------------------------------------------
// SH-4: submit returns the core's decision and id; a rejection writes nothing
// ---------------------------------------------------------------------------

fn cfg_with(metrics: Vec<Metric>, terms: Vec<Term>, recipes: Vec<Recipe>, max_age: u32) -> Config {
    Config {
        name: "case".into(),
        owner: OWNER.into(),
        metrics,
        terms,
        recipes,
        max_age_seconds: max_age,
    }
}
fn m(min: i64, max: i64, initial: i64) -> Metric {
    Metric { name: "m".into(), unit: "u".into(), initial, min, max }
}
fn t(metric: u32, target: i64, shape: Shape) -> Term {
    Term { metric, target, weight: 1, shape }
}

/// One rejection case: a configuration, an edit of the state, a request (by
/// `who` at `now`) and the reason the core gives.
struct Case {
    name: &'static str,
    cfg: Config,
    edit: fn(&mut Pool),
    who: &'static str,
    now: u64,
    req: fn(&Pool) -> Request,
    reason: &'static str,
}

fn rq(recipe: u32, units: u32, version: u32, expires_at: u64) -> Request {
    Request { recipe, units, version, expires_at }
}

fn rejection_cases() -> Vec<Case> {
    let full = |p: &mut Pool| {
        p.records = (0..256)
            .map(|id| Commitment { id, recipe: 0, units: 1, expires_at: 150, status: Status::Completed })
            .collect();
    };
    let mut prereq = open_config();
    prereq.recipes[1].requires = vec![(0, 2)];
    vec![
        Case { name: "paused", cfg: open_config(), edit: |p| p.paused = true, who: A1, now: 101, req: |p| rq(0, 1, p.version, 150), reason: "Paused" },
        Case { name: "stale", cfg: open_config(), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 1, p.version + 1, 150), reason: "Stale" },
        Case { name: "expired-now", cfg: open_config(), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 1, p.version, 101), reason: "Expired" },
        Case { name: "expired-horizon", cfg: open_config(), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 1, p.version, 101 + 86_401), reason: "Expired" },
        Case { name: "snapshot", cfg: cfg_with(vec![m(-10, 10, 0)], vec![t(0, 0, Shape::Excess)], vec![recipe(A1, X1, vec![0], vec![0], 5)], 10), edit: |_| {}, who: A1, now: 111, req: |p| rq(0, 1, p.version, 150), reason: "SnapshotExpired" },
        Case { name: "full", cfg: open_config(), edit: full, who: A1, now: 101, req: |p| rq(0, 1, p.version, 150), reason: "Full" },
        Case { name: "recipe", cfg: open_config(), edit: |_| {}, who: A1, now: 101, req: |p| rq(2, 1, p.version, 150), reason: "InvalidRecipe" },
        Case { name: "unauthorized", cfg: open_config(), edit: |_| {}, who: A2, now: 101, req: |p| rq(0, 1, p.version, 150), reason: "Unauthorized" },
        Case { name: "units-0", cfg: open_config(), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 0, p.version, 150), reason: "InvalidUnits" },
        Case { name: "units-max", cfg: open_config(), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 101, p.version, 150), reason: "InvalidUnits" },
        Case { name: "prerequisite", cfg: prereq, edit: |_| {}, who: A2, now: 101, req: |p| rq(1, 1, p.version, 150), reason: "Prerequisite" },
        Case { name: "arithmetic", cfg: cfg_with(vec![m(-1_000_000, 1_000_000, 999_999)], vec![t(0, 1_000_000, Shape::Excess)], vec![recipe(A1, X1, vec![1], vec![0], 5)], 0), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 2, p.version, 150), reason: "Arithmetic" },
        Case { name: "bounds", cfg: cfg_with(vec![m(0, 10, 5)], vec![t(0, 0, Shape::Deficit)], vec![recipe(A1, X1, vec![6], vec![0], 5)], 0), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 1, p.version, 150), reason: "Bounds" },
        Case { name: "energy", cfg: cfg_with(vec![m(0, 10, 5)], vec![t(0, 5, Shape::Target)], vec![recipe(A1, X1, vec![1], vec![0], 5)], 0), edit: |_| {}, who: A1, now: 101, req: |p| rq(0, 1, p.version, 150), reason: "Energy" },
        // Disturbed state ([12,5] outside [0,10]): the hedge's completion
        // must lower the energy, and [12,10] does not.
        Case { name: "energy-hedge", cfg: cfg_with(vec![m(0, 10, 5), m(-100, 100, 5)], vec![t(1, 0, Shape::Target)], vec![recipe(A1, X1, vec![-2, 0], vec![2, 5], 1)], 0), edit: |p| p.values = vec![12, 5], who: A1, now: 101, req: |p| rq(0, 1, p.version, 150), reason: "Energy" },
    ]
}

// PROP: SH-4
#[test]
fn sh4_rejected_submit_returns_the_decision_and_writes_nothing() {
    big_stack(|| {
        for path in paths() {
            for c in rejection_cases() {
                let mut s = Sim::new(path, c.cfg.clone(), 100);
                s.edit(c.edit);
                let req = (c.req)(&s.pool);
                let decision = s.pool.preview(c.who, &req, c.now);
                assert_eq!(decision.reason, c.reason, "case {} is not the intended rejection", c.name);
                let before = s.storage.clone();
                let r = s.ok(&Ctx::by(c.who, c.now), Op::Submit { req: req.clone() });
                // The exact core decision, no id, an event, and the same bytes.
                assert_eq!(r.value(), &json!({ "decision": decision_json(&decision), "id": null }), "{}", c.name);
                assert_eq!(r.event()["allowed"], json!(false));
                assert_eq!(r.event()["reason"], json!(c.reason));
                assert_eq!(r.event()["version"], json!(s.pool.version));
                assert_eq!(s.storage, before, "{path:?} {}: rejected submit changed state", c.name);
                if let Path::Wasm(_) = path {
                    // The &mut self wrapper still rewrites STATE (same bytes).
                    assert!(r.host_calls.contains(&"storage_write"));
                }
            }
            // An admitted submit returns the core's id and decision.
            let mut s = Sim::new(path, open_config(), 100);
            for i in 0..3u32 {
                let req = rq(i % 2, 1 + i, s.pool.version, 150);
                let who = if i % 2 == 0 { A1 } else { A2 };
                let d = s.pool.preview(who, &req, 101);
                let r = s.ok(&Ctx::by(who, 101), Op::Submit { req });
                assert_eq!(r.value(), &json!({ "decision": decision_json(&d), "id": i }));
            }
        }
    });
}

// ---------------------------------------------------------------------------
// SH-5: a core Err is a panic with the error string, and changes nothing
// ---------------------------------------------------------------------------

/// Two metrics; recipe 0 lowers metric 0 by 4 on reservation; recipe 1 would
/// raise it by 8 on completion. Releasing 0 while 1 is open is out of bounds.
fn dependent_config() -> Config {
    cfg_with(
        vec![m(0, 10, 5), m(-100, 100, 0)],
        vec![t(1, 0, Shape::Target)],
        vec![
            recipe(A1, X1, vec![-4, 0], vec![0, 0], 1),
            recipe(A2, X2, vec![0, 0], vec![8, 0], 1),
        ],
        10,
    )
}

// PROP: SH-5
#[test]
fn sh5_core_errors_are_panics_with_the_error_string() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, dependent_config(), 100);
            s.ok(&Ctx::by(A1, 101), submit(0, 1, 0, 105));
            s.ok(&Ctx::by(A2, 101), submit(1, 1, 1, 150));
            // dispatch
            s.err(&Ctx::by(A1, 101), Op::Dispatch { id: 9 }, guest(E::NotFound));
            s.err(&Ctx::by(A2, 101), Op::Dispatch { id: 0 }, guest(E::Unauthorized));
            s.ok(&Ctx::by(OWNER, 101), Op::Pause { paused: true });
            s.err(&Ctx::by(A1, 101), Op::Dispatch { id: 0 }, guest(E::Paused));
            s.ok(&Ctx::by(OWNER, 101), Op::Pause { paused: false });
            s.err(&Ctx::by(A1, 105), Op::Dispatch { id: 0 }, guest(E::Expired));
            s.err(&Ctx::by(A2, 111), Op::Dispatch { id: 1 }, guest(E::SnapshotExpired));
            // cancel: releasing 0 would expose 1's completion (+8 on 1 -> 13 > 10)
            s.err(&Ctx::by(A1, 102), Op::Cancel { id: 9 }, guest(E::NotFound));
            s.err(&Ctx::by(A2, 102), Op::Cancel { id: 0 }, guest(E::Unauthorized));
            s.err(&Ctx::by(A1, 102), Op::Cancel { id: 0 }, guest(E::Bounds));
            s.err(&Ctx::by(OWNER, 102), Op::Cancel { id: 0 }, guest(E::Bounds));
            s.ok(&Ctx::by(A2, 102), Op::Dispatch { id: 1 });
            s.err(&Ctx::by(A2, 102), Op::Dispatch { id: 1 }, guest(E::InvalidState));
            s.err(&Ctx::by(A2, 102), Op::Cancel { id: 1 }, guest(E::Pending));
            // settle
            s.err(&Ctx::by(X2, 102), Op::Settle { id: 9, completed: true }, guest(E::NotFound));
            s.err(&Ctx::by(A2, 102), Op::Settle { id: 1, completed: true }, guest(E::Unauthorized));
            s.err(&Ctx::by(X1, 102), Op::Settle { id: 1, completed: true }, guest(E::Unauthorized));
            s.err(&Ctx::by(X1, 102), Op::Settle { id: 0, completed: true }, guest(E::InvalidState));
            // pause / observe
            s.err(&Ctx::by(A1, 102), Op::Pause { paused: true }, guest(E::Unauthorized));
            s.err(&Ctx::by(Z, 102), Op::Observe { values: vec![5, 0] }, guest(E::Unauthorized));
            s.err(&Ctx::by(OWNER, 102), Op::Observe { values: vec![5, 0] }, guest(E::Pending));
            // Releasing 0 after 1 completed (+8 -> 9) would also leave [0, 10]
            // (13): 1 is settled as not executed instead.
            s.ok(&Ctx::by(X2, 102), Op::Settle { id: 1, completed: false });
            s.ok(&Ctx::by(OWNER, 102), Op::Cancel { id: 0 });
            s.err(&Ctx::by(OWNER, 103), Op::Observe { values: vec![5] }, guest(E::Bounds));
            s.err(&Ctx::by(OWNER, 103), Op::Observe { values: vec![5, 1_000_001] }, guest(E::Bounds));
            s.ok(&Ctx::by(OWNER, 103), Op::Observe { values: vec![5, 0] });
            // Every mutating method fails with Arithmetic at version u32::MAX.
            let mut s = Sim::new(path, open_config(), 100);
            s.ok(&Ctx::by(A1, 101), submit(0, 1, 0, 150));
            s.ok(&Ctx::by(A1, 101), submit(0, 1, 1, 150));
            s.ok(&Ctx::by(A1, 101), Op::Dispatch { id: 1 });
            s.edit(|p| p.version = u32::MAX);
            s.err(&Ctx::by(A1, 101), submit(0, 1, u32::MAX, 150), guest(E::Arithmetic));
            s.err(&Ctx::by(A1, 101), Op::Dispatch { id: 0 }, guest(E::Arithmetic));
            s.err(&Ctx::by(A1, 101), Op::Cancel { id: 0 }, guest(E::Arithmetic));
            s.err(&Ctx::by(X1, 101), Op::Settle { id: 1, completed: true }, guest(E::Arithmetic));
            s.err(&Ctx::by(X1, 101), Op::Settle { id: 1, completed: false }, guest(E::Arithmetic));
            s.err(&Ctx::by(OWNER, 101), Op::Pause { paused: true }, guest(E::Arithmetic));
            let mut q = Sim::new(path, open_config(), 100);
            q.edit(|p| p.version = u32::MAX);
            q.err(&Ctx::by(OWNER, 101), Op::Observe { values: vec![1] }, guest(E::Arithmetic));
            // on_result never panics on a core error: the error is in the event.
            let r = s.ok(&Ctx::by(POOL, 101), Op::OnResult { id: 1, result: Some("active".into()) });
            assert_eq!(r.event()["error"], json!("Arithmetic"));
            assert_eq!(s.status(1), Status::Dispatched);
        }
    });
}

// ---------------------------------------------------------------------------
// SH-6: dispatch sends execute{id,recipe,units} to the recipe's executor,
// then on_result{id} to itself
// ---------------------------------------------------------------------------

// PROP: SH-6
#[test]
fn sh6_dispatch_promise_shape() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, open_config(), 100);
            s.ok(&Ctx::by(A1, 100), submit(0, 7, 0, 150));
            s.ok(&Ctx::by(A2, 100), submit(1, 3, 1, 150));
            for (id, who, exec, recipe, units) in [(1u32, A2, X2, 1u32, 3u32), (0, A1, X1, 0, 7)] {
                let before = pool_of(&s.storage);
                let r = s.ok(&Ctx::by(who, 101), Op::Dispatch { id });
                assert_eq!(
                    r.calls,
                    vec![
                        fcall(exec, "execute", json!({ "id": id, "recipe": recipe, "units": units }), 30, vec![]),
                        fcall(POOL, "on_result", json!({ "id": id }), 30, vec![0]),
                    ],
                    "{path:?}"
                );
                assert!(r.events.is_empty(), "dispatch logs nothing");
                if let Path::Wasm(_) = path {
                    // dispatch returns the callback promise (index 1).
                    assert_eq!(r.promise_return, Some(1));
                }
                let after = pool_of(&s.storage);
                assert_eq!(after.version, before.version + 1);
                assert_eq!(after.values, before.values);
                assert_eq!(after.records[id as usize].status, Status::Dispatched);
            }
        }
    });
}

// ---------------------------------------------------------------------------
// SH-7: reconcile: anyone, only for in-flight records, status then on_result
// ---------------------------------------------------------------------------

// PROP: SH-7
#[test]
fn sh7_reconcile_guard_and_promise_shape() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, open_config(), 100);
            s.err(&Ctx::by(Z, 100), Op::Reconcile { id: 0 }, Fail::Rust("NotFound".into()));
            s.ok(&Ctx::by(A2, 100), submit(1, 2, 0, 150));
            // Reserved: not in flight.
            s.err(&Ctx::by(Z, 100), Op::Reconcile { id: 0 }, Fail::Rust("InvalidState".into()));
            s.ok(&Ctx::by(A2, 101), Op::Dispatch { id: 0 });
            let check = |s: &mut Sim, who: &str| {
                let before = s.storage.clone();
                let r = s.ok(&Ctx::new(who, Z, 102_000_000_000), Op::Reconcile { id: 0 });
                assert_eq!(
                    r.calls,
                    vec![
                        fcall(X2, "status", json!({ "id": 0 }), 10, vec![]),
                        fcall(POOL, "on_result", json!({ "id": 0 }), 30, vec![0]),
                    ]
                );
                assert!(r.events.is_empty());
                assert_eq!(s.storage, before, "reconcile changed state");
                if let Path::Wasm(_) = path {
                    assert!(!r.host_calls.contains(&"storage_write"), "reconcile (&self) wrote");
                    assert_eq!(r.promise_return, Some(1));
                }
            };
            for who in [Z, A1, X2, OWNER, RELAY] {
                check(&mut s, who); // Dispatched
            }
            s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: None });
            check(&mut s, Z); // Unknown
            s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: Some("active".into()) });
            check(&mut s, Z); // Active
            s.ok(&Ctx::by(X2, 103), Op::Settle { id: 0, completed: false });
            s.err(&Ctx::by(Z, 103), Op::Reconcile { id: 0 }, Fail::Rust("InvalidState".into()));
            s.ok(&Ctx::by(A2, 103), submit(1, 2, s.pool.version, 150));
            s.ok(&Ctx::by(A2, 103), Op::Dispatch { id: 1 });
            s.ok(&Ctx::by(X2, 103), Op::Settle { id: 1, completed: true });
            s.err(&Ctx::by(Z, 103), Op::Reconcile { id: 1 }, Fail::Rust("InvalidState".into()));
        }
    });
}

// ---------------------------------------------------------------------------
// SH-9: views
// ---------------------------------------------------------------------------

// PROP: SH-9 RD-PREVIEW
#[test]
fn sh9_views_and_paging_at_256_records() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, open_config(), 100);
            for i in 0..256u32 {
                // Recipe 1 completes at -1 per unit: one unit keeps the
                // envelope inside [-1000, 1000].
                let (who, recipe, units) = if i % 3 == 0 { (A2, 1, 1) } else { (A1, 0, 1 + i % 100) };
                let r = s.ok(&Ctx::by(who, 101), submit(recipe, units, s.pool.version, 150));
                assert_eq!(r.value()["id"], json!(i));
                if i % 5 == 0 {
                    s.ok(&Ctx::by(who, 101), Op::Dispatch { id: i });
                }
            }
            let r = s.ok(&Ctx::by(A1, 101), submit(0, 1, s.pool.version, 150));
            assert_eq!(r.value()["decision"]["reason"], json!("Full"));
            let froms = [0u32, 1, 49, 50, 51, 200, 206, 207, 255, 256, 257, u32::MAX];
            let limits = [0u32, 1, 49, 50, 51, 100, u32::MAX];
            match path {
                Path::Host => {
                    let mut rng = Rng::new(9);
                    check_views(&s.storage, &s.pool, &mut rng, 101, "256 records");
                    for from in froms {
                        for limit in limits {
                            let got = view(&s.storage, 101, |c| c.get_commitments(from, limit));
                            assert_eq!(got, expected_page(&s.pool, from, limit), "({from}, {limit})");
                            assert!(got.len() <= 50);
                        }
                    }
                }
                Path::Wasm(b) => {
                    let w = wasm(b, "pool_contract");
                    let v = |method: &str, args: Value| {
                        let out = wasm_call(w, &Ctx::by(Z, 101), s.storage.clone(), vec![], method, &serde_json::to_vec(&args).unwrap());
                        assert!(out.logs.is_empty() && out.receipts.is_empty());
                        assert!(!out.called("storage_write"), "view {method} wrote");
                        assert_eq!(out.storage, s.storage);
                        out.json()
                    };
                    assert_eq!(v("get_pool", json!({})), serde_json::to_value(&s.pool).unwrap());
                    for from in froms {
                        for limit in limits {
                            let want: Vec<Value> = expected_page(&s.pool, from, limit).iter().map(commitment_json).collect();
                            assert_eq!(v("get_commitments", json!({ "from": from, "limit": limit })), json!(want), "({from}, {limit})");
                        }
                    }
                    for (actor, req) in [(A1, rq(0, 1, s.pool.version, 150)), (A2, rq(1, 100, 3, 150)), (Z, rq(5, 1, 0, 0))] {
                        let d = s.pool.preview(actor, &req, 101);
                        assert_eq!(v("preview", json!({ "actor": actor, "request": request_json(&req) })), decision_json(&d));
                    }
                }
            }
        }
    });
}

// ---------------------------------------------------------------------------
// SH-10: nonpayable methods reject an attached deposit (wasm wrappers)
// ---------------------------------------------------------------------------

// PROP: SH-10
#[test]
fn sh10_mutating_methods_reject_attached_deposits() {
    big_stack(|| {
        for b in Build::all() {
            // Record 0 dispatched, record 1 reserved: every call below would
            // succeed without the deposit.
            let mut s = dispatched(Path::Wasm(b));
            s.ok(&Ctx::by(A2, 101), submit(1, 1, s.pool.version, 150));
            let fresh = Sim::new(Path::Wasm(b), open_config(), 100).storage;
            let w = wasm(b, "pool_contract");
            let cases: Vec<(&str, &str, Value, Vec<PromiseResult>, Storage)> = vec![
                ("new", POOL, json!({ "config": open_config() }), vec![], Storage::new()),
                ("submit", A1, json!({ "request": request_json(&rq(0, 1, s.pool.version, 150)) }), vec![], s.storage.clone()),
                ("dispatch", A2, json!({ "id": 1 }), vec![], s.storage.clone()),
                ("settle", X2, json!({ "id": 0, "completed": true }), vec![], s.storage.clone()),
                ("cancel", OWNER, json!({ "id": 1 }), vec![], s.storage.clone()),
                ("set_paused", OWNER, json!({ "paused": true }), vec![], s.storage.clone()),
                ("observe", OWNER, json!({ "values": [0] }), vec![], fresh),
                ("on_result", POOL, json!({ "id": 0 }), vec![PromiseResult::Successful(br#""active""#.to_vec())], s.storage.clone()),
            ];
            for (method, who, args, results, storage) in cases {
                for yocto in [1u128, 10u128.pow(24)] {
                    let out = wasm_call(
                        w,
                        &Ctx::by(who, 102).with_deposit(yocto),
                        storage.clone(),
                        results.iter().map(|r| match r {
                            PromiseResult::Successful(v) => PromiseResult::Successful(v.clone()),
                            PromiseResult::Failed => PromiseResult::Failed,
                        }).collect(),
                        method,
                        &serde_json::to_vec(&args).unwrap(),
                    );
                    assert_wasm_fail(
                        b,
                        &out,
                        &Fail::Guest(format!("Method {method} doesn't accept deposit")),
                        &storage,
                        method,
                    );
                    assert!(out.called("attached_deposit") && !out.called("input"), "{method}: {:?}", out.host_calls);
                }
                // Without a deposit the same call goes through.
                let out = wasm_call(w, &Ctx::by(who, 102), storage.clone(), results, method, &serde_json::to_vec(&args).unwrap());
                assert!(out.result.is_ok(), "{method} without deposit: {:?}", out.result);
            }
        }
    });
}

/// NT-F2 (low): `reconcile` is a `&self` method, so near-sdk generates no
/// deposit check for it (nor for the views). docs/api.md says "All mutating
/// methods are nonpayable"; reconcile is the one call-only method that
/// creates receipts, and it keeps any attached NEAR (the outgoing calls
/// carry 0). This test asserts the observed behaviour (a reproducer).
// PROP: SH-10
#[test]
fn nt_f2_reconcile_accepts_and_keeps_an_attached_deposit() {
    big_stack(|| {
        for b in Build::all() {
            let s = dispatched(Path::Wasm(b));
            let w = wasm(b, "pool_contract");
            let out = wasm_call(
                w,
                &Ctx::by(Z, 102).with_deposit(10u128.pow(24)),
                s.storage.clone(),
                vec![],
                "reconcile",
                br#"{"id":0}"#,
            );
            assert!(out.result.is_ok(), "{b:?}: {:?}", out.result);
            assert!(!out.called("attached_deposit"), "no deposit check at all");
            let calls = calls_of(&out.receipts);
            assert_eq!(calls.len(), 2);
            assert!(calls.iter().all(|c| c.deposit == 0), "the deposit is not forwarded");
            for (method, args) in [("get_pool", json!({})), ("get_commitments", json!({"from":0,"limit":1}))] {
                let out = wasm_call(w, &Ctx::by(Z, 102).with_deposit(1), s.storage.clone(), vec![], method, &serde_json::to_vec(&args).unwrap());
                assert!(out.result.is_ok(), "{method}");
            }
        }
    });
}

/// NT-F1: the wasm upstream builds (`scripts/build.sh`: plain `cargo build`,
/// no `--cfg near`) is near-sdk 5.29.1's "pure-Rust fallback, not for
/// on-chain use" configuration: `near-sdk-env`'s `panic_str` is then
/// `eprintln!` + `panic!()` instead of the `panic_utf8` host call, so every
/// contract failure (core errors, `#[private]`, deposit and init checks,
/// argument errors) is a bare `unreachable` trap with no message, and the
/// wasm does not even import `panic_utf8`. The `--cfg near` build reports the
/// error string. This test asserts the observed behaviour (a reproducer).
// PROP: SH-5
#[test]
fn nt_f1_upstream_build_drops_every_panic_message() {
    big_stack(|| {
        let plain = wasm(Build::Plain, "pool_contract");
        let near = wasm(Build::Near, "pool_contract");
        assert!(!plain.imports.iter().any(|i| i == "env.panic_utf8"), "plain imports panic_utf8");
        assert!(near.imports.iter().any(|i| i == "env.panic_utf8"));
        for b in Build::all() {
            let s = Sim::new(Path::Wasm(b), open_config(), 100);
            let out = wasm_step(b, &Ctx::by(Z, 101), s.storage.clone(), &Op::Observe { values: vec![1] });
            let f = out.fail();
            match b {
                Build::Plain => {
                    assert_eq!(f.panic_msg, None);
                    assert_eq!(f.trap, "wasm `unreachable` instruction executed");
                    assert!(!out.called("panic_utf8"));
                }
                Build::Near => {
                    assert_eq!(f.panic_msg.as_deref(), Some("Unauthorized"));
                }
            }
        }
        let exec_plain = wasm(Build::Plain, "pool_executor");
        assert!(!exec_plain.imports.iter().any(|i| i == "env.panic_utf8"));
    });
}
