//! F-1 (wedge) reproduced through the shell, on the host path, on both wasm
//! builds, and end to end with the executor (RT-WEDGE in the mocked
//! runtime).
//!
//! Brief: metrics m(0,10,5), m(-100,100,5); term t(1,0,1,target); recipe
//! r(a1,x1,[-2,0],[2,-5],1,[]); observe [12,5]; submit 1 unit -> Ok;
//! dispatch; settle(true) -> Bounds; settle(false) -> Bounds; observe ->
//! Pending. These tests assert the wedge exists (they are reproducers of a
//! finding, not of a desired property): if upstream fixes F-1 they fail.
//!
// PROP: F-1 SH-5

mod common;
use common::*;
use near_sdk::serde_json::{json, Value};
use pool_core::{Error as E, Status};

fn guest(e: E) -> Fail {
    Fail::Guest(e.to_string())
}

/// Observe [12,5], submit the hedge, dispatch it. Returns the Sim with the
/// record Dispatched.
fn wedge(path: Path) -> Sim {
    let mut s = Sim::new(path, wedge_config(), 100);
    s.ok(&Ctx::by(OWNER, 100), Op::Observe { values: vec![12, 5] });
    let r = s.ok(&Ctx::by(A1, 101), submit(0, 1, s.pool.version, 150));
    assert_eq!(r.value()["decision"]["reason"], json!("Allowed"), "the recovery rule admits the hedge");
    assert_eq!(r.value()["id"], json!(0));
    assert_eq!(s.pool.values, vec![10, 5], "the reservation brought metric 0 back inside");
    s.ok(&Ctx::by(A1, 101), Op::Dispatch { id: 0 });
    s
}

/// In every in-flight state, no call can make the record terminal, and the
/// owner can no longer observe.
fn assert_wedged(s: &mut Sim, at: Status) {
    assert_eq!(s.status(0), at);
    let v = s.pool.version;
    s.err(&Ctx::by(X1, 102), Op::Settle { id: 0, completed: true }, guest(E::Bounds));
    s.err(&Ctx::by(X1, 102), Op::Settle { id: 0, completed: false }, guest(E::Bounds));
    for outcome in ["completed", "cancelled"] {
        let r = s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: Some(outcome.into()) });
        assert_eq!(r.event(), &json!({ "id": 0, "outcome": outcome, "error": "Bounds" }));
    }
    s.err(&Ctx::by(A1, 102), Op::Cancel { id: 0 }, guest(E::Pending));
    s.err(&Ctx::by(OWNER, 102), Op::Cancel { id: 0 }, guest(E::Pending));
    for values in [vec![5, 5], vec![12, 5], vec![10, 0]] {
        s.err(&Ctx::by(OWNER, 103), Op::Observe { values }, guest(E::Pending));
    }
    assert_eq!(s.status(0), at);
    assert_eq!(s.pool.version, v, "nothing moved");
}

#[test]
fn f1_wedge_through_the_shell() {
    big_stack(|| {
        for path in paths() {
            let mut s = wedge(path);
            assert_wedged(&mut s, Status::Dispatched);
            s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: None });
            assert_wedged(&mut s, Status::Unknown);
            s.ok(&Ctx::by(POOL, 102), Op::OnResult { id: 0, result: Some("active".into()) });
            assert_wedged(&mut s, Status::Active);
            // Reconcile keeps asking (permissionless, no state change).
            let r = s.ok(&Ctx::by(Z, 104), Op::Reconcile { id: 0 });
            assert_eq!(r.calls.len(), 2);
        }
    });
}

/// Control: the same recipe from an undisturbed baseline settles normally
/// (LIVE-1 holds when the base violation is 0).
#[test]
fn f1_control_without_the_disturbing_observe() {
    big_stack(|| {
        for path in paths() {
            let mut s = Sim::new(path, wedge_config(), 100);
            s.ok(&Ctx::by(A1, 101), submit(0, 1, 0, 150));
            s.ok(&Ctx::by(A1, 101), Op::Dispatch { id: 0 });
            s.ok(&Ctx::by(X1, 102), Op::Settle { id: 0, completed: true });
            assert_eq!(s.status(0), Status::Completed);
            assert_eq!(s.pool.values, vec![5, 0]);
            s.ok(&Ctx::by(OWNER, 103), Op::Observe { values: vec![5, 5] });
        }
    });
}

/// RT-WEDGE in the mocked runtime: pool and executor wasm with the receipt
/// router. The operator's finish(true) succeeds at the executor, whose
/// settle receipt then fails Bounds at the pool: the executor's job is
/// "completed" while the pool's record stays Active forever, and the
/// operator cannot switch to the other outcome.
#[test]
fn f1_wedge_end_to_end_with_the_executor() {
    big_stack(|| {
        for b in Build::all() {
            let mut net = Net::new(b, &wedge_config(), X1, 100);
            assert!(net.tx(OWNER, POOL, "observe", json!({ "values": [12, 5] })).result.is_ok());
            let v = net.pool_state().version;
            let req = json!({ "request": { "recipe": 0, "units": 1, "version": v, "expires_at": 150 } });
            let out = net.tx(A1, POOL, "submit", req);
            assert_eq!(out.json()["id"], json!(0));
            net.tx(A1, POOL, "dispatch", json!({ "id": 0 }));
            assert_eq!(net.pool_state().records[0].status, Status::Active);
            let frozen = net.pool.clone();

            let n = net.trace.len();
            let fin = net.tx(OPERATOR, X1, "finish", json!({ "id": 0, "completed": true }));
            assert!(fin.result.is_ok(), "the executor accepts the completion");
            assert_eq!(net.trace.len(), n + 2);
            let (recv, method, settle, logs) = &net.trace[n + 1];
            assert_eq!((recv.as_str(), method.as_str()), (POOL, "settle"));
            let f = settle.as_ref().expect_err("settle must fail (F-1)");
            assert!(logs.is_empty());
            match b {
                Build::Plain => assert_eq!(f.panic_msg, None, "NT-F1: no message"),
                Build::Near => assert_eq!(f.panic_msg.as_deref(), Some("Bounds")),
            }
            assert_eq!(net.jobs(), json!([{ "id": 0, "recipe": 0, "units": 1, "status": "completed" }]));
            assert_eq!(net.pool, frozen, "the pool did not move");

            // The operator cannot report the other outcome instead.
            let other = net.tx(OPERATOR, X1, "finish", json!({ "id": 0, "completed": false }));
            let f = other.fail();
            if b == Build::Near {
                assert!(f.panic_msg.as_deref().unwrap_or("").contains("terminal outcome conflict"));
            }
            // Re-notifying fails the same way; reconcile reads "completed" and
            // the callback reports Bounds.
            net.tx(OPERATOR, X1, "finish", json!({ "id": 0, "completed": true }));
            assert!(net.trace.last().unwrap().2.is_err());
            let n = net.trace.len();
            assert!(net.tx(Z, POOL, "reconcile", json!({ "id": 0 })).result.is_ok());
            let (_, method, r, logs) = &net.trace[n + 2];
            assert_eq!(method, "on_result");
            assert!(r.is_ok());
            assert_eq!(
                parse_event(&logs[0])["data"][0],
                json!({ "id": 0, "outcome": "completed", "error": "Bounds" })
            );
            // The owner cannot observe or cancel; nothing has changed.
            for (method, args) in [("observe", json!({ "values": [5, 5] })), ("cancel", json!({ "id": 0 }))] {
                let out = net.tx(OWNER, POOL, method, args);
                let f = out.fail();
                if b == Build::Near {
                    assert_eq!(f.panic_msg.as_deref(), Some("Pending"), "{method}");
                }
            }
            assert_eq!(net.pool, frozen);
            assert_eq!(net.pool_state().records[0].status, Status::Active);
            let _: Value = net.jobs();
        }
    });
}
