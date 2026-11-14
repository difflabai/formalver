//! Runtime tests on the real wasm (pool_contract.wasm and pool_executor.wasm
//! built from the pin by scripts/build-wasm.sh) in a local near-sandbox:
//! RT-PRED, RT-PRIVATE, RT-CALLBACK, RT-REVERT, RT-RACE, RT-WEDGE, and the
//! SB-1 witness (the upstream build loses every panic message).
//!
//! Every test keeps a host-side `pool_core::Pool` (the real core) in step
//! with the chain and compares the whole `get_pool` state after each step,
//! so a divergence between the wasm and the core fails the test. Failure
//! messages are checked per build variant (`expect_panic` in common/).
// `ok()` asserts success itself; most callers drop the outcome.
#![allow(unused_must_use)]
mod common;

use common::*;
use pool_core::{Error, Pool, Status};
use serde_json::{json, Value};
use std::time::{Duration, Instant};

async fn same(env: &Env, reference: &Pool, what: &str) {
    assert_eq!(&env.pool().await, reference, "{what}: chain state differs from the core");
}

fn forward(env: &Env, method: &str, args: Value) -> Value {
    json!({ "receiver": env.lock.id(), "method": method, "args": args.to_string() })
}

// ------------------------------------------------------------------ RT-PRED

/// PROP: RT-PRED. A call forwarded by a third-party contract is attributed to
/// that contract (the predecessor), never to the account that signed it.
#[tokio::test]
async fn rt_pred_relay_is_the_caller() {
    let env = Env::bare().await;
    let relay = deploy(&env.worker, "relay", 10, &relay_wasm()).await;
    let cfg = basic_config(
        env.owner.id(),
        &[(env.actor.id(), env.exec.id()), (relay.id(), env.exec.id())],
    );
    let env = env.init(&cfg).await;
    let mut reference = env.pool().await;
    let mut rows = vec![];

    // 1. The actor signs a forward of its own, otherwise valid, submit.
    let req = env.request(0, 4).await;
    let raw = env.raw().await;
    let r = ok(&env.actor, relay.id(), "forward", forward(&env, "submit", json!({ "request": req }))).await;
    let v: Value = r.clone().json().unwrap();
    let expected = reference.preview(relay.id().as_str(), &req, env.now().await);
    assert_eq!(v["decision"], serde_json::to_value(&expected).unwrap());
    assert_eq!(v["decision"]["allowed"], false);
    assert_eq!(v["decision"]["reason"], "Unauthorized");
    assert_eq!(v["id"], Value::Null);
    let ev = event(&r, env.lock.id(), "decision");
    assert_eq!(ev["actor"], relay.id().as_str(), "the event names the relay as actor");
    assert_eq!(env.raw().await, raw, "a rejected submit writes nothing");
    rows.push(json!({"case": "actor signs relay.forward(submit recipe 0)", "attributed_to": ev["actor"], "allowed": false, "reason": v["decision"]["reason"], "storage_unchanged": true}));
    // Control: the same request, sent by the actor itself, is accepted.
    let (_, v) = env.submit(&env.actor, &req).await;
    assert_eq!(v["decision"]["allowed"], true);
    let id0 = reference.submit(env.actor.id().as_str(), req, env.now().await).unwrap();
    same(&env, &reference, "direct submit").await;
    rows.push(json!({"case": "actor submits the same request directly", "allowed": true, "id": id0}));

    // 2. Recipe 1's actor is the relay: a forward signed by an unrelated
    // account is the relay's submit and is accepted; the signer plays no part.
    let req = env.request(1, 2).await;
    let r = ok(&env.mallory, relay.id(), "forward", forward(&env, "submit", json!({ "request": req }))).await;
    let v: Value = r.clone().json().unwrap();
    assert_eq!(v["decision"]["allowed"], true, "{v}");
    assert_eq!(event(&r, env.lock.id(), "decision")["actor"], relay.id().as_str());
    let id1 = reference.submit(relay.id().as_str(), req, env.now().await).unwrap();
    assert_eq!(v["id"], id1);
    same(&env, &reference, "relay submit").await;
    rows.push(json!({"case": "mallory signs relay.forward(submit recipe 1); the relay is recipe 1's actor", "attributed_to": relay.id(), "allowed": true}));
    let req = env.request(1, 2).await;
    let (_, v) = env.submit(&env.mallory, &req).await;
    assert_eq!(v["decision"]["reason"], "Unauthorized");
    same(&env, &reference, "mallory direct").await;
    rows.push(json!({"case": "mallory submits recipe 1 directly", "allowed": false, "reason": "Unauthorized"}));

    // 3. Mutating calls forwarded by the relay are the relay's, whoever signs.
    let raw = env.raw().await;
    for (signer, method, args) in [
        (&env.actor, "dispatch", json!({ "id": id0 })),
        (&env.actor, "cancel", json!({ "id": id0 })),
        (env.exec.as_account(), "settle", json!({ "id": id1, "completed": true })),
        (&env.owner, "set_paused", json!({ "paused": true })),
        (&env.owner, "observe", json!({ "values": [50, 0] })),
    ] {
        let mut p = reference.clone();
        let core = match method {
            "dispatch" => p.dispatch(relay.id().as_str(), id0, env.now().await),
            "cancel" => p.cancel(relay.id().as_str(), id0, env.now().await),
            "settle" => p.settle(relay.id().as_str(), id1, true),
            "set_paused" => p.set_paused(relay.id().as_str(), true),
            _ => p.observe(relay.id().as_str(), vec![50, 0], env.now().await),
        };
        assert_eq!(core, Err(Error::Unauthorized));
        let observed = fails(signer, relay.id(), "forward", forward(&env, method, args), "Unauthorized").await;
        assert_eq!(env.raw().await, raw, "{method} via relay changed state");
        rows.push(json!({"case": format!("{} signs relay.forward({method})", signer.id()), "core": "Unauthorized", "observed_panic": observed, "storage_unchanged": true}));
    }
    // The relay may dispatch its own record, whoever asks it to.
    ok(&env.mallory, relay.id(), "forward", forward(&env, "dispatch", json!({ "id": id1 }))).await;
    reference.dispatch(relay.id().as_str(), id1, env.now().await).unwrap();
    reference.acknowledge(id1, true).unwrap();
    same(&env, &reference, "relay dispatch").await;
    rows.push(json!({"case": "mallory signs relay.forward(dispatch id1)", "result": "Ok, Active"}));
    record("RT-PRED", json!({ "property": "RT-PRED", "assumption": "ASM-PRED", "result": "pass", "cases": rows }));
}

// --------------------------------------------------------------- RT-PRIVATE

/// PROP: RT-PRIVATE. `new` (pool and executor) and `on_result` reject every
/// predecessor other than the contract's own account; `new` runs once.
#[tokio::test]
async fn rt_private_new_and_on_result() {
    let env = Env::bare().await;
    let relay = deploy(&env.worker, "relay", 10, &relay_wasm()).await;
    let cfg = basic_config(env.owner.id(), &[(env.actor.id(), env.exec.id())]);
    let new_args = json!({ "config": cfg });
    let mut rows = vec![];
    for a in [&env.owner, &env.actor, &env.mallory, env.exec.as_account()] {
        let o = fails(a, env.lock.id(), "new", new_args.clone(), "Method new is private").await;
        rows.push(json!({"call": "pool.new", "predecessor": a.id(), "expected": "Method new is private", "observed_panic": o}));
    }
    // Signed by the pool's own key but forwarded: the predecessor is the relay.
    let o = fails(
        env.lock.as_account(),
        relay.id(),
        "forward",
        json!({ "receiver": env.lock.id(), "method": "new", "args": new_args.to_string() }),
        "Method new is private",
    )
    .await;
    rows.push(json!({"call": "pool.new via relay, signed by the pool's key", "predecessor": relay.id(), "expected": "Method new is private", "observed_panic": o}));
    assert!(env.raw().await.is_empty(), "a rejected new left state");
    // A view's failure is a query error, not an execution outcome.
    let e = format!("{:?}", env.lock.view("get_pool").await.unwrap_err());
    if variant() == "cfg-near" {
        assert!(e.contains("The contract is not initialized"), "{e}");
    } else {
        assert!(e.to_lowercase().contains("unreachable"), "{e}");
    }
    let o = fails(
        &env.owner,
        env.exec.id(),
        "new",
        json!({ "lock": env.lock.id(), "operator": env.mallory.id() }),
        "Method new is private",
    )
    .await;
    assert!(raw_state(&env.worker, env.exec.id()).await.is_empty());
    rows.push(json!({"call": "exec.new", "predecessor": env.owner.id(), "expected": "Method new is private", "observed_panic": o}));

    let env = env.init(&cfg).await;
    let raw = env.raw().await;
    let raw_exec = raw_state(&env.worker, env.exec.id()).await;
    let mut cfg2 = cfg.clone();
    cfg2.owner = env.mallory.id().to_string();
    let o = fails(env.lock.as_account(), env.lock.id(), "new", json!({ "config": cfg2 }), "The contract has already been initialized").await;
    fails(
        env.exec.as_account(),
        env.exec.id(),
        "new",
        json!({ "lock": env.lock.id(), "operator": env.mallory.id() }),
        "The contract has already been initialized",
    )
    .await;
    assert_eq!(env.raw().await, raw);
    assert_eq!(raw_state(&env.worker, env.exec.id()).await, raw_exec);
    rows.push(json!({"call": "pool.new and exec.new again, by their own accounts", "expected": "The contract has already been initialized", "observed_panic": o, "storage_unchanged": true}));

    // An Unknown record: a forged callback would move it (to Active, or to
    // Cancelled with the reservation released) if it got through.
    let mut reference = env.pool().await;
    env.mode("unknown").await;
    let id = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id })).await;
    reference.dispatch(env.actor.id().as_str(), id, env.now().await).unwrap();
    reference.acknowledge(id, false).unwrap();
    same(&env, &reference, "dispatch (unknown)").await;
    let raw = env.raw().await;
    for a in [&env.owner, &env.actor, &env.mallory, env.exec.as_account()] {
        let o = fails(a, env.lock.id(), "on_result", json!({ "id": id }), "Method on_result is private").await;
        assert_eq!(env.raw().await, raw);
        rows.push(json!({"call": "pool.on_result", "predecessor": a.id(), "expected": "Method on_result is private", "observed_panic": o, "storage_unchanged": true}));
    }
    let o = fails(&env.actor, relay.id(), "forward", forward(&env, "on_result", json!({ "id": id })), "Method on_result is private").await;
    assert_eq!(env.raw().await, raw);
    rows.push(json!({"call": "pool.on_result via relay", "predecessor": relay.id(), "expected": "Method on_result is private", "observed_panic": o, "storage_unchanged": true}));
    // The pool's own key passes the private check, but a transaction carries
    // no promise result, so the callback still cannot run.
    let r = tx(env.lock.as_account(), env.lock.id(), "on_result", json!({ "id": id })).await;
    let text = failure_text(&r);
    assert!(!text.contains("is private"), "{text}");
    const NO_RESULT: &str = "Accessed invalid promise result index: 0";
    let self_call = if text.contains(NO_RESULT) { format!("host error: {NO_RESULT}") } else { panic_message(&text) };
    assert_eq!(env.raw().await, raw);
    same(&env, &reference, "after forged callbacks").await;
    rows.push(json!({"call": "pool.on_result signed by the pool's own key (no promise result)", "predecessor": env.lock.id(), "observed_failure": self_call, "storage_unchanged": true}));
    record("RT-PRIVATE", json!({ "property": "RT-PRIVATE", "assumption": "ASM-PRIVATE", "result": "pass", "cases": rows }));
}

// -------------------------------------------------------------- RT-CALLBACK

/// PROP: RT-CALLBACK. The dispatch callback's mapping on the real receipt
/// path, one row per executor mode, compared with the core after each step.
#[tokio::test]
async fn rt_callback_status_mapping() {
    let env = Env::bare().await;
    let cfg = basic_config(env.owner.id(), &[(env.actor.id(), env.exec.id())]);
    let env = env.init(&cfg).await;
    let a = env.actor.id().as_str();
    let x = env.exec.id().as_str().to_string();
    let mut reference = env.pool().await;
    let mut rows = vec![];

    // normal: execute returns "active" -> acknowledge(true) -> Active, the
    // reservation stays (ASYNC-1).
    let id_normal = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    let held = reference.values.clone();
    let r = ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id_normal })).await;
    reference.dispatch(a, id_normal, env.now().await).unwrap();
    reference.acknowledge(id_normal, true).unwrap();
    same(&env, &reference, "normal").await;
    let ev = event(&r, env.lock.id(), "reconciled");
    assert_eq!(ev, json!({ "id": id_normal, "outcome": "active", "error": null }));
    assert_eq!(env.status(id_normal).await, Status::Active);
    assert_eq!(env.pool().await.values, held);
    rows.push(json!({"mode": "normal", "execute_returns": "active", "status": "Active", "values": held, "event": ev}));

    // reject: execute returns "cancelled" -> settle(executor, false) ->
    // Cancelled, the reservation released.
    env.mode("reject").await;
    let id_reject = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    let before = reference.values.clone();
    let r = ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id_reject })).await;
    reference.dispatch(a, id_reject, env.now().await).unwrap();
    reference.settle(&x, id_reject, false).unwrap();
    same(&env, &reference, "reject").await;
    let ev = event(&r, env.lock.id(), "reconciled");
    assert_eq!(ev, json!({ "id": id_reject, "outcome": "cancelled", "error": null }));
    assert_eq!(env.status(id_reject).await, Status::Cancelled);
    assert_eq!(reference.values, held, "release undoes exactly the reservation");
    rows.push(json!({"mode": "reject", "execute_returns": "cancelled", "status": "Cancelled", "values_before": before, "values_after": reference.values, "event": ev}));

    // unknown: execute stores an active job but returns "unknown" ->
    // acknowledge(false) -> Unknown; reconcile (anyone) reads "active".
    env.mode("unknown").await;
    let id_unknown = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    let r = ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id_unknown })).await;
    reference.dispatch(a, id_unknown, env.now().await).unwrap();
    reference.acknowledge(id_unknown, false).unwrap();
    same(&env, &reference, "unknown").await;
    let ev = event(&r, env.lock.id(), "reconciled");
    assert_eq!(ev, json!({ "id": id_unknown, "outcome": "unknown", "error": null }));
    fails(&env.actor, env.lock.id(), "cancel", json!({ "id": id_unknown }), "Pending").await;
    let r = ok(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id_unknown })).await;
    reference.acknowledge(id_unknown, true).unwrap();
    same(&env, &reference, "reconcile unknown").await;
    let ev2 = event(&r, env.lock.id(), "reconciled");
    assert_eq!(ev2["outcome"], "active");
    // A repeated reconcile is a no-op, version included.
    let v = env.pool().await.version;
    ok(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id_unknown })).await;
    assert_eq!(env.pool().await.version, v);
    rows.push(json!({"mode": "unknown", "execute_returns": "unknown", "status": "Unknown", "event": ev, "cancel": "Pending", "reconcile": {"by": "mallory", "status_returns": "active", "status": "Active", "repeat_is_noop": true}}));

    // panic: execute fails -> the callback sees a PromiseError -> Unknown, the
    // reservation stays. The dispatch's own state change is not reverted.
    env.mode("panic").await;
    let id_panic = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    let held_panic = reference.values.clone();
    let r = tx(&env.actor, env.lock.id(), "dispatch", json!({ "id": id_panic })).await;
    let on_exec = receipts_on(&r, env.exec.id());
    let failed = on_exec.iter().find(|o| o.is_failure()).expect("execute should fail");
    let exec_failure = format!("{:?}", (*failed).clone().into_result().unwrap_err());
    let exec_panic = expect_panic(&exec_failure, "injected failure", false);
    assert!(r.is_success(), "the callback itself succeeds: {:?}", r.failures());
    reference.dispatch(a, id_panic, env.now().await).unwrap();
    reference.acknowledge(id_panic, false).unwrap();
    same(&env, &reference, "panic").await;
    let ev = event(&r, env.lock.id(), "reconciled");
    assert_eq!(ev, json!({ "id": id_panic, "outcome": "unknown", "error": null }));
    assert_eq!(env.pool().await.values, held_panic);
    // reconcile: no job, status "unknown" -> acknowledge(false), a no-op.
    let v = env.pool().await.version;
    ok(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id_panic })).await;
    assert_eq!(env.pool().await.version, v);
    // Definitive nonexecution from the operator releases it.
    ok(&env.owner, env.exec.id(), "confirm_not_executed", json!({ "id": id_panic, "recipe": 0, "units": 4 })).await;
    reference.settle(&x, id_panic, false).unwrap();
    same(&env, &reference, "confirm_not_executed").await;
    rows.push(json!({"mode": "panic", "execute": "fails", "execute_panic": exec_panic, "dispatch_tx_success": true, "status": "Unknown", "values": held_panic, "event": ev,
        "reconcile": "status unknown, no-op", "confirm_not_executed": {"status": "Cancelled", "values": reference.values}}));

    // Close the rest through the operator: Completed and Cancelled.
    ok(&env.owner, env.exec.id(), "finish", json!({ "id": id_normal, "completed": true })).await;
    reference.settle(&x, id_normal, true).unwrap();
    ok(&env.owner, env.exec.id(), "finish", json!({ "id": id_unknown, "completed": false })).await;
    reference.settle(&x, id_unknown, false).unwrap();
    same(&env, &reference, "finish").await;
    // Same terminal again: idempotent (TERM-1 through the executor).
    let v = env.pool().await.version;
    ok(&env.owner, env.exec.id(), "finish", json!({ "id": id_normal, "completed": true })).await;
    assert_eq!(env.pool().await.version, v);
    let statuses: Vec<String> = env.pool().await.records.iter().map(|c| format!("{:?}", c.status)).collect();
    assert_eq!(statuses, ["Completed", "Cancelled", "Cancelled", "Cancelled"]);
    record(
        "RT-CALLBACK",
        json!({ "property": "RT-CALLBACK", "assumption": "ASM-CALLBACK", "result": "pass", "modes": rows, "final": summary(&env.pool().await) }),
    );
}

// ---------------------------------------------------------------- RT-REVERT

/// PROP: RT-REVERT. A call whose core step fails panics and leaves the pool's
/// storage byte-for-byte unchanged (ASM-ATOMIC), with no event; a rejected
/// submit returns a decision instead and also writes nothing.
#[tokio::test]
async fn rt_revert_core_errors_write_nothing() {
    let env = Env::bare().await;
    let cfg = basic_config(env.owner.id(), &[(env.actor.id(), env.exec.id())]);
    let env = env.init(&cfg).await;
    let (o, a, m) = (env.owner.id().as_str(), env.actor.id().as_str(), env.mallory.id().as_str());
    let x = env.exec.id().as_str().to_string();
    let mut reference = env.pool().await;
    let reserved = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    let active = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": active })).await;
    reference.dispatch(a, active, env.now().await).unwrap();
    reference.acknowledge(active, true).unwrap();
    same(&env, &reference, "setup").await;
    let now = env.now().await;
    let mut rows = vec![];

    type Core<'a> = Box<dyn Fn(&mut Pool) -> Result<(), Error> + 'a>;
    // (signer, method, args, error, the same call on the core)
    let xs = x.clone();
    let cases: Vec<(&near_workspaces::Account, &str, Value, Error, Core)> = vec![
        (&env.mallory, "dispatch", json!({"id": reserved}), Error::Unauthorized, Box::new(move |p: &mut Pool| p.dispatch(m, reserved, now))),
        (&env.actor, "dispatch", json!({"id": 99}), Error::NotFound, Box::new(move |p: &mut Pool| p.dispatch(a, 99, now))),
        (&env.actor, "dispatch", json!({"id": active}), Error::InvalidState, Box::new(move |p: &mut Pool| p.dispatch(a, active, now))),
        (&env.actor, "settle", json!({"id": active, "completed": true}), Error::Unauthorized, Box::new(move |p: &mut Pool| p.settle(a, active, true))),
        (env.exec.as_account(), "settle", json!({"id": reserved, "completed": true}), Error::InvalidState, Box::new(|p: &mut Pool| p.settle(&xs, reserved, true))),
        (env.exec.as_account(), "settle", json!({"id": 99, "completed": false}), Error::NotFound, Box::new(|p: &mut Pool| p.settle(&xs, 99, false))),
        (&env.mallory, "cancel", json!({"id": reserved}), Error::Unauthorized, Box::new(move |p: &mut Pool| p.cancel(m, reserved, now))),
        (&env.actor, "cancel", json!({"id": active}), Error::Pending, Box::new(move |p: &mut Pool| p.cancel(a, active, now))),
        (&env.actor, "set_paused", json!({"paused": true}), Error::Unauthorized, Box::new(move |p: &mut Pool| p.set_paused(a, true))),
        (&env.owner, "observe", json!({"values": [50, 0]}), Error::Pending, Box::new(move |p: &mut Pool| p.observe(o, vec![50, 0], now))),
    ];
    for (signer, method, args, err, core) in cases {
        let raw = env.raw().await;
        let mut p = reference.clone();
        assert_eq!(core(&mut p), Err(err.clone()), "core disagrees on {method}");
        assert_eq!(p, reference, "core error changed the pool (TX-0)");
        let (observed, r) = fails_r(signer, env.lock.id(), method, args.clone(), &err.to_string()).await;
        assert!(events_on(&r, env.lock.id()).is_empty(), "{method}: event from a failed call");
        assert_eq!(env.raw().await, raw, "{method}: storage changed");
        rows.push(json!({"call": method, "signer": signer.id(), "args": args, "core_error": err.to_string(), "observed_panic": observed, "storage_unchanged": true, "events": 0}));
    }
    same(&env, &reference, "after errors").await;

    // Paused: dispatch panics, submit is rejected without a panic.
    ok(&env.owner, env.lock.id(), "set_paused", json!({ "paused": true })).await;
    reference.set_paused(o, true).unwrap();
    let raw = env.raw().await;
    let observed = fails(&env.actor, env.lock.id(), "dispatch", json!({ "id": reserved }), "Paused").await;
    assert_eq!(env.raw().await, raw);
    rows.push(json!({"call": "dispatch", "state": "paused", "core_error": "Paused", "observed_panic": observed, "storage_unchanged": true}));
    let req = env.request(0, 1).await;
    let (r, v) = env.submit(&env.actor, &req).await;
    assert_eq!(v["decision"]["reason"], "Paused");
    assert_eq!(event(&r, env.lock.id(), "decision")["allowed"], false);
    assert_eq!(env.raw().await, raw);
    rows.push(json!({"call": "submit", "state": "paused", "rejected": "Paused", "panic": false, "storage_unchanged": true}));
    ok(&env.owner, env.lock.id(), "set_paused", json!({ "paused": false })).await;
    reference.set_paused(o, false).unwrap();

    // Rejected submits (Stale, InvalidUnits, Unauthorized): no panic, one
    // decision event, nothing written.
    let raw = env.raw().await;
    let mut stale = env.request(0, 1).await;
    stale.version -= 1;
    for (signer, req, reason) in [
        (&env.actor, stale, "Stale"),
        (&env.actor, env.request(0, 11).await, "InvalidUnits"),
        (&env.mallory, env.request(0, 1).await, "Unauthorized"),
    ] {
        let (r, v) = env.submit(signer, &req).await;
        assert_eq!(v["decision"]["reason"], reason);
        assert_eq!(v["id"], Value::Null);
        assert_eq!(event(&r, env.lock.id(), "decision")["allowed"], false);
        assert_eq!(env.raw().await, raw, "rejected submit ({reason}) wrote state");
        rows.push(json!({"call": "submit", "rejected": reason, "panic": false, "storage_unchanged": true}));
    }
    same(&env, &reference, "after rejections").await;

    // Close everything, then observe with bad input: Bounds.
    ok(&env.actor, env.lock.id(), "cancel", json!({ "id": reserved })).await;
    reference.cancel(a, reserved, env.now().await).unwrap();
    ok(&env.owner, env.exec.id(), "finish", json!({ "id": active, "completed": true })).await;
    reference.settle(&x, active, true).unwrap();
    same(&env, &reference, "closed").await;
    for values in [vec![50], vec![50, 1_000_001], vec![-1_000_001, 0]] {
        let raw = env.raw().await;
        assert_eq!(reference.clone().observe(o, values.clone(), now), Err(Error::Bounds));
        let observed = fails(&env.owner, env.lock.id(), "observe", json!({ "values": values }), "Bounds").await;
        assert_eq!(env.raw().await, raw);
        rows.push(json!({"call": "observe", "values": values, "core_error": "Bounds", "observed_panic": observed, "storage_unchanged": true}));
    }

    // Version overflow (needs 2^32 - 1 effective transitions, so the state is
    // patched in): every effective transition fails Arithmetic. A submit the
    // preview allows is not "rejected": the shell's must(submit) panics.
    let mut maxed = env.pool().await;
    maxed.version = u32::MAX;
    env.worker.patch_state(env.lock.id(), b"STATE", &borsh::to_vec(&maxed).unwrap()).await.unwrap();
    assert_eq!(env.pool().await, maxed);
    let raw = env.raw().await;
    assert_eq!(maxed.clone().set_paused(o, true), Err(Error::Arithmetic));
    let observed = fails(&env.owner, env.lock.id(), "set_paused", json!({ "paused": true }), "Arithmetic").await;
    assert_eq!(env.raw().await, raw);
    rows.push(json!({"call": "set_paused", "state": "version = u32::MAX (patched)", "core_error": "Arithmetic", "observed_panic": observed, "storage_unchanged": true}));
    let req = pool_core::Request { recipe: 0, units: 1, version: u32::MAX, expires_at: env.now().await + 3600 };
    let preview: pool_core::Decision = env.lock.view("preview").args_json(json!({ "actor": env.actor.id(), "request": req })).await.unwrap().json().unwrap();
    assert!(preview.allowed, "preview allows at version u32::MAX: {preview:?}");
    let (observed, r) = fails_r(&env.actor, env.lock.id(), "submit", json!({ "request": req }), "Arithmetic").await;
    assert!(events_on(&r, env.lock.id()).is_empty());
    assert_eq!(env.raw().await, raw);
    rows.push(json!({"call": "submit", "state": "version = u32::MAX (patched)", "preview_allowed": true, "core_error": "Arithmetic", "observed_panic": observed, "note": "a panic, not a rejected decision (RD-PREVIEW's version < u32::MAX clause)", "storage_unchanged": true}));
    record("RT-REVERT", json!({ "property": "RT-REVERT", "assumption": "ASM-ATOMIC", "result": "pass", "cases": rows }));
}

// ------------------------------------------------------------------ RT-RACE

/// PROP: RT-RACE. The executor's settle lands before the dispatch callback
/// (deterministic on one shard with the helper executor, see relay/): the
/// late "active" ack is ignored, version included. Also with settle(false),
/// and for a stale reconcile read.
#[tokio::test]
async fn rt_race_settle_before_callback() {
    let env = Env::bare().await;
    let racer = deploy(&env.worker, "racer", 10, &relay_wasm()).await;
    let cfg = basic_config(env.owner.id(), &[(env.actor.id(), racer.id())]);
    let env = env.init(&cfg).await;
    let a = env.actor.id().as_str();
    let x = racer.id().as_str();
    let mut reference = env.pool().await;
    let mut rows = vec![];

    for completed in [true, false] {
        ok(&env.owner, racer.id(), "set_settle", json!({ "settle": completed })).await;
        let id = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
        let v0 = reference.version;
        let r = ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id })).await;
        reference.dispatch(a, id, env.now().await).unwrap();
        // The other order, for contrast: callback first, then settle.
        let mut callback_first = reference.clone();
        callback_first.acknowledge(id, true).unwrap();
        callback_first.settle(x, id, completed).unwrap();
        // The order NEAR produces here: settle, then the late ack (a no-op).
        reference.settle(x, id, completed).unwrap();
        let before_ack = reference.clone();
        reference.acknowledge(id, true).unwrap();
        assert_eq!(reference, before_ack, "late ack must be a no-op");
        same(&env, &reference, "race").await;
        assert_eq!(env.pool().await.version, v0 + 2, "dispatch + settle only");
        assert_eq!(callback_first.version, v0 + 3);
        let settled = event(&r, env.lock.id(), "settled");
        let ack = event(&r, env.lock.id(), "reconciled");
        assert_eq!(settled, json!({ "id": id, "completed": completed }));
        assert_eq!(ack, json!({ "id": id, "outcome": "active", "error": null }));
        let h_settle = block_height(&env.worker, receipts_on(&r, env.lock.id()).into_iter().find(|o| o.logs.iter().any(|l| l.contains("\"settled\""))).unwrap()).await;
        let h_ack = block_height(&env.worker, receipts_on(&r, env.lock.id()).into_iter().find(|o| o.logs.iter().any(|l| l.contains("\"reconciled\""))).unwrap()).await;
        assert!(h_settle <= h_ack);
        rows.push(json!({"path": "dispatch: execute settles, then returns active", "completed": completed,
            "status": format!("{:?}", env.status(id).await), "version_delta": 2, "callback_first_would_give": 3,
            "settle_block": h_settle, "callback_block": h_ack, "late_ack_event": ack}));
    }

    // Stale reconcile read: an Active record; reconcile's status call
    // settles first and answers "active".
    ok(&env.owner, racer.id(), "set_settle", json!({ "settle": null })).await;
    let id = env.submit_ok(&mut reference, &env.actor, 0, 4).await;
    ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id })).await;
    reference.dispatch(a, id, env.now().await).unwrap();
    reference.acknowledge(id, true).unwrap();
    same(&env, &reference, "active").await;
    ok(&env.owner, racer.id(), "set_settle", json!({ "settle": true })).await;
    let v0 = reference.version;
    let r = ok(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id })).await;
    reference.settle(x, id, true).unwrap();
    reference.acknowledge(id, true).unwrap();
    same(&env, &reference, "stale reconcile").await;
    assert_eq!(env.pool().await.version, v0 + 1);
    assert_eq!(event(&r, env.lock.id(), "reconciled")["outcome"], "active");
    // A terminal record cannot be reconciled at all.
    let observed = fails_containing(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id }), "InvalidState").await;
    rows.push(json!({"path": "reconcile: status settles, then returns active", "completed": true,
        "status": format!("{:?}", env.status(id).await), "version_delta": 1, "reconcile_after_terminal": observed}));
    record("RT-RACE", json!({ "property": "RT-RACE", "assumption": "ASM-INTERLEAVE", "result": "pass", "executor": "helper (relay/ deployed as racer)", "cases": rows }));
}

/// PROP: RT-RACE (upstream executor). The upstream executor contract cannot
/// overtake its own callback on one shard: `finish` needs the job that
/// `execute` creates in the receipt that also emits the callback's data, so
/// its notify lands after the callback. The executor account's own key can:
/// a settle sent while the dispatch is in flight. Timed race, repeated over a
/// range of delays; every outcome must be one of the serial orders the core
/// allows, and the late-ack order must occur at least once.
#[tokio::test]
async fn rt_race_executor_key_settles_while_callback_in_flight() {
    const DELAYS_MS: [u64; 6] = [0, 100, 200, 300, 400, 150];
    const ATTEMPTS: usize = 16;
    let env = Env::bare().await;
    let cfg = basic_config(env.owner.id(), &[(env.actor.id(), env.exec.id())]);
    let env = env.init(&cfg).await;
    let a = env.actor.id().as_str();
    let x = env.exec.id().as_str();
    let mut reference = env.pool().await;
    let mut rows = vec![];
    let mut late = 0;
    for attempt in 0..ATTEMPTS {
        let delay = DELAYS_MS[attempt % DELAYS_MS.len()];
        let id = env.submit_ok(&mut reference, &env.actor, 0, 1).await;
        let v0 = reference.version;
        let t1 = env.actor.call(env.lock.id(), "dispatch").args_json(json!({ "id": id })).max_gas().transact_async().await.unwrap();
        tokio::time::sleep(Duration::from_millis(delay)).await;
        let t2 = env
            .exec
            .as_account()
            .call(env.lock.id(), "settle")
            .args_json(json!({ "id": id, "completed": true }))
            .max_gas()
            .transact_async()
            .await
            .unwrap();
        let start = Instant::now();
        let r1 = t1.await.unwrap();
        let r2 = t2.await.unwrap();
        assert!(start.elapsed() < Duration::from_secs(60));
        assert!(r1.is_success(), "{:?}", r1.failures());
        let on_pool = receipts_on(&r1, env.lock.id());
        let ack_receipt = on_pool.iter().find(|o| o.logs.iter().any(|l| l.contains("\"reconciled\""))).unwrap();
        let dispatch_receipt = on_pool.iter().find(|o| !o.logs.iter().any(|l| l.contains("\"reconciled\""))).unwrap();
        let settle_receipt = receipts_on(&r2, env.lock.id())[0];
        let heights = json!({
            "dispatch": block_height(&env.worker, dispatch_receipt).await,
            "execute": block_height(&env.worker, receipts_on(&r1, env.exec.id())[0]).await,
            "callback": block_height(&env.worker, ack_receipt).await,
            "settle": block_height(&env.worker, settle_receipt).await,
        });
        // The three serial orders the core allows.
        let mut settle_first = reference.clone();
        assert_eq!(settle_first.clone().settle(x, id, true), Err(Error::InvalidState));
        settle_first.dispatch(a, id, 0).unwrap();
        settle_first.acknowledge(id, true).unwrap();
        let mut late_ack = reference.clone();
        late_ack.dispatch(a, id, 0).unwrap();
        late_ack.settle(x, id, true).unwrap();
        late_ack.acknowledge(id, true).unwrap();
        let mut serial = reference.clone();
        serial.dispatch(a, id, 0).unwrap();
        serial.acknowledge(id, true).unwrap();
        serial.settle(x, id, true).unwrap();
        let p = env.pool().await;
        let order = if r2.is_failure() {
            assert_eq!(p, settle_first, "attempt {attempt}");
            let observed = expect_panic(&failure_text(&r2), "InvalidState", true);
            json!({ "order": "settle before dispatch: rejected", "observed_panic": observed })
        } else if p == late_ack {
            late += 1;
            json!({ "order": "dispatch, settle, callback: late ack ignored" })
        } else if p == serial {
            json!({ "order": "dispatch, callback, settle" })
        } else {
            panic!("attempt {attempt}: no serial order gives {p:?}");
        };
        assert_eq!(event(&r1, env.lock.id(), "reconciled")["error"], Value::Null);
        let mut row = json!({ "attempt": attempt, "delay_ms": delay, "version_delta": p.version - v0, "blocks": heights });
        row.as_object_mut().unwrap().extend(order.as_object().unwrap().clone());
        rows.push(row);
        reference = p;
        if late >= 3 {
            break;
        }
    }
    record(
        "RT-RACE-timed",
        json!({ "property": "RT-RACE", "executor": "upstream pool_executor, its account key signing settle", "late_ack_hits": late, "attempts": rows }),
    );
    assert!(late > 0, "the late-ack interleaving never occurred in {ATTEMPTS} attempts");
}

/// PROP: RT-RACE (upstream executor, operator `finish`): the same timed race with
/// the operator's `finish(id, true)`, the path the property names. `finish`
/// needs the job `execute` creates; NEAR emits `execute`'s data receipt (the
/// callback's input) before any receipt `finish` can create later, so on one
/// shard the notify cannot overtake the callback. Every outcome must be a
/// serial order the core allows; the counts are recorded, and a late-ack hit
/// here would only strengthen RT-RACE.
#[tokio::test]
async fn rt_race_operator_finish_vs_callback() {
    // Finer around the 200-300 ms boundary seen in the first runs, where
    // finish lands in execute's block or the next one.
    const DELAYS_MS: [u64; 8] = [0, 150, 200, 225, 250, 275, 300, 400];
    const ATTEMPTS: usize = 16;
    let env = Env::bare().await;
    let cfg = basic_config(env.owner.id(), &[(env.actor.id(), env.exec.id())]);
    let env = env.init(&cfg).await;
    let a = env.actor.id().as_str();
    let x = env.exec.id().as_str();
    let mut reference = env.pool().await;
    let mut rows = vec![];
    let mut counts = std::collections::BTreeMap::<&str, u32>::new();
    for attempt in 0..ATTEMPTS {
        let delay = DELAYS_MS[attempt % DELAYS_MS.len()];
        let id = env.submit_ok(&mut reference, &env.actor, 0, 1).await;
        let v0 = reference.version;
        let t1 = env.actor.call(env.lock.id(), "dispatch").args_json(json!({ "id": id })).max_gas().transact_async().await.unwrap();
        tokio::time::sleep(Duration::from_millis(delay)).await;
        let t2 = env.owner.call(env.exec.id(), "finish").args_json(json!({ "id": id, "completed": true })).max_gas().transact_async().await.unwrap();
        let r1 = t1.await.unwrap();
        let r2 = t2.await.unwrap();
        assert!(r1.is_success(), "{:?}", r1.failures());
        let mut late_ack = reference.clone();
        late_ack.dispatch(a, id, 0).unwrap();
        late_ack.settle(x, id, true).unwrap();
        late_ack.acknowledge(id, true).unwrap();
        let mut serial = reference.clone();
        serial.dispatch(a, id, 0).unwrap();
        serial.acknowledge(id, true).unwrap();
        let mut p = env.pool().await;
        let (order, finish_block) = if r2.is_failure() {
            // finish ran before execute created the job: nothing notified.
            assert_eq!(p, serial, "attempt {attempt}");
            let observed = expect_panic(&failure_text(&r2), "unknown job", false);
            ok(&env.owner, env.exec.id(), "finish", json!({ "id": id, "completed": true })).await;
            serial.settle(x, id, true).unwrap();
            p = env.pool().await;
            assert_eq!(p, serial);
            (format!("finish before execute: rejected ({observed}); finished afterwards"), Value::Null)
        } else {
            let h = json!(block_height(&env.worker, receipts_on(&r2, env.lock.id())[0]).await);
            serial.settle(x, id, true).unwrap();
            if p == late_ack {
                ("dispatch, finish->settle, callback: late ack ignored".to_string(), h)
            } else {
                assert_eq!(p, serial, "attempt {attempt}: no serial order");
                ("dispatch, callback, finish->settle".to_string(), h)
            }
        };
        let key = if order.starts_with("finish before") { "finish_before_execute" } else if order.contains("late ack") { "late_ack" } else { "callback_first" };
        *counts.entry(key).or_default() += 1;
        let ack = receipts_on(&r1, env.lock.id()).into_iter().find(|o| o.logs.iter().any(|l| l.contains("\"reconciled\""))).unwrap();
        rows.push(json!({
            "attempt": attempt, "delay_ms": delay, "order": order, "version_delta_dispatch_to_terminal": p.version - v0,
            "blocks": { "execute": block_height(&env.worker, receipts_on(&r1, env.exec.id())[0]).await, "callback": block_height(&env.worker, ack).await, "settle": finish_block },
        }));
        reference = p;
    }
    record(
        "RT-RACE-finish",
        json!({ "property": "RT-RACE", "executor": "upstream pool_executor, operator finish", "counts": counts, "attempts": rows,
            "note": "single shard: finish's notify is created after execute's data receipt, so the callback runs first" }),
    );
}

// ---------------------------------------------------------------- RT-WEDGE

async fn wedged(env: &Env, reference: &Pool, id: u32, label: &str) {
    same(env, reference, label).await;
    assert_eq!(env.status(id).await, Status::Active, "{label}");
}

/// PROP: RT-WEDGE. F-1 end to end on the wasm, with the upstream executor:
/// after a disturbing observe, an admitted hedge completes, the completion
/// notify fails Bounds, the executor's job is completed but the pool's record
/// stays open, no path closes it, and observe fails Pending.
#[tokio::test]
async fn rt_wedge_f1_end_to_end() {
    let env = Env::bare().await;
    let cfg = wedge_config(env.owner.id(), env.actor.id(), env.exec.id());
    let env = env.init(&cfg).await;
    let (o, a) = (env.owner.id().as_str(), env.actor.id().as_str());
    let x = env.exec.id().as_str().to_string();
    let mut reference = env.pool().await;
    let mut steps = vec![];

    ok(&env.owner, env.lock.id(), "observe", json!({ "values": [12, 5] })).await;
    reference.observe(o, vec![12, 5], env.now().await).unwrap();
    reference.observed_at = env.pool().await.observed_at;
    same(&env, &reference, "observe [12, 5]").await;
    steps.push(json!({"step": "owner observe [12, 5]", "result": "Ok", "values": [12, 5]}));

    let id = env.submit_ok(&mut reference, &env.actor, 0, 1).await;
    same(&env, &reference, "submit").await;
    steps.push(json!({"step": "actor submit recipe 0 x 1", "result": "Ok (allowed)", "values": reference.values}));
    ok(&env.actor, env.lock.id(), "dispatch", json!({ "id": id })).await;
    reference.dispatch(a, id, env.now().await).unwrap();
    reference.acknowledge(id, true).unwrap();
    same(&env, &reference, "dispatch").await;
    steps.push(json!({"step": "actor dispatch", "result": "Ok: execute -> active -> Active"}));

    // finish(completed): the executor commits "completed", its notify fails.
    let r = tx(&env.owner, env.exec.id(), "finish", json!({ "id": id, "completed": true })).await;
    let notify = expect_panic(&failure_text(&r), "Bounds", true);
    assert!(receipts_on(&r, env.exec.id())[0].is_success(), "finish itself commits");
    assert_eq!(reference.clone().settle(&x, id, true), Err(Error::Bounds));
    same(&env, &reference, "finish").await;
    // get_jobs is #[private]: called by the executor account itself.
    let jobs: Value = ok(env.exec.as_account(), env.exec.id(), "get_jobs", json!({})).await.json().unwrap();
    assert_eq!(jobs[0]["status"], "completed");
    assert_eq!(env.status(id).await, Status::Active);
    steps.push(json!({"step": "operator finish(id, completed)", "executor_job": "completed", "notify settle(true)": {"core_error": "Bounds", "observed_panic": notify}, "pool_record": "Active"}));

    // reconcile: status "completed" -> settle(true) -> Bounds, only in the event.
    let r = ok(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id })).await;
    let ev = event(&r, env.lock.id(), "reconciled");
    assert_eq!(ev, json!({ "id": id, "outcome": "completed", "error": "Bounds" }));
    wedged(&env, &reference, id, "reconcile").await;
    steps.push(json!({"step": "anyone reconcile(id)", "result": "Ok (no panic), record unchanged", "event": ev}));
    // The executor cannot change its answer; repeating it fails again.
    let c1 = fails_containing(&env.owner, env.exec.id(), "finish", json!({ "id": id, "completed": false }), "terminal outcome conflict").await;
    let c2 = fails_containing(&env.owner, env.exec.id(), "confirm_not_executed", json!({ "id": id, "recipe": 0, "units": 1 }), "job exists").await;
    let c3 = fails(&env.owner, env.exec.id(), "finish", json!({ "id": id, "completed": true }), "Bounds").await;
    wedged(&env, &reference, id, "executor").await;
    steps.push(json!({"step": "operator finish(id, cancelled) / confirm_not_executed / finish(id, completed) again",
        "expected": ["terminal outcome conflict", "job exists", "Bounds"], "observed_panic": [c1, c2, c3]}));
    // Even the executor account's own key: both settles fail Bounds.
    let mut observed = vec![];
    for completed in [true, false] {
        assert_eq!(reference.clone().settle(&x, id, completed), Err(Error::Bounds));
        observed.push(fails(env.exec.as_account(), env.lock.id(), "settle", json!({ "id": id, "completed": completed }), "Bounds").await);
    }
    wedged(&env, &reference, id, "settle").await;
    steps.push(json!({"step": "executor key settle(id, true), settle(id, false)", "core_error": ["Bounds", "Bounds"], "observed_panic": observed}));
    let mut observed = vec![];
    for who in [&env.actor, &env.owner] {
        observed.push(fails(who, env.lock.id(), "cancel", json!({ "id": id }), "Pending").await);
    }
    steps.push(json!({"step": "actor / owner cancel(id)", "core_error": "Pending", "observed_panic": observed}));
    let mut observed = vec![];
    for values in [vec![5, 5], vec![10, 5], vec![12, 0]] {
        assert_eq!(reference.clone().observe(o, values.clone(), 0), Err(Error::Pending));
        observed.push(fails(&env.owner, env.lock.id(), "observe", json!({ "values": values }), "Pending").await);
    }
    steps.push(json!({"step": "owner observe [5,5], [10,5], [12,0]", "core_error": "Pending", "observed_panic": observed}));
    fails(&env.actor, env.lock.id(), "dispatch", json!({ "id": id }), "InvalidState").await;
    wedged(&env, &reference, id, "all paths").await;

    // Time does not help: no expiry applies to a dispatched record.
    env.worker.fast_forward(200).await.unwrap();
    fails(&env.owner, env.lock.id(), "observe", json!({ "values": [5, 5] }), "Pending").await;
    let r = ok(&env.mallory, env.lock.id(), "reconcile", json!({ "id": id })).await;
    assert_eq!(event(&r, env.lock.id(), "reconciled")["error"], "Bounds");
    fails(env.exec.as_account(), env.lock.id(), "settle", json!({ "id": id, "completed": true }), "Bounds").await;
    wedged(&env, &reference, id, "after fast_forward").await;
    steps.push(json!({"step": "fast_forward 200 blocks; observe / reconcile / executor-key settle", "result": "Pending / event error Bounds / Bounds"}));

    let p = env.pool().await;
    record(
        "RT-WEDGE",
        json!({
            "property": "RT-WEDGE", "finding": "F-1", "result": "wedge reproduced on the wasm: LIVE-2 violated",
            "config": "m(0,10,5), m(-100,100,5); t(1,0,1,target); r(actor, exec, [-2,0], [2,-5], 1, [])",
            "steps": steps,
            "final": {"values": p.values, "version": p.version, "record": format!("{:?}", p.records[0].status), "executor_job": "completed", "open_records": 1}
        }),
    );
}

// ----------------------------------------------------------------- SB-1

/// Finding SB-1 witness (RT-REVERT's error string; near-tests SH-5 on the
/// deployed artifact). Both builds side by side: the upstream build (plain
/// `cargo build`, scripts/build.sh) reports every panic as a bare
/// `unreachable` trap; the cfg(near) build of the same source reports the
/// message. Passes while the finding reproduces; fails (stale witness) once
/// upstream builds with cfg(near).
#[tokio::test]
async fn sb1_upstream_build_loses_panic_messages() {
    let worker = sandbox().await;
    let owner = subaccount(&worker, "owner", 20).await;
    let actor = subaccount(&worker, "actor", 20).await;
    let mallory = subaccount(&worker, "mallory", 20).await;
    let mut rows = vec![];
    for variant in ["upstream", "cfg-near"] {
        let tag = if variant == "upstream" { "up" } else { "nr" };
        let lock = deploy(&worker, &format!("pool-{tag}"), 30, &wasm_of(variant, "pool_contract")).await;
        let exec = deploy(&worker, &format!("exec-{tag}"), 20, &wasm_of(variant, "pool_executor")).await;
        let cfg = basic_config(owner.id(), &[(actor.id(), exec.id())]);
        let mut seen = serde_json::Map::new();
        let msg = |r: &near_workspaces::result::ExecutionFinalResult| panic_message(&failure_text(r));
        seen.insert("pool.new by mallory".into(), json!(msg(&tx(&mallory, lock.id(), "new", json!({ "config": cfg })).await)));
        ok(lock.as_account(), lock.id(), "new", json!({ "config": cfg })).await;
        ok(exec.as_account(), exec.id(), "new", json!({ "lock": lock.id(), "operator": owner.id() })).await;
        seen.insert("pool.set_paused by mallory (core Unauthorized)".into(), json!(msg(&tx(&mallory, lock.id(), "set_paused", json!({ "paused": true })).await)));
        seen.insert("pool.dispatch(99) (core NotFound)".into(), json!(msg(&tx(&actor, lock.id(), "dispatch", json!({ "id": 99 })).await)));
        seen.insert("pool.on_result by mallory".into(), json!(msg(&tx(&mallory, lock.id(), "on_result", json!({ "id": 0 })).await)));
        seen.insert("exec.finish by mallory".into(), json!(msg(&tx(&mallory, exec.id(), "finish", json!({ "id": 0, "completed": true })).await)));
        let all: Vec<String> = seen.values().map(|v| v.as_str().unwrap().to_string()).collect();
        if variant == "upstream" {
            assert!(all.iter().all(|m| m == TRAP), "upstream: {all:?}");
        } else {
            assert_eq!(seen["pool.new by mallory"], "Method new is private");
            assert_eq!(seen["pool.set_paused by mallory (core Unauthorized)"], "Unauthorized");
            assert_eq!(seen["pool.dispatch(99) (core NotFound)"], "NotFound");
            assert_eq!(seen["pool.on_result by mallory"], "Method on_result is private");
            assert!(seen["exec.finish by mallory"].as_str().unwrap().contains("only independent operator"));
        }
        rows.push(json!({ "variant": variant, "pool_contract_sha256": sha256_hex(&wasm_of(variant, "pool_contract")), "observed": seen }));
    }
    record(
        "SB-1",
        json!({ "finding": "SB-1", "summary": "upstream scripts/build.sh builds without cfg(near); near-sdk's panic_str then traps without calling panic_utf8, so every on-chain failure is a bare unreachable trap",
            "result": "reproduced", "builds": rows }),
    );
}
