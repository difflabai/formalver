//! RES-1: gas at a maximum-size state, on the real wasm in near-sandbox.
//!
//! The state is reached through real transactions only (no state patching):
//! 32 metrics with 128-byte names and units, 64 terms, 32 recipes with
//! 128-byte names, 64-byte actor and executor ids, full 32-entry effect
//! vectors and the longest prerequisite lists validate allows (recipe i
//! requires every j < i, so recipe 31 has 31), and MAX_RECORDS = 256 records:
//! 31 Completed (recipes 0..30, the prerequisites of recipe 31) and 225 open
//! recipe-31 reservations of 100 units. The 256th submit is the costliest
//! admission there is under these limits: the shell runs the admission twice
//! (preview, then submit), each scanning 31 prerequisites over 255 records and
//! the pending envelope over 224 open records x 32 metrics.
//!
//! Measured: gas burnt per receipt on the pool (and the transaction total)
//! for submit, a Full rejection, preview, get_pool and get_commitments (as
//! transactions, plus the get_pool view), dispatch (with execute and the
//! on_result callback), settle(true) through the executor's notify, settle by
//! the executor key, release (cancel), reconcile; margins to 300 Tgas and to
//! the fixed gas the shell attaches (execute 30, on_result 30, status 10,
//! the executor's notify 40).
//!
//! A second RES-1 test builds the same state and then (a) finds, by a
//! whole-Tgas sweep, the smallest prepaid gas for which dispatch, reconcile
//! and the executor's finish succeed; every smaller amount must fail with
//! "Exceeded the prepaid gas." and change nothing (raw storage of both
//! contracts byte-identical, no event, the pool equal to the oracle); and
//! (b) dispatches every record the pool can hold, so the executor holds its
//! cap of 256 jobs, and measures execute, status and finish there.
#![allow(unused_must_use)]
mod common;

use common::*;
use near_workspaces::network::Sandbox;
use near_workspaces::result::ExecutionFinalResult;
use near_workspaces::{Account, AccountId, Contract, Worker};
use pool_core::{Config, Metric, Pool, Recipe, Request, Shape, Status, Term, MAX_RECORDS};
use serde_json::{json, Value};
use std::time::Instant;

const N_METRICS: usize = 32;
const N_RECIPES: usize = 32;

fn long(c: char, len: usize, tag: usize) -> String {
    let t = tag.to_string();
    format!("{}{}", c.to_string().repeat(len - t.len()), t)
}

fn max_config(owner: &AccountId, actor: &AccountId, executor: &AccountId) -> Config {
    let metrics = (0..N_METRICS)
        .map(|i| Metric { name: long('M', 128, i), unit: long('U', 128, i), initial: 0, min: -1_000_000, max: 1_000_000 })
        .collect();
    let mut terms = vec![];
    for i in 0..N_METRICS as u32 {
        terms.push(Term { metric: i, target: 0, weight: 1000, shape: Shape::Target });
        terms.push(Term { metric: i, target: 0, weight: 1000, shape: if i % 2 == 0 { Shape::Excess } else { Shape::Deficit } });
    }
    let recipes = (0..N_RECIPES)
        .map(|i| Recipe {
            name: long('R', 128, i),
            actor: actor.to_string(),
            executor: executor.to_string(),
            // Reservations are energy-neutral, so every one is admissible;
            // the checked arithmetic costs the same for any value.
            reserve: vec![0; N_METRICS],
            complete: (0..N_METRICS).map(|j| if (i + j) % 2 == 0 { 1 } else { -1 }).collect(),
            max_units: 100,
            requires: (0..i as u32).map(|j| (j, 1)).collect(),
        })
        .collect();
    Config { name: long('N', 128, 0), owner: owner.to_string(), metrics, terms, recipes, max_age_seconds: 86_400 }
}

struct Gas {
    rows: Vec<Value>,
}

impl Gas {
    /// Records the gas burnt by each receipt of `r` on `on` (in order) and the
    /// transaction total; returns the largest receipt.
    fn add(&mut self, what: &str, r: &ExecutionFinalResult, on: &[(&AccountId, &str)], budget: Option<(usize, u64)>) -> u64 {
        let mut receipts = vec![];
        for (account, label) in on {
            for o in receipts_on(r, account) {
                receipts.push(json!({ "on": label, "gas_tgas": tgas(o.gas_burnt.as_gas()), "gas": o.gas_burnt.as_gas(), "ok": o.is_success() }));
            }
        }
        let max = receipts.iter().map(|v| v["gas"].as_u64().unwrap()).max().unwrap_or(0);
        let total = r.total_gas_burnt.as_gas();
        let mut row = json!({
            "call": what,
            "tx_total_tgas": tgas(total),
            "receipts": receipts,
            "margin_to_300_tgas": tgas(TX_GAS_LIMIT - total),
        });
        if let Some((i, b)) = budget {
            let g = row["receipts"][i]["gas"].as_u64().unwrap();
            row["attached_budget_tgas"] = json!(b / TGAS);
            row["margin_to_budget_tgas"] = json!(tgas(b.saturating_sub(g)));
            assert!(g < b, "{what}: receipt {i} burnt {g} of its {b} budget");
        }
        assert!(total < TX_GAS_LIMIT, "{what}: {total} gas");
        eprintln!("RES-1 {row}");
        self.rows.push(row);
        max
    }
}

/// The maximum-size state at 255 records (module doc), built with real
/// transactions only, with the host-side oracle in step.
struct Max {
    worker: Worker<Sandbox>,
    owner: Account,
    actor: Account,
    lock: Contract,
    exec: Contract,
    reference: Pool,
    a: String,
    x: String,
    now: u64,
    expires_at: u64,
    r_new: ExecutionFinalResult,
    submit_curve: Vec<(usize, u64)>,
}

async fn build_max(t0: Instant) -> Max {
    let worker = sandbox().await;
    // 64-byte account ids (54 + ".test.near") for the ids stored per recipe.
    let owner = subaccount(&worker, &"o".repeat(54), 20).await;
    let actor = subaccount(&worker, &"a".repeat(54), 50).await;
    let lock = deploy(&worker, "pool", 50, &contract_wasm()).await;
    let exec = deploy(&worker, &"x".repeat(54), 50, &executor_wasm()).await;
    assert_eq!(actor.id().as_str().len(), 64);
    let cfg = max_config(owner.id(), actor.id(), exec.id());
    cfg.validate().expect("max config validates");
    assert_eq!((cfg.metrics.len(), cfg.terms.len(), cfg.recipes.len()), (32, 64, 32));
    let r_new = ok(lock.as_account(), lock.id(), "new", json!({ "config": cfg })).await;
    ok(exec.as_account(), exec.id(), "new", json!({ "lock": lock.id(), "operator": owner.id() })).await;
    let mut reference: Pool = pool(&lock).await;
    assert_eq!(reference, Pool::new(cfg.clone(), reference.observed_at).unwrap());
    let a = actor.id().as_str().to_string();
    let x = exec.id().as_str().to_string();
    let now = block_now(&worker).await;
    let expires_at = now + 3 * 3600;
    let mut submit_curve = vec![];

    let submit = |recipe: u32, units: u32, version: u32| {
        let actor = actor.clone();
        let lock = lock.id().clone();
        async move {
            let req = Request { recipe, units, version, expires_at };
            let r = ok(&actor, &lock, "submit", json!({ "request": req })).await;
            (req, r)
        }
    };

    // 31 Completed prerequisites: recipe i (requires 0..i) x 1 unit.
    for i in 0..31u32 {
        let (req, r) = submit(i, 1, reference.version).await;
        let v: Value = r.clone().json().unwrap();
        assert_eq!(v["decision"]["allowed"], true, "prerequisite {i}: {v}");
        let id = reference.submit(&a, req, now).unwrap();
        submit_curve.push((reference.records.len(), receipts_on(&r, lock.id())[0].gas_burnt.as_gas()));
        ok(&actor, lock.id(), "dispatch", json!({ "id": id })).await;
        reference.dispatch(&a, id, now).unwrap();
        reference.acknowledge(id, true).unwrap();
        ok(&owner, exec.id(), "finish", json!({ "id": id, "completed": true })).await;
        reference.settle(&x, id, true).unwrap();
    }
    assert_eq!(pool(&lock).await, reference, "after prerequisites");
    eprintln!("prerequisites done in {:?}", t0.elapsed());

    // 224 open reservations of recipe 31 (31 prerequisites) x 100 units.
    while reference.records.len() < MAX_RECORDS - 1 {
        let (req, r) = submit(31, 100, reference.version).await;
        let v: Value = r.clone().json().unwrap();
        assert_eq!(v["decision"]["allowed"], true, "open record {}: {v}", reference.records.len());
        reference.submit(&a, req, now).unwrap();
        submit_curve.push((reference.records.len(), receipts_on(&r, lock.id())[0].gas_burnt.as_gas()));
    }
    assert_eq!(pool(&lock).await, reference, "at 255 records");
    eprintln!("255 records in {:?}", t0.elapsed());
    Max { worker, owner, actor, lock, exec, reference, a, x, now, expires_at, r_new, submit_curve }
}

/// PROP: RES-1
#[tokio::test]
async fn res_1_gas_at_max_state() {
    let t0 = Instant::now();
    let Max { worker, owner, actor, lock, exec, mut reference, a, x, now, expires_at, r_new, mut submit_curve } = build_max(t0).await;
    let pool_on = [(lock.id(), "pool")];
    let mut gas = Gas { rows: vec![] };
    gas.add("new (max config)", &r_new, &pool_on, None);

    let submit = |recipe: u32, units: u32, version: u32| {
        let actor = actor.clone();
        let lock = lock.id().clone();
        async move {
            let req = Request { recipe, units, version, expires_at };
            let r = ok(&actor, &lock, "submit", json!({ "request": req })).await;
            (req, r)
        }
    };

    // preview of the same request (one admission, no write), as a transaction.
    let req = Request { recipe: 31, units: 100, version: reference.version, expires_at };
    let r = ok(&actor, lock.id(), "preview", json!({ "actor": actor.id(), "request": req })).await;
    let d: Value = r.clone().json().unwrap();
    assert_eq!(d["allowed"], true, "{d}");
    gas.add("preview at 255 records (as a transaction)", &r, &pool_on, None);

    // The 256th submit: the measured worst case.
    let (req, r) = submit(31, 100, reference.version).await;
    let v: Value = r.clone().json().unwrap();
    assert_eq!(v["decision"]["allowed"], true, "{v}");
    let last = reference.submit(&a, req, now).unwrap();
    assert_eq!(last as usize, MAX_RECORDS - 1);
    submit_curve.push((reference.records.len(), receipts_on(&r, lock.id())[0].gas_burnt.as_gas()));
    let submit_max = gas.add("submit #256 (recipe 31, 31 prerequisites, 224 open records)", &r, &pool_on, None);
    assert_eq!(pool(&lock).await, reference, "at 256 records");
    let open = reference.records.iter().filter(|c| c.status == Status::Reserved).count();
    assert_eq!((reference.records.len(), open), (256, 225));

    // 257th: Full, a rejected decision.
    let (_, r) = submit(31, 100, reference.version).await;
    let v: Value = r.clone().json().unwrap();
    assert_eq!(v["decision"]["reason"], "Full");
    gas.add("submit #257 (rejected Full)", &r, &pool_on, None);

    // Reads.
    let r = ok(&actor, lock.id(), "get_pool", json!({})).await;
    let json_len = r.clone().into_result().unwrap().raw_bytes().unwrap().len();
    let get_pool_tx = gas.add("get_pool (as a transaction)", &r, &pool_on, None);
    let viewed: Pool = pool(&lock).await;
    assert_eq!(viewed, reference, "get_pool view at max state");
    let r = ok(&actor, lock.id(), "get_commitments", json!({ "from": 0, "limit": 1000 })).await;
    let page: Vec<Value> = r.clone().json().unwrap();
    assert_eq!(page.len(), 50);
    gas.add("get_commitments(0, 1000) -> 50 (as a transaction)", &r, &pool_on, None);
    let state_bytes = raw_state(&worker, lock.id()).await.get(b"STATE".as_slice()).map(Vec::len).unwrap();
    let storage_usage = lock.view_account().await.unwrap().storage_usage;

    // dispatch at max state: dispatch, execute (30 Tgas), on_result (30 Tgas).
    let id = last;
    let r = ok(&actor, lock.id(), "dispatch", json!({ "id": id })).await;
    reference.dispatch(&a, id, now).unwrap();
    reference.acknowledge(id, true).unwrap();
    let on_dispatch = [(lock.id(), "pool"), (exec.id(), "exec")];
    // receipts: pool.dispatch, pool.on_result, exec.execute
    gas.add("dispatch (pool.dispatch, pool.on_result [30 Tgas], exec.execute [30 Tgas])", &r, &on_dispatch, Some((1, 30 * TGAS)));
    let exec_receipt = receipts_on(&r, exec.id())[0].gas_burnt.as_gas();
    assert!(exec_receipt < 30 * TGAS);
    assert_eq!(pool(&lock).await, reference);

    // settle(true) through the executor: finish -> notify settle (40 Tgas).
    let r = ok(&owner, exec.id(), "finish", json!({ "id": id, "completed": true })).await;
    reference.settle(&x, id, true).unwrap();
    gas.add("finish -> notify settle(true) [40 Tgas]", &r, &pool_on, Some((0, 40 * TGAS)));
    assert_eq!(pool(&lock).await, reference);

    // settle(true) and settle(false) by the executor key (300 Tgas).
    for (id, completed) in [(31u32, true), (32u32, false)] {
        ok(&actor, lock.id(), "dispatch", json!({ "id": id })).await;
        reference.dispatch(&a, id, now).unwrap();
        reference.acknowledge(id, true).unwrap();
        let r = ok(exec.as_account(), lock.id(), "settle", json!({ "id": id, "completed": completed })).await;
        reference.settle(&x, id, completed).unwrap();
        gas.add(&format!("settle({completed}) by the executor key"), &r, &pool_on, None);
    }
    // release through cancel, and through the executor's notify (40 Tgas).
    let r = ok(&actor, lock.id(), "cancel", json!({ "id": 33 })).await;
    reference.cancel(&a, 33, now).unwrap();
    gas.add("cancel (release)", &r, &pool_on, None);
    ok(&actor, lock.id(), "dispatch", json!({ "id": 34 })).await;
    reference.dispatch(&a, 34, now).unwrap();
    reference.acknowledge(34, true).unwrap();
    // reconcile: pool.reconcile, exec.status (10 Tgas), pool.on_result (30 Tgas).
    let r = ok(&owner, lock.id(), "reconcile", json!({ "id": 34 })).await;
    gas.add("reconcile (pool.reconcile, pool.on_result [30 Tgas], exec.status [10 Tgas])", &r, &on_dispatch, Some((1, 30 * TGAS)));
    assert!(receipts_on(&r, exec.id())[0].gas_burnt.as_gas() < 10 * TGAS);
    let r = ok(&owner, exec.id(), "finish", json!({ "id": 34, "completed": false })).await;
    reference.settle(&x, 34, false).unwrap();
    gas.add("finish -> notify settle(false) [40 Tgas]", &r, &pool_on, Some((0, 40 * TGAS)));
    assert_eq!(pool(&lock).await, reference, "final");

    let worst = gas
        .rows
        .iter()
        .flat_map(|r| r["receipts"].as_array().unwrap().iter().filter(|x| x["on"] == "pool").map(|x| x["gas"].as_u64().unwrap()))
        .max()
        .unwrap();
    let curve: Vec<Value> = submit_curve
        .iter()
        .filter(|(n, _)| *n == 1 || *n % 32 == 0 || *n == 31 || *n == 32 || *n == 256)
        .map(|(n, g)| json!({ "records_after": n, "pool_receipt_tgas": tgas(*g) }))
        .collect();
    record(
        "RES-1",
        json!({
            "property": "RES-1",
            "result": "pass",
            "state": {
                "metrics": 32, "terms": 64, "recipes": 32, "max_requires": 31, "records": 256,
                "completed": reference.records.iter().filter(|c| c.status == Status::Completed).count(),
                "open": reference.records.iter().filter(|c| !matches!(c.status, Status::Completed | Status::Cancelled)).count(),
                "state_bytes": state_bytes, "storage_usage_bytes": storage_usage, "get_pool_json_bytes": json_len,
                "built_by": "real transactions only", "build_seconds": t0.elapsed().as_secs()
            },
            "worst_pool_receipt_tgas": tgas(worst),
            "worst_margin_to_300_tgas": tgas(TX_GAS_LIMIT - worst),
            "submit_256_pool_receipt_tgas": tgas(submit_max),
            "get_pool_tx_tgas": tgas(get_pool_tx),
            "calls": gas.rows,
            "submit_gas_by_record_count": curve,
        }),
    );
}

// ------------------------------------------- prepaid gas below 300 Tgas

/// One call with `tgas` Tgas prepaid. On success returns the outcome. On
/// failure checks that the call ran out of gas in its first receipt (on
/// `receiver`) and that nothing else happened: no receipt on the other
/// contract, no event, the raw storage of both contracts byte-identical, the
/// pool equal to `reference` and record `id` still `status`. Returns the row.
#[allow(clippy::too_many_arguments)]
async fn attempt(
    worker: &Worker<Sandbox>,
    signer: &Account,
    receiver: &AccountId,
    method: &str,
    args: &Value,
    tgas_prepaid: u64,
    lock: &Contract,
    exec: &Contract,
    reference: &Pool,
    id: u32,
    status: Status,
) -> Result<ExecutionFinalResult, Value> {
    let (pool_raw, exec_raw) = (raw_state(worker, lock.id()).await, raw_state(worker, exec.id()).await);
    let r = tx_gas(signer, receiver, method, args.clone(), tgas_prepaid * TGAS).await;
    if r.is_success() {
        return Ok(r);
    }
    let what = format!("{method} {args} with {tgas_prepaid} Tgas");
    let failures = r.failures();
    assert_eq!(failures.len(), 1, "{what}: {failures:?}");
    let f = failures[0];
    assert_eq!(&f.executor_id, receiver, "{what}: failed on {}", f.executor_id);
    let text = format!("{:?}", r.clone().into_result().unwrap_err());
    assert!(text.contains(OUT_OF_GAS), "{what}: not an out-of-gas failure: {text}");
    assert_eq!(receipts_on(&r, receiver).len(), 1, "{what}: more than one receipt on {receiver}");
    for other in [lock.id(), exec.id()].into_iter().filter(|o| *o != receiver) {
        assert!(receipts_on(&r, other).is_empty(), "{what}: a receipt ran on {other}");
    }
    let logs: Vec<String> = r.logs().iter().map(|l| l.to_string()).collect();
    assert!(logs.is_empty() && events(&logs).is_empty(), "{what}: log or event from a failed call: {logs:?}");
    assert_eq!(raw_state(worker, lock.id()).await, pool_raw, "{what}: pool storage changed");
    assert_eq!(raw_state(worker, exec.id()).await, exec_raw, "{what}: executor storage changed");
    let p = pool(lock).await;
    assert_eq!(&p, reference, "{what}: pool differs from the oracle");
    assert_eq!(p.records[id as usize].status, status, "{what}");
    Err(json!({
        "call": method, "args": args, "prepaid_tgas": tgas_prepaid, "ok": false, "failure": OUT_OF_GAS,
        "failed_receipt_on": receiver, "failed_receipt_burnt_tgas": tgas(f.gas_burnt.as_gas()),
        "receipts_on_other_contract": 0, "events": 0,
        "pool_storage_unchanged": true, "executor_storage_unchanged": true,
        "record_status_after": format!("{status:?}"),
    }))
}

/// The smallest whole-Tgas prepaid gas, counting up from `from`, for which
/// the call succeeds; every smaller amount tried must fail as `attempt`
/// checks (its rows go to `rows`). Returns the minimum and its outcome.
#[allow(clippy::too_many_arguments)]
async fn min_prepaid(
    worker: &Worker<Sandbox>,
    signer: &Account,
    receiver: &AccountId,
    method: &str,
    args: Value,
    from: u64,
    lock: &Contract,
    exec: &Contract,
    reference: &Pool,
    id: u32,
    status: Status,
    rows: &mut Vec<Value>,
) -> (u64, ExecutionFinalResult) {
    let mut g = from;
    loop {
        assert!(g * TGAS <= TX_GAS_LIMIT, "{method} {args}: no success up to 300 Tgas");
        match attempt(worker, signer, receiver, method, &args, g, lock, exec, reference, id, status.clone()).await {
            Ok(r) => {
                eprintln!("RES-1 {method} {args}: smallest whole-Tgas prepaid gas that succeeds: {g}");
                return (g, r);
            }
            Err(row) => rows.push(row),
        }
        g += 1;
    }
}

async fn jobs(exec: &Contract) -> Vec<Value> {
    exec.view("get_jobs").await.unwrap().json().unwrap()
}

/// PROP: RES-1. Prepaid gas below 300 Tgas at the maximum-size state, and
/// the executor at its cap of 256 jobs (every record the pool can hold,
/// dispatched through the pool). Below the minimum, dispatch, reconcile and
/// finish fail with "Exceeded the prepaid gas." and write nothing.
#[tokio::test]
async fn res_1_min_prepaid_gas_and_executor_cap() {
    let t0 = Instant::now();
    let Max { worker, owner, actor, lock, exec, mut reference, a, x, now, expires_at, .. } = build_max(t0).await;
    // The 256th record: 31 Completed, 225 Reserved (recipe 31 x 100 units).
    let req = Request { recipe: 31, units: 100, version: reference.version, expires_at };
    let r = ok(&actor, lock.id(), "submit", json!({ "request": req })).await;
    let v: Value = r.json().unwrap();
    assert_eq!(v["decision"]["allowed"], true, "{v}");
    assert_eq!(reference.submit(&a, req, now).unwrap() as usize, MAX_RECORDS - 1);
    assert_eq!(pool(&lock).await, reference, "at 256 records");
    let reserved: Vec<u32> = reference.records.iter().filter(|c| c.status == Status::Reserved).map(|c| c.id).collect();
    assert_eq!(reserved, (31..256).collect::<Vec<u32>>());
    let both = [(lock.id(), "pool"), (exec.id(), "exec")];
    let mut gas = Gas { rows: vec![] };
    let mut below = vec![];
    let mut minimum = vec![];

    // --- dispatch below 300 Tgas (pool at 256 records, executor at 31 jobs).
    // Record 255: every whole Tgas from 40 up fails until the minimum.
    assert_eq!(jobs(&exec).await.len(), 31, "executor jobs before the dispatch sweep");
    let (ra, rb, rc) = (255u32, 254u32, 253u32);
    let (min_dispatch, r) =
        min_prepaid(&worker, &actor, lock.id(), "dispatch", json!({ "id": ra }), 40, &lock, &exec, &reference, ra, Status::Reserved, &mut below).await;
    assert!(min_dispatch > 40, "dispatch succeeded with 40 Tgas");
    reference.dispatch(&a, ra, now).unwrap();
    reference.acknowledge(ra, true).unwrap();
    assert_eq!(pool(&lock).await, reference, "after dispatch at the minimum");
    let dispatch_burnt = receipts_on(&r, lock.id())[0].gas_burnt.as_gas();
    gas.add(&format!("dispatch #{ra} with {min_dispatch} Tgas prepaid (the minimum)"), &r, &both, Some((1, 30 * TGAS)));
    minimum.push(json!({
        "call": "dispatch", "state": "pool 256 records (225 Reserved), executor 31 jobs", "min_prepaid_tgas": min_dispatch,
        "fails_at_tgas": format!("40..={}", min_dispatch - 1), "static_gas_attached_tgas": "execute 30 + on_result 30",
        "first_receipt_burnt_tgas": tgas(dispatch_burnt),
    }));
    // Record 254: 40 and minimum - 1 fail and change nothing; then a 300
    // Tgas dispatch succeeds.
    let mut amounts = vec![40, min_dispatch - 1];
    amounts.dedup();
    for g in amounts {
        let row = attempt(&worker, &actor, lock.id(), "dispatch", &json!({ "id": rb }), g, &lock, &exec, &reference, rb, Status::Reserved)
            .await
            .expect_err("dispatch below the minimum succeeded on a second record");
        below.push(row);
    }
    let r = ok(&actor, lock.id(), "dispatch", json!({ "id": rb })).await;
    reference.dispatch(&a, rb, now).unwrap();
    reference.acknowledge(rb, true).unwrap();
    assert_eq!(pool(&lock).await, reference, "after the 300 Tgas dispatch");
    let max_burnt = receipts_on(&r, lock.id())[0].gas_burnt.as_gas();
    gas.add(&format!("dispatch #{rb} with 300 Tgas after failed low-gas attempts"), &r, &both, Some((1, 30 * TGAS)));
    // Record 253: exactly the minimum succeeds again.
    let r = tx_gas(&actor, lock.id(), "dispatch", json!({ "id": rc }), min_dispatch * TGAS).await;
    assert!(r.is_success(), "dispatch #{rc} with {min_dispatch} Tgas: {:?}", r.failures());
    reference.dispatch(&a, rc, now).unwrap();
    reference.acknowledge(rc, true).unwrap();
    assert_eq!(pool(&lock).await, reference);
    gas.add(&format!("dispatch #{rc} with {min_dispatch} Tgas prepaid (the minimum, again)"), &r, &both, Some((1, 30 * TGAS)));

    // --- reconcile below 300 Tgas (record 255 is Active; executor at 34
    // jobs, the 31 prerequisites plus 255, 254 and 253).
    assert_eq!(jobs(&exec).await.len(), 34, "executor jobs before the reconcile sweep");
    let (min_reconcile, r) =
        min_prepaid(&worker, &owner, lock.id(), "reconcile", json!({ "id": ra }), 40, &lock, &exec, &reference, ra, Status::Active, &mut below).await;
    assert_eq!(pool(&lock).await, reference, "reconcile of an Active record is a no-op");
    gas.add(&format!("reconcile #{ra} with {min_reconcile} Tgas prepaid (the minimum)"), &r, &both, Some((1, 30 * TGAS)));
    minimum.push(json!({
        "call": "reconcile", "state": "pool 256 records, record Active, executor 34 jobs", "min_prepaid_tgas": min_reconcile,
        "fails_at_tgas": format!("40..={}", min_reconcile - 1), "static_gas_attached_tgas": "status 10 + on_result 30",
        "first_receipt_burnt_tgas": tgas(receipts_on(&r, lock.id())[0].gas_burnt.as_gas()),
    }));

    // --- the executor at its cap: finish 255, 254, 253, then dispatch every
    // other Reserved record (31..=252) and finish each but the last, so the
    // 256th execute finds 255 "completed" jobs.
    for id in [ra, rb, rc] {
        ok(&owner, exec.id(), "finish", json!({ "id": id, "completed": true })).await;
        reference.settle(&x, id, true).unwrap();
    }
    let last = 252u32;
    for id in 31..last {
        ok(&actor, lock.id(), "dispatch", json!({ "id": id })).await;
        reference.dispatch(&a, id, now).unwrap();
        reference.acknowledge(id, true).unwrap();
        ok(&owner, exec.id(), "finish", json!({ "id": id, "completed": true })).await;
        reference.settle(&x, id, true).unwrap();
        if id % 32 == 0 {
            assert_eq!(pool(&lock).await, reference, "at record {id}");
        }
    }
    assert_eq!(pool(&lock).await, reference, "255 jobs");
    let js = jobs(&exec).await;
    assert_eq!(js.len(), 255);
    assert!(js.iter().all(|j| j["status"] == "completed"));
    let exec_state_255 = raw_state(&worker, exec.id()).await.get(b"STATE".as_slice()).map(Vec::len).unwrap();
    eprintln!("255 jobs in {:?}", t0.elapsed());

    // The 256th execute: scans 255 jobs, pushes the 256th.
    let r = ok(&actor, lock.id(), "dispatch", json!({ "id": last })).await;
    reference.dispatch(&a, last, now).unwrap();
    reference.acknowledge(last, true).unwrap();
    assert_eq!(pool(&lock).await, reference);
    gas.add("dispatch at the executor cap (exec.execute: 255 jobs -> 256)", &r, &both, Some((1, 30 * TGAS)));
    let execute_256 = receipts_on(&r, exec.id())[0].gas_burnt.as_gas();
    assert!(execute_256 < 30 * TGAS);
    let js = jobs(&exec).await;
    assert_eq!(js.len(), 256);
    assert_eq!((js[255]["id"].as_u64(), js[255]["status"].as_str()), (Some(last as u64), Some("active")));

    // status at 256 jobs (the job is the last one scanned), through reconcile.
    let r = ok(&owner, lock.id(), "reconcile", json!({ "id": last })).await;
    assert_eq!(pool(&lock).await, reference, "reconcile of an Active record is a no-op");
    gas.add("reconcile at the executor cap (exec.status scans 256 jobs)", &r, &both, Some((1, 30 * TGAS)));
    let status_256 = receipts_on(&r, exec.id())[0].gas_burnt.as_gas();
    assert!(status_256 < 10 * TGAS);

    // finish below 300 Tgas at 256 jobs, on the last job.
    let (min_finish, r) = min_prepaid(
        &worker, &owner, exec.id(), "finish", json!({ "id": last, "completed": true }), 40, &lock, &exec, &reference, last, Status::Active, &mut below,
    )
    .await;
    reference.settle(&x, last, true).unwrap();
    assert_eq!(pool(&lock).await, reference, "after finish at the minimum");
    let finish_on = [(exec.id(), "exec"), (lock.id(), "pool")];
    gas.add(&format!("finish at the executor cap with {min_finish} Tgas prepaid (the minimum) -> notify settle(true) [40 Tgas]"), &r, &finish_on, Some((1, 40 * TGAS)));
    let finish_256 = receipts_on(&r, exec.id())[0].gas_burnt.as_gas();
    minimum.push(json!({
        "call": "finish (executor)", "state": "executor 256 jobs (last job), pool 256 records", "min_prepaid_tgas": min_finish,
        "fails_at_tgas": format!("40..={}", min_finish - 1), "static_gas_attached_tgas": "notify (pool.settle) 40",
        "first_receipt_burnt_tgas": tgas(finish_256),
    }));
    let js = jobs(&exec).await;
    assert!(js.len() == 256 && js.iter().all(|j| j["status"] == "completed"));
    let exec_state_256 = raw_state(&worker, exec.id()).await.get(b"STATE".as_slice()).map(Vec::len).unwrap();
    let exec_storage = exec.view_account().await.unwrap().storage_usage;

    // At the cap a new job is refused ("full"), and nothing is written.
    let raw = raw_state(&worker, exec.id()).await;
    let full = fails_containing(&owner, exec.id(), "confirm_not_executed", json!({ "id": 999, "recipe": 31, "units": 100 }), "full").await;
    assert_eq!(raw_state(&worker, exec.id()).await, raw);
    assert!(reference.records.iter().all(|c| c.status == Status::Completed));
    assert_eq!(pool(&lock).await, reference, "final");

    let table: Vec<String> = minimum
        .iter()
        .map(|m| format!("{:<18} min {:>3} Tgas, fails at {:>8}, first receipt {:>5} Tgas, {}", m["call"].as_str().unwrap(), m["min_prepaid_tgas"], m["fails_at_tgas"].as_str().unwrap(), m["first_receipt_burnt_tgas"], m["state"].as_str().unwrap()))
        .collect();
    eprintln!("RES-1 minimum prepaid gas (whole Tgas):\n{}", table.join("\n"));
    for row in &gas.rows {
        let rs: Vec<String> = row["receipts"].as_array().unwrap().iter().map(|r| format!("{} {}", r["on"].as_str().unwrap(), r["gas_tgas"])).collect();
        eprintln!("RES-1 {:<90} tx {:>6} Tgas | {}", row["call"].as_str().unwrap(), row["tx_total_tgas"], rs.join(", "));
    }
    record(
        "RES-1-gas",
        json!({
            "property": "RES-1",
            "test": "res_1_min_prepaid_gas_and_executor_cap",
            "result": "pass",
            "method": "whole-Tgas sweep from 40 Tgas up; every amount below the minimum fails with the runtime's out-of-gas error in its first receipt, runs no other receipt, emits no event, and leaves both contracts' raw storage byte-identical and the pool equal to the oracle",
            "minimum_prepaid_gas": minimum,
            "dispatch_pool_receipt_burnt_tgas": { "at_minimum_prepaid": tgas(dispatch_burnt), "at_300_tgas": tgas(max_burnt) },
            "executor_cap": {
                "jobs": 256, "state_bytes_at_255_jobs": exec_state_255, "state_bytes_at_256_jobs_all_completed": exec_state_256,
                "storage_usage_bytes": exec_storage,
                "execute_256th_tgas": tgas(execute_256), "execute_budget_tgas": 30,
                "status_at_256_tgas": tgas(status_256), "status_budget_tgas": 10,
                "finish_last_job_at_256_tgas": tgas(finish_256),
                "confirm_not_executed_at_cap": { "result": "fails", "observed_panic": full },
            },
            "below_minimum_attempts": below,
            "calls": gas.rows,
            "build_seconds": t0.elapsed().as_secs(),
        }),
    );
}
