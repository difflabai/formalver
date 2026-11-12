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
#![allow(unused_must_use)]
mod common;

use common::*;
use near_workspaces::result::ExecutionFinalResult;
use near_workspaces::AccountId;
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

/// PROP: RES-1
#[tokio::test]
async fn res_1_gas_at_max_state() {
    let t0 = Instant::now();
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
    let pool_on = [(lock.id(), "pool")];
    let mut gas = Gas { rows: vec![] };
    gas.add("new (max config)", &r_new, &pool_on, None);
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
