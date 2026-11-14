//! SH-8: differential test of the shell against the pool-core reference,
//! with the contract state reloaded (Borsh) on every call.
//!
//! Host path: STORE_DIFF_SEQS (default 2,000) sequences of STORE_DIFF_STEPS
//! (default 40) random calls, from the five fixtures, the F-1 wedge config,
//! `open_config` and random small configurations (the conformance generator's
//! distribution). Every call runs on a contract freshly `state_read` from
//! storage and is compared with `pool_core::Pool` (the same pinned crate):
//! return value, panic message, events, outgoing receipts, and the stored
//! bytes (= Borsh of the core's pool); views (get_pool, get_commitments,
//! preview) are compared after every call.
//!
//! Wasm path: WASM_DIFF_SEQS (default 300) sequences per build through the
//! real wasm (JSON in and out, near-sdk wrappers), same comparisons, JSON
//! views every few steps.
//!
//! Coverage: every error the generator can reach is required to occur, so a
//! generator that stopped exercising a guard fails the test.
//!
//! The reference (`core_step`) fixes, on every call, the caller as the
//! predecessor with 15% relayed calls (SH-1), the on_result mapping (SH-3),
//! the submit decision (SH-4), errors as panics that change nothing (SH-5),
//! and the dispatch and reconcile receipts (SH-6, SH-7). The views include
//! `preview`, compared with the core's (shell half of RD-PREVIEW).
//!
// PROP: SH-8 SH-1 SH-3 SH-4 SH-5 SH-6 SH-7 SH-9 RD-PREVIEW

mod common;
use common::*;
use near_sdk::serde_json::{self, json, Value};
use pool_core::{Config, Pool};
use std::collections::BTreeMap;

type Coverage = BTreeMap<String, u64>;

fn config_for(seq: u64, rng: &mut Rng) -> (String, Config) {
    match seq % 10 {
        0 => {
            let name = pool_core::fixtures::NAMES[(seq / 10 % 5) as usize];
            (name.to_string(), pool_core::fixtures::config(name).expect("fixture"))
        }
        1 => ("wedge".into(), wedge_config()),
        2 => ("open".into(), open_config()),
        _ => ("random".into(), random_config(rng)),
    }
}

/// What a call did, for coverage: method and result (error, submit reason,
/// on_result outcome/error).
fn label(op: &Op, r: &Result<Value, Fail>, events: &[Value]) -> String {
    let m = op.method();
    match (op, r) {
        (_, Err(f)) => format!("{m}:Err({})", f.msg()),
        (Op::Submit { .. }, Ok(v)) => format!("{m}:{}", v["decision"]["reason"].as_str().unwrap()),
        (Op::OnResult { result, .. }, Ok(_)) => {
            let class = match result.as_deref() {
                Some(s @ ("completed" | "cancelled" | "active" | "unknown")) => s,
                Some(_) => "other",
                None => "failed",
            };
            let err = &events[0]["data"][0]["error"];
            format!("{m}:{class}:{}", err.as_str().unwrap_or("ok"))
        }
        (_, Ok(_)) => format!("{m}:Ok"),
    }
}

fn run_host(seq: u64, steps: u64, seed: u64, cov: &mut Coverage) {
    let mut rng = Rng::new(seed.wrapping_mul(1_000_003).wrapping_add(seq));
    let (name, cfg) = config_for(seq, &mut rng);
    let mut now = 100 + rng.below(1_000);
    let mut storage = deploy(cfg.clone(), now);
    let mut pool = Pool::new(cfg, now).unwrap();
    assert_eq!(storage, storage_of(&pool), "seq {seq}: new");
    for i in 0..steps {
        now += rng.below(4);
        let ts = now * 1_000_000_000 + rng.below(1_000_000_000);
        let (ctx, op) = random_step(&mut rng, &pool, ts);
        let what = format!("seed {seed} seq {seq} ({name}) step {i}: {op:?} by {} (signer {}) at {ts}", ctx.predecessor, ctx.signer);
        let out = step(storage, &mut pool, &ctx, &op, &what);
        storage = out.storage;
        // The stored bytes decode to the core's pool (Borsh round trip).
        assert_eq!(pool_of(&storage), pool, "{what}: reload");
        let events: Vec<Value> = out.logs.iter().map(|l| parse_event(l)).collect();
        *cov.entry(label(&op, &out.result, &events)).or_default() += 1;
        check_views(&storage, &pool, &mut rng, now, &what);
    }
}

/// Errors and outcomes the generator reaches; each must occur at least once
/// over the default run (a vacuity guard on the generator).
const REQUIRED_HOST: &[&str] = &[
    "submit:Allowed",
    "submit:Paused",
    "submit:Stale",
    "submit:Expired",
    "submit:SnapshotExpired",
    "submit:InvalidRecipe",
    "submit:Unauthorized",
    "submit:InvalidUnits",
    "submit:Prerequisite",
    "submit:Bounds",
    "submit:Energy",
    "dispatch:Ok",
    "dispatch:Err(NotFound)",
    "dispatch:Err(Unauthorized)",
    "dispatch:Err(Paused)",
    "dispatch:Err(InvalidState)",
    "dispatch:Err(Expired)",
    "dispatch:Err(SnapshotExpired)",
    "reconcile:Ok",
    "reconcile:Err(NotFound)",
    "reconcile:Err(InvalidState)",
    "on_result:active:ok",
    "on_result:completed:ok",
    "on_result:cancelled:ok",
    "on_result:unknown:ok",
    "on_result:other:ok",
    "on_result:failed:ok",
    "on_result:completed:InvalidState",
    "on_result:cancelled:InvalidState",
    "on_result:Err(NotFound)",
    "settle:Ok",
    "settle:Err(NotFound)",
    "settle:Err(Unauthorized)",
    "settle:Err(InvalidState)",
    "settle:Err(Bounds)",
    "cancel:Ok",
    "cancel:Err(NotFound)",
    "cancel:Err(Unauthorized)",
    "cancel:Err(Pending)",
    "cancel:Err(Bounds)",
    "set_paused:Ok",
    "set_paused:Err(Unauthorized)",
    "observe:Ok",
    "observe:Err(Unauthorized)",
    "observe:Err(Pending)",
    "observe:Err(Bounds)",
];

fn print_coverage(title: &str, cov: &Coverage) {
    let total: u64 = cov.values().sum();
    println!("{title}: {total} calls");
    for (k, v) in cov {
        println!("  {k:<40} {v}");
    }
}

// PROP: SH-8 SH-1 SH-3 SH-4 SH-5 SH-6 SH-7 SH-9 RD-PREVIEW
#[test]
fn sh8_store_diff_host() {
    let seqs = env_u64("STORE_DIFF_SEQS", 2_000);
    let steps = env_u64("STORE_DIFF_STEPS", 40);
    let seed = env_u64("STORE_DIFF_SEED", 1);
    let shards = 4;
    let covs: Vec<Coverage> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..shards)
            .map(|k| {
                s.spawn(move || {
                    quiet_expected_panics();
                    let mut cov = Coverage::new();
                    for seq in (k..seqs).step_by(shards as usize) {
                        run_host(seq, steps, seed, &mut cov);
                    }
                    cov
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
    });
    let mut cov = Coverage::new();
    for c in covs {
        for (k, v) in c {
            *cov.entry(k).or_default() += v;
        }
    }
    print_coverage(&format!("SH-8 host: {seqs} x {steps}, seed {seed}"), &cov);
    assert_eq!(cov.values().sum::<u64>(), seqs * steps);
    if seqs >= 2_000 && steps >= 40 {
        let missing: Vec<_> = REQUIRED_HOST.iter().filter(|k| !cov.contains_key(**k)).collect();
        assert!(missing.is_empty(), "never reached: {missing:?}");
    }
}

/// The wasm's JSON views equal the core's reads.
fn wasm_views(b: Build, storage: &Storage, pool: &Pool, rng: &mut Rng, now: u64, what: &str) {
    let w = wasm(b, "pool_contract");
    let call = |method: &str, args: Value| {
        let out = wasm_call(w, &Ctx::by(Z, now), storage.clone(), vec![], method, &serde_json::to_vec(&args).unwrap());
        assert!(out.logs.is_empty() && out.receipts.is_empty(), "{what}: view {method}");
        assert_eq!(&out.storage, storage, "{what}: view {method} changed state");
        out.json()
    };
    assert_eq!(call("get_pool", json!({})), serde_json::to_value(pool).unwrap(), "{what}: get_pool");
    let n = pool.records.len() as u64;
    let (from, limit) = (rng.below(n + 2) as u32, rng.below(60) as u32);
    let want: Vec<Value> = expected_page(pool, from, limit).iter().map(commitment_json).collect();
    assert_eq!(call("get_commitments", json!({ "from": from, "limit": limit })), json!(want), "{what}: page");
    let accts = accounts_of(&pool.config);
    let actor = rng.pick(&accts).clone();
    let req = random_request(rng, pool, now);
    let d = pool.preview(&actor, &req, now);
    assert_eq!(
        call("preview", json!({ "actor": actor, "request": request_json(&req) })),
        decision_json(&d),
        "{what}: preview"
    );
}

fn run_wasm(b: Build, seq: u64, steps: u64, seed: u64, cov: &mut Coverage) {
    let mut rng = Rng::new(seed.wrapping_mul(7_000_003).wrapping_add(seq) ^ 0x5eed);
    let (name, cfg) = config_for(seq, &mut rng);
    let mut now = 100 + rng.below(1_000);
    let mut storage = wasm_deploy(b, &cfg, now);
    let mut pool = Pool::new(cfg, now).unwrap();
    assert_eq!(storage, storage_of(&pool), "seq {seq}: new");
    for i in 0..steps {
        now += rng.below(4);
        let ts = now * 1_000_000_000 + rng.below(1_000_000_000);
        let (ctx, op) = random_step(&mut rng, &pool, ts);
        let what = format!("{b:?} seed {seed} seq {seq} ({name}) step {i}: {op:?} by {} (signer {}) at {ts}", ctx.predecessor, ctx.signer);
        let exp = core_step(&mut pool.clone(), &ctx, &op);
        let out = wasm_diff_step(b, storage, &mut pool, &ctx, &op, &what);
        storage = out.storage.clone();
        assert_eq!(pool_of(&storage), pool, "{what}: reload");
        let events: Vec<Value> = out.logs.iter().map(|l| parse_event(l)).collect();
        *cov.entry(label(&op, &exp.result, &events)).or_default() += 1;
        if i % 4 == 3 {
            wasm_views(b, &storage, &pool, &mut rng, now, &what);
        }
    }
}

// PROP: SH-8 SH-1 SH-3 SH-4 SH-5 SH-6 SH-7 SH-9 RD-PREVIEW
#[test]
fn sh8_store_diff_wasm() {
    let seqs = env_u64("WASM_DIFF_SEQS", 300);
    let steps = env_u64("STORE_DIFF_STEPS", 40);
    let seed = env_u64("STORE_DIFF_SEED", 1);
    // One thread per build (256 MiB stacks: wasmi in a debug build).
    let hs: Vec<_> = Build::all()
        .into_iter()
        .map(|b| {
            std::thread::Builder::new()
                .stack_size(256 << 20)
                .spawn(move || {
                    quiet_expected_panics();
                    let mut cov = Coverage::new();
                    for seq in 0..seqs {
                        run_wasm(b, seq, steps, seed, &mut cov);
                    }
                    (b, cov)
                })
                .unwrap()
        })
        .collect();
    for h in hs {
        let (b, cov) = h.join().unwrap_or_else(|p| std::panic::resume_unwind(p));
        print_coverage(&format!("SH-8 wasm {b:?}: {seqs} x {steps}, seed {seed}"), &cov);
        assert_eq!(cov.values().sum::<u64>(), seqs * steps);
        if seqs >= 150 {
            for k in ["submit:Allowed", "dispatch:Ok", "reconcile:Ok", "on_result:failed:ok", "settle:Ok", "settle:Err(Unauthorized)", "observe:Ok", "cancel:Err(Pending)"] {
                assert!(cov.contains_key(k), "{b:?}: never reached {k}");
            }
        }
    }
}
