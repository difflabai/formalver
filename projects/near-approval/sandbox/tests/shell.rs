//! M6 shell properties that only the real runtime shows (strategy.md 5.7,
//! 5.8): SH-9 (init), SH-10 (deposits on all 16 exports at the pin), RES-1
//! (measured storage deltas) and RES-3 (a full page of maximum-size proofs).

mod common;

use common::*;
use near_workspaces::types::{Gas, KeyType, NearToken};
use near_workspaces::{Account, Contract};
use serde_json::{json, Value};

/// The 16 `#[near]` methods at the pin (F-15: the SH-10/SH-11 rows said 13).
const METHODS: [&str; 16] = [
    "add_agent",
    "add_approver",
    "approve",
    "get_approval",
    "get_approval_count",
    "get_approvals",
    "get_owner",
    "get_principal",
    "get_rejection",
    "get_request",
    "get_request_count",
    "get_revocation",
    "new",
    "reject",
    "request_action",
    "revoke_key",
];

/// Well-formed arguments for each method.
fn args(method: &str, account: &Account) -> Value {
    match method {
        "new" => json!({ "owner_id": account.id() }),
        "add_agent" | "add_approver" => json!({ "account_id": account.id(), "public_key": pk(account) }),
        "revoke_key" | "get_principal" => json!({ "public_key": pk(account) }),
        "request_action" => json!({ "action": "x" }),
        "approve" => json!({ "request_id": 0, "action": "x" }),
        "reject" | "get_request" | "get_approval" | "get_rejection" => json!({ "request_id": 0 }),
        "get_revocation" => json!({ "registration_id": 0 }),
        _ => json!({}),
    }
}

fn is_view(m: &str) -> bool {
    m.starts_with("get_")
}

// PROP: SH-9
#[tokio::test]
async fn sh9_init() {
    let worker = sandbox().await;
    let c_account = subaccount(&worker, "approvals", 20).await;
    let contract = c_account.deploy(&wasm()).await.unwrap().into_result().unwrap();
    let stranger = subaccount(&worker, "stranger", 10).await;
    let owner = subaccount(&worker, "owner", 10).await;

    // `new` only from C (#[private]).
    assert_fails_with(
        stranger.call(contract.id(), "new").args_json(args("new", &owner)).transact().await,
        "Method new is private",
    );
    // Every other method fails before init (PanicOnDefault), views included.
    for m in METHODS.iter().filter(|m| **m != "new") {
        if is_view(m) {
            let e = contract.view(m).args_json(args(m, &owner)).await.unwrap_err();
            assert!(format!("{e:?}").contains("The contract is not initialized"), "{m}: {e:?}");
        } else {
            assert_fails_with(
                stranger.call(contract.id(), m).args_json(args(m, &owner)).max_gas().transact().await,
                "The contract is not initialized",
            );
        }
    }
    must(contract.call("new").args_json(args("new", &owner)).transact().await);
    // Post-init state is Init(owner).
    let init = json!({
        "get_owner": owner.id(),
        "get_request_count": 0,
        "get_approval_count": 0,
        "get_request": null,
        "get_approval": null,
        "get_rejection": null,
        "get_revocation": null,
        "get_approvals": [],
        "get_principal": null,
    });
    for m in METHODS.iter().filter(|m| is_view(m)) {
        assert_eq!(view(&contract, m, args(m, &owner)).await, init[*m], "{m} after init");
    }
    // Once only, even from C.
    assert_fails_with(
        contract.call("new").args_json(args("new", &stranger)).transact().await,
        "The contract has already been initialized",
    );
    assert_eq!(view(&contract, "get_owner", json!({})).await, json!(owner.id()));
}

// PROP: SH-10
#[tokio::test]
async fn sh10_deposits() {
    // The export surface first: exactly the 16 methods plus near-sdk/cargo-near
    // metadata (SH-11's list, repeated on the wasm under test).
    let mut exports = function_exports(&wasm());
    exports.retain(|e| e != "contract_source_metadata" && e != "__contract_abi");
    exports.sort();
    assert_eq!(exports, METHODS.to_vec(), "function exports at the pin");

    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id().clone();
    // Full-access keys: function-call keys can't attach deposits (RT-FCKEY).
    for (method, account) in [("add_agent", &s.agent_account), ("add_approver", &s.approver_account)] {
        must(s.owner
            .call(&c, method)
            .args_json(json!({ "account_id": account.id(), "public_key": pk(account) }))
            .transact()
            .await);
    }
    let before = s.snapshot().await;
    let yocto = NearToken::from_yoctonear(1);
    let mut rec = serde_json::Map::new();
    for m in METHODS {
        // A caller the method would otherwise accept.
        let (caller, a): (&Account, Value) = match m {
            "add_agent" | "add_approver" | "revoke_key" => (&s.owner, args(m, &s.owner)),
            "request_action" => (&s.agent_account, json!({ "action": "x" })),
            "approve" | "reject" => (&s.approver_account, args(m, &s.owner)),
            _ => (&s.owner, args(m, &s.owner)),
        };
        if m == "new" {
            continue;
        }
        let r = caller.call(&c, m).args_json(a).deposit(yocto).max_gas().transact().await.unwrap();
        let outcome = if r.is_success() {
            "success".to_string()
        } else {
            let t = format!("{:?}", r.clone().into_result().unwrap_err());
            match t.split_once("ExecutionError(\"") {
                Some((_, rest)) => rest.split("\")").next().unwrap().to_string(),
                None => t,
            }
        };
        if !is_view(m) {
            assert_eq!(outcome, format!("Smart contract panicked: Method {m} doesn't accept deposit"), "{m}");
        }
        rec.insert(m.into(), json!(outcome));
    }
    // new on a fresh, uninitialized deployment, called by C itself.
    let fresh = subaccount(&s.worker, "fresh", 20).await;
    let fresh: Contract = fresh.deploy(&wasm()).await.unwrap().into_result().unwrap();
    let (text, _) = executed_failure(fresh.call("new").args_json(args("new", &s.owner)).deposit(yocto).transact().await);
    assert!(text.contains("Method new doesn't accept deposit"), "{text}");
    rec.insert("new".into(), json!("Smart contract panicked: Method new doesn't accept deposit"));
    // contract_source_metadata is a cargo-near/near-sdk export, not a #[near] method.
    let r = s.owner.call(&c, "contract_source_metadata").deposit(yocto).transact().await.unwrap();
    rec.insert("contract_source_metadata".into(), json!(if r.is_success() { "success" } else { "failure" }));
    assert_eq!(s.snapshot().await, before, "deposit calls changed state");
    record("SH-10", Value::Object(rec));
}

// PROP: RES-1
#[tokio::test]
async fn res1_storage_deltas() {
    let mut rec = serde_json::Map::new();
    for (label, long, kt) in [("short_ed25519", false, KeyType::ED25519), ("long64_secp256k1", true, KeyType::SECP256K1)] {
        let s = setup(long, kt).await;
        let c = s.contract.id().clone();
        let usage = || async { s.contract.view_account().await.unwrap().storage_usage };
        let mut d = serde_json::Map::new();
        // One more agent key (an access key on the agent account, not on C).
        let extra = function_call_key(&s.worker, &s.agent_account, &c, &["request_action"], kt).await;
        let mut last = usage().await;
        let mut step = |name: &str, now: u64, d: &mut serde_json::Map<String, Value>| -> i64 {
            let delta = now as i64 - last as i64;
            d.insert(name.into(), json!(delta));
            last = now;
            delta
        };
        must(s.owner
            .call(&c, "add_agent")
            .args_json(json!({ "account_id": s.agent.id(), "public_key": pk(&extra) }))
            .transact()
            .await);
        step("add_agent", usage().await, &mut d);
        let id1: u64 = ok(s.request("a").await).json().unwrap();
        step("request_action(1 byte)", usage().await, &mut d);
        let max = "\u{1}".repeat(MAX_ACTION_LEN);
        let id2: u64 = ok(s.request(&max).await).json().unwrap();
        step("request_action(2048 bytes)", usage().await, &mut d);
        must(s.approve(id1, "a").await);
        step("approve", usage().await, &mut d);
        must(s.approver.call(&c, "reject").args_json(json!({ "request_id": id2 })).max_gas().transact().await);
        step("reject", usage().await, &mut d);
        // Failures add nothing.
        for (what, r) in [
            ("fail: request_action('')", s.request("").await),
            ("fail: approve(missing)", s.approve(99, "a").await),
            ("fail: add_agent(not owner)", s.agent_account.call(&c, "add_agent")
                .args_json(json!({ "account_id": s.agent.id(), "public_key": pk(&s.agent_account) })).transact().await),
        ] {
            let _ = executed_failure(r);
            let now = usage().await;
            assert_eq!(step(what, now, &mut d), 0, "{what} changed storage");
        }
        must(s.owner.call(&c, "revoke_key").args_json(json!({ "public_key": pk(&extra) })).transact().await);
        step("revoke_key", usage().await, &mut d);
        let req1 = d["request_action(1 byte)"].as_i64().unwrap();
        let req_max = d["request_action(2048 bytes)"].as_i64().unwrap();
        // Borsh stores the action as u32 length + bytes, so the record grows
        // byte for byte.
        assert_eq!(req_max - req1, MAX_ACTION_LEN as i64 - 1);
        // RES-1's bound: 16 maximum-size requests per agent key with no approver.
        let lockable = 16 * req_max as u128 * YOCTO_PER_BYTE;
        d.insert("16 x B_req(max) in NEAR".into(), json!(format!("{:.4}", lockable as f64 / 1e24)));
        rec.insert(label.into(), Value::Object(d));
    }
    record("RES-1", Value::Object(rec));
}

// PROP: RES-3 RES-2
#[tokio::test]
async fn res3_full_page_of_max_proofs() {
    // 64-character accounts, secp256k1 keys, 2048 control characters: the
    // largest proof JSON (each byte escapes to six).
    let s = setup(true, KeyType::SECP256K1).await;
    let c = s.contract.id().clone();
    let action = "\u{1}".repeat(MAX_ACTION_LEN);
    let (mut req_log, mut appr_log) = (0, 0);
    for _ in 0..100 {
        let r = ok(s.request(&action).await);
        req_log = req_log.max(max_receipt_log_len(&r));
        let id: u64 = r.json().unwrap();
        let a = ok(s.approve(id, &action).await);
        appr_log = appr_log.max(max_receipt_log_len(&a));
    }
    assert!(req_log <= MAX_TOTAL_LOG_LEN && appr_log <= MAX_TOTAL_LOG_LEN);
    // As a view (the node's view gas cap applies) ...
    let raw = s
        .contract
        .view("get_approvals")
        .args_json(json!({ "from_index": 0, "limit": 100 }))
        .await
        .expect("get_approvals(0,100) as a view")
        .result;
    let page: Vec<Value> = serde_json::from_slice(&raw).unwrap();
    assert_eq!(page.len(), 100);
    assert!(page.iter().all(|p| p["action"] == json!(action)));
    assert!(raw.len() < 4 * 1024 * 1024, "{} bytes", raw.len());
    // ... and as a transaction, to measure gas (views don't report it).
    let tx = ok(s
        .owner
        .call(&c, "get_approvals")
        .args_json(json!({ "from_index": 0, "limit": 100 }))
        .gas(Gas::from_tgas(300))
        .transact()
        .await);
    let gas = receipts_on(&tx, &c)[0].gas_burnt;
    assert_eq!(tx.raw_bytes().unwrap(), raw, "tx and view returned different pages");
    assert!(gas < Gas::from_tgas(300));
    record(
        "RES-3",
        json!({
            "proofs": 100,
            "return_bytes": raw.len(),
            "return_limit_bytes": 4 * 1024 * 1024,
            "gas_burnt_tgas": (gas.as_gas() as f64 / 1e12 * 10.0).round() / 10.0,
            "gas_limit_tgas": 300,
            "view_succeeded": true,
            "RES-2 max receipt log bytes": { "approval_requested": req_log, "action_approved": appr_log, "limit": MAX_TOTAL_LOG_LEN },
        }),
    );
}
