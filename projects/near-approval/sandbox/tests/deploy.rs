//! M7 in the sandbox: `deploy-checks/check_deployment.sh sandbox` against a
//! local near-sandbox (strategy.md 5.10), and RT-RESET (5.9).
//!
//! - The DEP-1 lock batch (deploy + new + delete every full-access key of C,
//!   one transaction), one agent and one approver with DEP-1.4
//!   function-call keys, one proof: every check passes (DEP-1.3 is a WARN:
//!   the sandbox owner is a plain account, `allow_plain_owner`).
//!   The VER-8 observations the script writes go to
//!   `verifier_rules.pl:ver8_ok/4`, which accepts them.
//! - Negative cases each make it fail: a full-access key left on C, a wrong
//!   expected code hash, a full-access agent key (DEP-1.4, and VER-8 per
//!   proof, in the script and in Prolog).
//! - RT-RESET: delete and recreate an unlocked C. Counters reset; VER-3
//!   flags the DeleteAccount; VER-6 (Prolog) flags the counter decrease.
//!
//! No public network is touched: the script gets the sandbox's RPC URL and
//! accounts through CHECK_* overrides of [deployment.sandbox].

mod common;

use common::*;
use near_workspaces::network::Sandbox;
use near_workspaces::operations::Function;
use near_workspaces::types::{AccessKey, KeyType, NearToken};
use near_workspaces::{Account, AccountId, Worker};
use serde_json::{json, Value};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Deployed {
    id: AccountId,
    lock_tx: String,
    /// C's own key, when the deployment kept it (negative and RT-RESET cases).
    key: Option<Account>,
}

/// Creates `name` and deploys in one transaction signed by C:
/// DeployContract + new(owner) [+ DeleteKey(C's only key)].
async fn deploy(worker: &Worker<Sandbox>, name: &str, owner: &AccountId, lock: bool) -> Deployed {
    let c = subaccount(worker, name, 30).await;
    let mut tx = c
        .batch(c.id())
        .deploy(&wasm())
        .call(Function::new("new").args_json(json!({ "owner_id": owner })));
    if lock {
        tx = tx.delete_key(pk(&c));
    }
    let outcome = ok(tx.transact().await);
    Deployed {
        id: c.id().clone(),
        lock_tx: outcome.outcome().transaction_hash.to_string(),
        key: if lock { None } else { Some(c) },
    }
}

struct Parties {
    /// The agent account signing with its full-access (creation) key.
    agent_account: Account,
    #[allow(dead_code)]
    agent: Account,
    approver: Account,
}

/// Registers one agent and one approver with DEP-1.4 keys (receiver C,
/// [request_action] / [approve, reject], finite allowance) and makes one proof.
async fn register_and_prove(worker: &Worker<Sandbox>, owner: &Account, c: &AccountId, tag: &str) -> Parties {
    let agent_acc = subaccount(worker, &format!("agent{tag}"), 10).await;
    let approver_acc = subaccount(worker, &format!("approver{tag}"), 10).await;
    let allowance = Some(NearToken::from_near(5));
    let agent = add_key(worker, &agent_acc, AccessKey::function_call_access(c, &["request_action"], allowance), KeyType::ED25519).await;
    let approver = add_key(worker, &approver_acc, AccessKey::function_call_access(c, &["approve", "reject"], allowance), KeyType::ED25519).await;
    for (m, a) in [("add_agent", &agent), ("add_approver", &approver)] {
        must(owner.call(c, m).args_json(json!({ "account_id": a.id(), "public_key": pk(a) })).transact().await);
    }
    let id: u64 = ok(agent.call(c, "request_action").args_json(json!({ "action": "ship it" })).max_gas().transact().await)
        .json()
        .unwrap();
    must(approver.call(c, "approve").args_json(json!({ "request_id": id, "action": "ship it" })).max_gas().transact().await);
    Parties { agent_account: agent_acc, agent, approver }
}

struct Report {
    code: i32,
    verdicts: Vec<(String, String, String)>,
    facts: String,
}

impl Report {
    fn verdict(&self, id: &str) -> &str {
        &self.verdicts.iter().find(|v| v.0 == id).unwrap_or_else(|| panic!("no {id} in {:?}", self.verdicts)).1
    }
    fn detail(&self, id: &str) -> &str {
        &self.verdicts.iter().find(|v| v.0 == id).unwrap().2
    }
}

fn check(worker: &Worker<Sandbox>, d: &Deployed, overrides: &[(&str, String)]) -> Report {
    let code = wasm();
    // One directory per call: the tests in this file run on parallel threads
    // of one process and deploy under the same account name, so a directory
    // keyed by pid and account alone let one test read the other's out.json.
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let n = CALLS.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("m7-check-{}-{}-{n}", std::process::id(), d.id));
    std::fs::create_dir_all(&dir).unwrap();
    let (facts, out_json) = (dir.join("facts.pl"), dir.join("out.json"));
    let script = sandbox_dir().join("../deploy-checks/check_deployment.sh");
    let mut cmd = Command::new("bash");
    cmd.arg(&script)
        .arg("sandbox")
        .arg("--facts")
        .arg(&facts)
        .arg("--json")
        .arg(&out_json)
        .env("CHECK_RPC_URL", worker.rpc_addr())
        .env("CHECK_CONTRACT_ACCOUNT", d.id.as_str())
        .env("CHECK_EXPECTED_CODE_HASH", code_hash_b58(&code))
        .env("CHECK_WASM_SHA256", hex(&sha256(&code)))
        .env("CHECK_LOCK_TX_HASH", &d.lock_tx)
        .env("CHECK_LOCK_TX_SIGNER", d.id.as_str())
        .env("APPROVAL_WASM", wasm_path());
    for (k, v) in overrides {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("run check_deployment.sh");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    eprintln!("--- check_deployment.sh sandbox ({})\n{stdout}{}", d.id, String::from_utf8_lossy(&out.stderr));
    let code = out.status.code().unwrap_or(-1);
    assert!(code == 0 || code == 1, "configuration error: {stdout}");
    let rows: Vec<Value> = serde_json::from_str(&std::fs::read_to_string(&out_json).unwrap()).unwrap();
    Report {
        code,
        verdicts: rows
            .iter()
            .map(|r| (r["id"].as_str().unwrap().into(), r["verdict"].as_str().unwrap().into(), r["detail"].as_str().unwrap().into()))
            .collect(),
        facts: std::fs::read_to_string(&facts).unwrap_or_default(),
    }
}

/// verifier_rules.pl's VER-8 verdict on each proof the script observed.
fn ver8_prolog(facts: &str) -> Vec<String> {
    let out = prolog(
        facts,
        "forall(ver8_obs(C, P, A, K), \
         ( arg(2, P, I), (verifier_rules:ver8_ok(C, P, A, K) -> format(\"~d ok~n\", [I]) ; format(\"~d reject~n\", [I])) ))",
    );
    out.lines().map(str::to_string).collect()
}

// PROP: DEP-1 VER-2 VER-3 VER-8
#[tokio::test]
async fn dep1_check_deployment_in_sandbox() {
    let worker = sandbox().await;
    let owner = subaccount(&worker, "owner", 10).await;
    let mut rec = serde_json::Map::new();
    let summary = |r: &Report| -> Value {
        json!({ "exit": r.code, "verdicts": r.verdicts.iter().map(|v| format!("{} {}", v.1, v.0)).collect::<Vec<_>>() })
    };

    // 1. Locked deployment, DEP-1.4 keys, one proof: passes.
    let good = deploy(&worker, "approvals", owner.id(), true).await;
    let p = register_and_prove(&worker, &owner, &good.id, "").await;
    let r = check(&worker, &good, &[]);
    for id in ["DEP-1.1", "DEP-1.2", "DEP-1.4", "DEP-1.5", "VER-2", "VER-3", "VER-8"] {
        assert_eq!(r.verdict(id), "PASS", "{id}: {}", r.detail(id));
    }
    assert_eq!(r.verdict("DEP-1.3"), "WARN", "sandbox owner is a plain account");
    assert_eq!(r.code, 0);
    assert_eq!(ver8_prolog(&r.facts), ["0 ok"], "verifier_rules VER-8 on the sandbox proof");
    rec.insert("locked_fc_keys".into(), summary(&r));

    // 2. Wrong expected code hash (the relay's): DEP-1.1 and VER-2 fail.
    let other = res("relay");
    let r = check(
        &worker,
        &good,
        &[
            ("CHECK_EXPECTED_CODE_HASH", code_hash_b58(&other)),
            ("CHECK_WASM_SHA256", hex(&sha256(&other))),
            ("APPROVAL_WASM", sandbox_dir().join("res/wasm/relay.wasm").display().to_string()),
        ],
    );
    assert_eq!(r.code, 1);
    for id in ["DEP-1.1", "DEP-1.2", "VER-2"] {
        assert_eq!(r.verdict(id), "FAIL", "{id}");
    }
    rec.insert("wrong_code_hash".into(), summary(&r));

    // 3. A full-access agent key, used for a proof: DEP-1.4 and VER-8 fail,
    // in the script and in verifier_rules.pl.
    must(owner
        .call(&good.id, "add_agent")
        .args_json(json!({ "account_id": p.agent_account.id(), "public_key": pk(&p.agent_account) }))
        .transact()
        .await);
    let fa = &p.agent_account;
    let id: u64 = ok(fa.call(&good.id, "request_action").args_json(json!({ "action": "via full access" })).max_gas().transact().await)
        .json()
        .unwrap();
    must(p.approver.call(&good.id, "approve").args_json(json!({ "request_id": id, "action": "via full access" })).max_gas().transact().await);
    let r = check(&worker, &good, &[]);
    assert_eq!(r.code, 1);
    assert_eq!(r.verdict("DEP-1.4"), "FAIL");
    assert_eq!(r.verdict("VER-8"), "FAIL");
    assert!(r.detail("VER-8").contains(&format!("proof {id}")), "{}", r.detail("VER-8"));
    assert_eq!(ver8_prolog(&r.facts), ["0 ok".to_string(), format!("{id} reject")]);
    rec.insert("full_access_agent_key".into(), summary(&r));

    // 4. Not locked: C keeps its full-access key. DEP-1.2 and VER-3 fail.
    let unlocked = deploy(&worker, "unlocked", owner.id(), false).await;
    register_and_prove(&worker, &owner, &unlocked.id, "u").await;
    let r = check(&worker, &unlocked, &[]);
    assert_eq!(r.code, 1);
    assert_eq!(r.verdict("DEP-1.2"), "FAIL");
    assert_eq!(r.verdict("VER-3"), "FAIL");
    assert!(r.detail("VER-3").contains("full-access key"), "{}", r.detail("VER-3"));
    rec.insert("extra_full_access_key".into(), summary(&r));
    record("DEP-1", Value::Object(rec));
}

// PROP: RT-RESET VER-3 VER-6
#[tokio::test]
async fn rt_reset() {
    let worker = sandbox().await;
    let owner = subaccount(&worker, "owner", 10).await;
    // Not locked, so C's key can delete it.
    let d = deploy(&worker, "approvals", owner.id(), false).await;
    register_and_prove(&worker, &owner, &d.id, "").await;
    let c = d.key.clone().unwrap();
    let cached = (
        view_at(&worker, &d.id, "get_request_count").await,
        view_at(&worker, &d.id, "get_approval_count").await,
    );
    assert_eq!(cached, (1, 1));
    let hash_before = code_hash_b58(&wasm());

    // Delete C, then recreate it under the same name and redeploy, locked.
    must(c.clone().delete_account(worker.root_account().unwrap().id()).await);
    let again = deploy(&worker, "approvals", owner.id(), true).await;
    assert_eq!(again.id, d.id);
    let now = (
        view_at(&worker, &d.id, "get_request_count").await,
        view_at(&worker, &d.id, "get_approval_count").await,
    );
    assert_eq!(now, (0, 0), "counters reset");

    // VER-3, against the original b0: the scan finds the DeleteAccount (and
    // the recreation's AddKey and DeployContract).
    let r = check(&worker, &d, &[]);
    assert_eq!(r.verdict("VER-3"), "FAIL");
    let v3 = r.detail("VER-3");
    assert!(v3.contains("DeleteAccount"), "{v3}");
    // VER-6 (Prolog): a heuristic that catches it while counters are below the
    // cached ones, and misses it once they catch up.
    let out = prolog(
        "",
        &format!(
            "( verifier_rules:ver6_invalidates(state({}, {}, '{h}'), state({}, {}, '{h}')) -> write(invalidated) ; write(kept) ), nl, \
             ( verifier_rules:ver6_invalidates(state({}, {}, '{h}'), state({}, {}, '{h}')) -> write(invalidated) ; write(kept) ), nl",
            cached.0, cached.1, now.0, now.1, cached.0, cached.1, cached.0, cached.1,
            h = hash_before
        ),
    );
    assert_eq!(out.trim(), "invalidated\nkept");
    record(
        "RT-RESET",
        json!({
            "counters_before": [cached.0, cached.1],
            "counters_after_recreate": [now.0, now.1],
            "code_hash_unchanged": true,
            "ver3": "FAIL (DeleteAccount, AddKey, DeployContract receipts on C since b0)",
            "ver6": "invalidates while counters are below the cache; misses a reset that caught up",
        }),
    );
}

async fn view_at(worker: &Worker<Sandbox>, c: &AccountId, m: &str) -> u64 {
    worker.view(c, m).args_json(json!({})).await.unwrap().json().unwrap()
}
