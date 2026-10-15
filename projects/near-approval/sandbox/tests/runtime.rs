//! M6 runtime assumption tests (strategy.md section 5.9): RT-KEY, RT-RELAY,
//! RT-SELFACCT, RT-METATX, RT-FCKEY, RT-REVERT, RT-BATCH, RT-SPOOF and
//! RT-CODEHASH, on the approval wasm in a local near-sandbox.
//! (RT-RESET is in `deploy.rs`, next to the VER-3 check that detects it;
//! RT-TRACE is in `trace.rs`.)
//!
//! Tests that *record* an outcome write it to `results/<ID>.json`.

mod common;

use common::*;
use near_workspaces::operations::Function;
use near_workspaces::types::{AccessKey, Gas, KeyType, NearToken};
use near_workspaces::AccountId;
use serde_json::{json, Value};

// PROP: RT-CODEHASH
#[tokio::test]
async fn rt_codehash() {
    let worker = sandbox().await;
    let owner = subaccount(&worker, "owner", 10).await;
    let contract = deploy_init(&worker, "approvals", owner.id()).await;
    let code = wasm();
    let sha = hex(&sha256(&code));
    let b58 = code_hash_b58(&code);
    let account = contract.view_account().await.unwrap();
    let onchain_hash = match account.contract_state {
        near_workspaces::ContractState::LocalHash(h) => h.to_string(),
        other => panic!("expected a locally deployed contract, got {other:?}"),
    };
    assert_eq!(onchain_hash, b58, "on-chain code_hash = base58(sha256(wasm))");
    assert_eq!(contract.view_code().await.unwrap(), code, "deployed code reads back unchanged");
    // In CI the sandbox job pins the expected reproducible-build hash.
    if let Ok(expected) = std::env::var("APPROVAL_WASM_EXPECTED_SHA256") {
        assert_eq!(sha, expected, "wasm under test is not the expected reproducible build");
    }
    let exports = function_exports(&code);
    record(
        "RT-CODEHASH",
        json!({
            "wasm_sha256": sha,
            "code_hash": b58,
            "bytes": code.len(),
            "reproducible": wasm_kind() == "reproducible",
            "function_exports": exports,
        }),
    );
}

// PROP: RT-KEY
#[tokio::test]
async fn rt_key() {
    for key_type in [KeyType::ED25519, KeyType::SECP256K1] {
        let s = setup(false, key_type).await;
        let c = s.contract.id();

        // A function-call key of the agent account arrives as signer =
        // predecessor = agent, with signer_pk = that key.
        let outcome = ok(s.request("deploy v2").await);
        let event = single_event(&outcome);
        assert_eq!(event["data"]["agent_account_id"], json!(s.agent.id()));
        assert_eq!(event["data"]["agent_public_key"], json!(pk(&s.agent)));
        let id: u64 = outcome.json().unwrap();
        // Same for the approver.
        let outcome = ok(s.approve(id, "deploy v2").await);
        let event = single_event(&outcome);
        assert_eq!(event["data"]["approver_account_id"], json!(s.approver.id()));
        assert_eq!(event["data"]["approver_public_key"], json!(pk(&s.approver)));

        // An unregistered key on the right account: UnknownKey.
        let stray = function_call_key(&s.worker, &s.agent_account, c, &["request_action"], key_type).await;
        assert_fails_with(
            stray
                .call(c, "request_action")
                .args_json(json!({ "action": "x" }))
                .transact()
                .await,
            &format!("{PANIC_PREFIX}signing key is unknown"),
        );

        // A key registered to the agent account but held by another account:
        // KeyAccountMismatch.
        let other = subaccount(&s.worker, "other", 5).await;
        let other_fc = function_call_key(&s.worker, &other, c, &["request_action"], key_type).await;
        must(s.owner
            .call(c, "add_agent")
            .args_json(json!({ "account_id": s.agent.id(), "public_key": pk(&other_fc) }))
            .transact()
            .await);
        assert_fails_with(
            other_fc
                .call(c, "request_action")
                .args_json(json!({ "action": "x" }))
                .transact()
                .await,
            &format!("{PANIC_PREFIX}signing key belongs to another account"),
        );
        assert_eq!(s.view("get_request_count", json!({})).await, json!(1));
    }
}

/// Registers `account`'s own (full-access) key as `role` (`add_agent` /
/// `add_approver`). DEP-1.4 forbids this; RT-RELAY, RT-SELFACCT, RT-BATCH and
/// SH-10 need it.
async fn register_full_access(s: &Setup, method: &str, account: &near_workspaces::Account) {
    must(s.owner
        .call(s.contract.id(), method)
        .args_json(json!({ "account_id": account.id(), "public_key": pk(account) }))
        .transact()
        .await);
}

// PROP: RT-RELAY
#[tokio::test]
async fn rt_relay() {
    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id();
    let relay_account = subaccount(&s.worker, "relay", 10).await;
    let relay = relay_account.deploy(&res("relay")).await.unwrap().into_result().unwrap();
    // The worst case for the contract: the victims' keys can sign anything.
    register_full_access(&s, "add_agent", &s.agent_account).await;
    register_full_access(&s, "add_approver", &s.approver_account).await;
    let id: u64 = ok(s.request("real").await).json().unwrap();
    let before = s.snapshot().await;

    let forward = |who: &near_workspaces::Account, method: &str, args: Value| {
        who.call(relay.id(), "forward")
            .args_json(json!({ "receiver": c, "method": method, "args": args.to_string() }))
            .max_gas()
            .transact()
    };
    for (who, method, args) in [
        (&s.agent_account, "request_action", json!({ "action": "relayed" })),
        (&s.approver_account, "approve", json!({ "request_id": id, "action": "real" })),
        (&s.approver_account, "reject", json!({ "request_id": id })),
    ] {
        let (text, outcome) = executed_failure(forward(who, method, args).await);
        assert!(
            text.contains(&format!("{PANIC_PREFIX}caller must be the signing account")),
            "{method}: {text}"
        );
        // The failure is the approval contract's receipt, and it logged nothing.
        let on_c = receipts_on(&outcome, c);
        assert_eq!(on_c.len(), 1);
        assert!(on_c[0].is_failure() && on_c[0].logs.is_empty());
    }
    assert_eq!(s.snapshot().await, before, "relayed calls changed state");

    // With DEP-1.4 keys the relay can't even be reached: a function-call
    // key whose receiver is C can't sign a transaction to the relay.
    let text = failure(
        s.agent
            .call(relay.id(), "forward")
            .args_json(json!({ "receiver": c, "method": "request_action", "args": "{}" }))
            .transact()
            .await,
    );
    assert!(text.contains("ReceiverMismatch"), "{text}");
}

// PROP: RT-SELFACCT
#[tokio::test]
async fn rt_selfacct() {
    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id();
    // Code on the agent's own account; its full-access key registered as an
    // agent key (what DEP-1.4 forbids).
    s.agent_account.deploy(&res("selfacct")).await.unwrap().into_result().unwrap();
    register_full_access(&s, "add_agent", &s.agent_account).await;

    let outcome = ok(s
        .agent_account
        .call(s.agent_account.id(), "request")
        .args_json(json!({ "target": c, "action": "via own code" }))
        .max_gas()
        .transact()
        .await);
    let logs = logs_on(&outcome, c);
    assert_eq!(logs.len(), 1);
    let event: Value = serde_json::from_str(logs[0].strip_prefix("EVENT_JSON:").unwrap()).unwrap();
    assert_eq!(event["event"], "approval_requested");
    // Accepted, and attributed to the signing key: predecessor = signer
    // holds even though the agent's code, not the key holder, made the call (F-9).
    assert_eq!(event["data"]["agent_account_id"], json!(s.agent_account.id()));
    assert_eq!(event["data"]["agent_public_key"], json!(pk(&s.agent_account)));

    // A DEP-1.4 function-call key (receiver C) can't invoke the account's
    // own code, so the case needs a non-compliant key.
    let text = failure(
        s.agent
            .call(s.agent_account.id(), "request")
            .args_json(json!({ "target": c, "action": "x" }))
            .transact()
            .await,
    );
    assert!(text.contains("ReceiverMismatch"), "{text}");
    record(
        "RT-SELFACCT",
        json!({
            "outcome": "success",
            "event": "approval_requested",
            "attributed_to": "agent account and its full-access key",
            "fc_key_scoped_to_C": "InvalidAccessKeyError::ReceiverMismatch",
        }),
    );
}

// PROP: RT-FCKEY
#[tokio::test]
async fn rt_fckey() {
    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id();
    let id: u64 = ok(s.request("x").await).json().unwrap();
    let before = s.snapshot().await;

    // The kind, not a contract panic: the runtime refused the transaction
    // before the contract ran (`Err` from RPC, no outcome).
    let rejected = |r: near_workspaces::Result<near_workspaces::result::ExecutionFinalResult>| match r {
        Err(e) => format!("{e:?}"),
        Ok(o) => panic!("expected an invalid transaction, got an executed outcome: {:?}", o.failures()),
    };
    let mut observed = serde_json::Map::new();
    for (who, label, method, args) in [
        (&s.agent, "agent", "approve", json!({ "request_id": id, "action": "x" })),
        (&s.agent, "agent", "add_agent", json!({ "account_id": s.agent.id(), "public_key": pk(&s.agent) })),
        (&s.approver, "approver", "request_action", json!({ "action": "y" })),
    ] {
        let text = rejected(who.call(c, method).args_json(args).transact().await);
        assert!(
            text.contains("InvalidAccessKeyError") && text.contains("MethodNameMismatch"),
            "{label} -> {method}: {text}"
        );
        assert!(!text.contains(PANIC_PREFIX), "{text}");
        observed.insert(format!("{label}_key->{method}"), json!("InvalidTxError::InvalidAccessKeyError(MethodNameMismatch)"));
    }
    // No deposit through a function-call key.
    let text = rejected(
        s.agent
            .call(c, "request_action")
            .args_json(json!({ "action": "x" }))
            .deposit(NearToken::from_yoctonear(1))
            .transact()
            .await,
    );
    assert!(text.contains("DepositWithFunctionCall"), "{text}");
    observed.insert("agent_key+deposit".into(), json!("DepositWithFunctionCall"));
    // No AddKey through a function-call key.
    let text = rejected(
        s.agent
            .batch(s.agent.id())
            .add_key(
                near_workspaces::types::SecretKey::from_random(KeyType::ED25519).public_key(),
                AccessKey::full_access(),
            )
            .transact()
            .await,
    );
    assert!(text.contains("RequiresFullAccess") || text.contains("ReceiverMismatch"), "{text}");
    observed.insert("agent_key->AddKey".into(), json!(if text.contains("RequiresFullAccess") { "RequiresFullAccess" } else { "ReceiverMismatch" }));
    assert_eq!(s.snapshot().await, before);
    record("RT-FCKEY", Value::Object(observed));
}

// PROP: RT-REVERT
#[tokio::test]
async fn rt_revert() {
    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id();
    let mut rec = serde_json::Map::new();

    // 1. A core rejection: panics, writes nothing, logs nothing (SH-3 on chain).
    let before = s.snapshot().await;
    let (text, outcome) = executed_failure(s.request("").await);
    assert!(text.contains(&format!("{PANIC_PREFIX}action is empty")), "{text}");
    assert!(logs_on(&outcome, c).is_empty());
    assert_eq!(s.snapshot().await, before);

    // 2. Out of gas after the emit. Find the least gas a request succeeds
    // with, then probe below it; each success is rejected again to keep the
    // agent key under its pending cap.
    let pending_id: u64 = ok(s.request("keep").await).json().unwrap();
    let agent = s.agent.clone();
    let try_gas = |g: u64| {
        let agent = agent.clone();
        let c = c.clone();
        async move {
            agent
                .call(&c, "request_action")
                .args_json(json!({ "action": "gas probe" }))
                .gas(Gas::from_gas(g))
                .transact()
                .await
                .unwrap()
        }
    };
    let (mut lo, mut hi) = (Gas::from_ggas(1).as_gas(), Gas::from_tgas(300).as_gas());
    let free = |o: &near_workspaces::result::ExecutionFinalResult| -> u64 { o.clone().json().unwrap() };
    let mut succeeded = Vec::new();
    while hi - lo > Gas::from_ggas(2).as_gas() {
        let mid = lo + (hi - lo) / 2;
        let o = try_gas(mid).await;
        if o.is_success() {
            succeeded.push(free(&o));
            hi = mid;
        } else {
            lo = mid;
        }
        for id in succeeded.drain(..) {
            must(s.approver
                .call(c, "reject")
                .args_json(json!({ "request_id": id }))
                .max_gas()
                .transact()
                .await);
        }
    }
    let mut probes = Vec::new();
    let mut event_survives_oog = false;
    let mut g = hi;
    // Probe downwards in steps of 1/40 of the minimum.
    let step = hi / 40;
    while g > step && probes.len() < 40 {
        g -= step;
        let before = s.snapshot().await;
        let o = try_gas(g).await;
        if o.is_success() {
            let id = free(&o);
            must(s.approver.call(c, "reject").args_json(json!({ "request_id": id })).max_gas().transact().await);
            continue;
        }
        let text = format!("{:?}", o.clone().into_result().unwrap_err());
        let logs = logs_on(&o, c);
        let kind = match text.split_once("ExecutionError(\"") {
            Some((_, rest)) => rest.split("\")").next().unwrap().to_string(),
            None => text.chars().take(120).collect(),
        };
        if !logs.is_empty() {
            event_survives_oog = true;
        }
        assert_eq!(s.snapshot().await, before, "out-of-gas failure changed state");
        probes.push(json!({ "fraction_of_min": format!("{}/40", 40 - (hi - g) / step), "failure": kind, "logs_on_C": logs.len() }));
        // Stop once probes have shown both: failures with and without the event.
        if event_survives_oog && logs.is_empty() {
            break;
        }
    }
    rec.insert(
        "out_of_gas".into(),
        json!({
            "min_success_gas_tgas_approx": (hi as f64 / 1e12 * 10.0).round() / 10.0,
            "probes": probes,
            "event_survives_in_failed_outcome": event_survives_oog,
        }),
    );

    // 3. LackBalanceForState: leave C its current storage plus 10 bytes.
    let details = s.contract.view_account().await.unwrap();
    let balance = (details.storage_usage as u128 + 10) * YOCTO_PER_BYTE;
    s.worker
        .patch(c)
        .account_from_current(move |cur| {
            near_workspaces::types::AccountDetailsPatch::from(cur).balance(NearToken::from_yoctonear(balance))
        })
        .transact()
        .await
        .unwrap();
    let before = s.snapshot().await;
    let mut lack = serde_json::Map::new();
    for (label, result) in [
        ("request_action", s.request(&"a".repeat(MAX_ACTION_LEN)).await),
        ("approve", s.approve(pending_id, "keep").await),
    ] {
        let (text, outcome) = executed_failure(result);
        assert!(text.contains("LackBalanceForState"), "{label}: {text}");
        let logs = logs_on(&outcome, c);
        lack.insert(label.into(), json!({ "failure": "LackBalanceForState", "logs_on_C": logs.len(),
            "event_survives_in_failed_outcome": !logs.is_empty() }));
    }
    assert_eq!(s.snapshot().await, before, "LackBalanceForState changed state");
    assert_eq!(s.view("get_approval", json!({ "request_id": pending_id })).await, Value::Null);
    let next = s.view("get_request_count", json!({})).await.as_u64().unwrap();
    assert_eq!(s.view("get_request", json!({ "request_id": next })).await, Value::Null);
    rec.insert("lack_balance_for_state".into(), Value::Object(lack));
    rec.insert("core_rejection".into(), json!({ "failure": "action is empty", "logs_on_C": 0 }));
    record("RT-REVERT", Value::Object(rec));
}

// PROP: RT-BATCH
#[tokio::test]
async fn rt_batch() {
    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id();
    // A function-call key can sign only single-action transactions, so the
    // agent account's full-access key is registered as its agent key.
    register_full_access(&s, "add_agent", &s.agent_account).await;
    let before = s.snapshot().await;
    let before_fa = s.view("get_principal", json!({ "public_key": pk(&s.agent_account) })).await;
    let result = s
        .agent_account
        .batch(c)
        .call(Function::new("request_action").args_json(json!({ "action": "a" })).gas(Gas::from_tgas(100)))
        .call(Function::new("request_action").args_json(json!({ "action": "" })).gas(Gas::from_tgas(100)))
        .transact()
        .await;
    let (text, outcome) = executed_failure(result);
    assert!(text.contains(&format!("{PANIC_PREFIX}action is empty")), "{text}");
    assert!(text.contains("index: Some(1)"), "failure is not at action index 1: {text}");
    assert_eq!(s.snapshot().await, before, "batch left state behind");
    assert_eq!(
        s.view("get_principal", json!({ "public_key": pk(&s.agent_account) })).await,
        before_fa,
        "pending count of the full-access agent key changed"
    );
    let logs = logs_on(&outcome, c);
    let events: Vec<String> = logs
        .iter()
        .filter_map(|l| l.strip_prefix("EVENT_JSON:"))
        .map(|j| {
            let v: Value = serde_json::from_str(j).unwrap();
            format!("{} request_id={} action={}", v["event"].as_str().unwrap(), v["data"]["request_id"], v["data"]["action"])
        })
        .collect();
    record(
        "RT-BATCH",
        json!({
            "failure": "ActionError index 1: Smart contract panicked: action is empty",
            "counters_unchanged": true,
            "events_in_failed_outcome": events,
            "first_event_appears": logs.iter().any(|l| l.contains("approval_requested")),
        }),
    );
}

// PROP: RT-METATX
#[tokio::test]
async fn rt_metatx() {
    use near_crypto::{InMemorySigner, SecretKey as NcSecretKey};
    use near_jsonrpc_client::{methods, JsonRpcClient};
    use near_primitives::action::delegate::{DelegateAction, NonDelegateAction, SignedDelegateAction};
    use near_primitives::action::{Action, FunctionCallAction};
    use near_primitives::transaction::{SignedTransaction, Transaction, TransactionV0};
    use near_primitives::views::{FinalExecutionOutcomeViewEnum, FinalExecutionStatus, TxExecutionStatus};

    let s = setup(false, KeyType::ED25519).await;
    let c: AccountId = s.contract.id().clone();
    let relayer = subaccount(&s.worker, "relayer", 10).await;
    let rpc = JsonRpcClient::connect(s.worker.rpc_addr());
    let nc_signer = |a: &near_workspaces::Account| {
        let sk: NcSecretKey = a.secret_key().to_string().parse().unwrap();
        InMemorySigner::from_secret_key(a.id().clone(), sk)
    };
    let mut rec = serde_json::Map::new();
    // The agent's DEP-1.4 key, then its full-access key registered as an agent key.
    register_full_access(&s, "add_agent", &s.agent_account).await;
    for (label, agent) in [("agent_fc_key", &s.agent), ("agent_full_access_key", &s.agent_account)] {
        let before = s.snapshot().await;
        let inner = nc_signer(agent);
        let key = s.worker.view_access_key(agent.id(), &pk(agent)).await.unwrap();
        let head = s.worker.view_block().await.unwrap();
        let delegate = DelegateAction {
            sender_id: agent.id().clone(),
            receiver_id: c.clone(),
            actions: vec![NonDelegateAction::try_from(Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: "request_action".into(),
                args: json!({ "action": "meta" }).to_string().into_bytes(),
                gas: near_primitives::gas::Gas::from_teragas(100),
                deposit: near_primitives::types::Balance::from_yoctonear(0),
            })))
            .unwrap()],
            nonce: key.nonce + 1,
            max_block_height: head.height() + 100,
            public_key: inner.public_key(),
        };
        let signed = SignedDelegateAction::sign(&inner, delegate);
        let outer = nc_signer(&relayer);
        let rkey = s.worker.view_access_key(relayer.id(), &pk(&relayer)).await.unwrap();
        let tx = Transaction::V0(TransactionV0 {
            signer_id: relayer.id().clone(),
            public_key: outer.public_key(),
            nonce: rkey.nonce + 1 + (label.len() as u64),
            receiver_id: agent.id().clone(),
            block_hash: head.hash().to_string().parse().unwrap(),
            actions: vec![Action::Delegate(Box::new(signed))],
        });
        let (hash, _) = tx.get_hash_and_size();
        let signed_tx = SignedTransaction::new(outer.sign(hash.as_ref()), tx);
        let resp = rpc
            .call(methods::send_tx::RpcSendTransactionRequest {
                signed_transaction: signed_tx,
                wait_until: TxExecutionStatus::Final,
            })
            .await
            .expect("relayer transaction");
        let outcome = match resp.final_execution_outcome.expect("outcome") {
            FinalExecutionOutcomeViewEnum::FinalExecutionOutcome(o) => o,
            FinalExecutionOutcomeViewEnum::FinalExecutionOutcomeWithReceipt(o) => o.final_outcome,
        };
        let on_c: Vec<_> = outcome.receipts_outcome.iter().filter(|r| r.outcome.executor_id == c).collect();
        let c_status = on_c.first().map(|r| format!("{:?}", r.outcome.status)).unwrap_or_else(|| "no receipt on C".into());
        let overall = match &outcome.status {
            FinalExecutionStatus::SuccessValue(_) => "success".to_string(),
            other => format!("{other:?}"),
        };
        let indirect = c_status.contains("caller must be the signing account");
        rec.insert(
            label.into(),
            json!({
                "receipt_on_C": if indirect { "Smart contract panicked: caller must be the signing account (IndirectCall)".to_string() } else { c_status.clone() },
                "transaction_status": if overall == "success" { "success" } else { "failure" },
                "state_unchanged": s.snapshot().await == before,
            }),
        );
        // ASM-META: the inner receipt has signer = relayer, so the core
        // refuses it. Recorded above; asserted here as the expected outcome.
        assert!(indirect, "{label}: receipt on C was {c_status}");
        assert_eq!(s.snapshot().await, before);
    }
    record("RT-METATX", Value::Object(rec));
}

// PROP: RT-SPOOF VER-1
#[tokio::test]
async fn rt_spoof() {
    let s = setup(false, KeyType::ED25519).await;
    let c = s.contract.id().clone();
    let id: u64 = ok(s.request("pay 10").await).json().unwrap();
    let real = ok(s.approve(id, "pay 10").await);
    let real_line = logs_on(&real, &c).pop().unwrap();
    let spoofer = subaccount(&s.worker, "spoofer", 10)
        .await
        .deploy(&res("spoofer"))
        .await
        .unwrap()
        .into_result()
        .unwrap();
    // A byte-for-byte copy of the real event, and one that claims an
    // approval that never happened.
    let forged = real_line.replace("\"request_id\":0", "\"request_id\":7");
    let mut receipts = vec![(real.outcome().block_hash, c.clone(), true, real_line.clone())];
    for line in [&real_line, &forged] {
        let o = ok(spoofer.call("emit").args_json(json!({ "line": line })).transact().await);
        let r = receipts_on(&o, spoofer.id())[0];
        receipts.push((r.block_hash, spoofer.id().clone(), r.is_success(), line.clone()));
    }
    // And a failed receipt on C that logged before failing would look the
    // same as a success to a log scraper; VER-1 also needs status = success.
    // (RT-REVERT records whether such logs exist; here we feed one in.)
    receipts.push((real.outcome().block_hash, c.clone(), false, real_line.clone()));

    // VER-1 in Prolog (prolog/verification/verifier_rules.pl) decides.
    let mut facts = String::new();
    for (n, (_, executor, success, line)) in receipts.iter().enumerate() {
        let ev: Value = serde_json::from_str(line.strip_prefix("EVENT_JSON:").unwrap()).unwrap();
        facts += &format!(
            "observed_log(r{n}, '{executor}', {}, final, '{}', '{}', '{}', {}).\n",
            if *success { "success" } else { "failure" },
            ev["standard"].as_str().unwrap(),
            ev["version"].as_str().unwrap(),
            ev["event"].as_str().unwrap(),
            ev["data"]["request_id"]
        );
    }
    let goal = format!(
        "forall(observed_log(R, E, S, F, Std, V, Ev, I), \
         ( verifier_rules:ver1_accept('{c}', log(receipt(E, S, F), event(Std, V, Ev, I))) \
           -> format(\"accept ~a~n\", [R]) ; format(\"reject ~a~n\", [R]) ))"
    );
    let out = prolog(&facts, &goal);
    assert_eq!(out.trim(), "accept r0\nreject r1\nreject r2\nreject r3", "{out}");
    // The authoritative read (VER-1's first clause) agrees with the real event.
    let proof = s.view("get_approval", json!({ "request_id": id })).await;
    let ev: Value = serde_json::from_str(real_line.strip_prefix("EVENT_JSON:").unwrap()).unwrap();
    assert_eq!(proof, ev["data"]);
    assert_eq!(s.view("get_approval", json!({ "request_id": 7 })).await, Value::Null);
    record(
        "RT-SPOOF",
        json!({
            "spoofer_receipt_status": "success",
            "ver1": { "real_event_on_C": "accept", "copy_from_spoofer": "reject", "forged_from_spoofer": "reject", "failed_receipt_on_C": "reject" },
        }),
    );
}

