//! RT-TRACE (strategy.md section 5.9): main flows on the deployed artifact.
//!
//! Replays the conformance traces (`conformance/traces/*.txt`, MC-2 format:
//! `<call>\t<result>\t<post-store>` per line, `#` ends a trace, owner `o`,
//! accounts `o a1 a2 a3`, keys `k0..k3`, actions `t1..t3 empty too_long`) on
//! the approval wasm in near-sandbox. Two files are checked in (see
//! `sandbox/scripts/gen-traces.sh`):
//! - `prolog.txt`: traces generated from the Prolog reference semantics
//!   `step/4` (mc2.pl `generate/2`);
//! - `core-random.txt`: 200 seeded random sequences of 30 calls from
//!   `kani/src/trace.rs`, whose every step the kani crate checks against the
//!   TLA+ transcription `tla.rs` (REF-5) and Prolog replays (MC-2).
//!
//! For every step the wasm must agree with the trace and with a host oracle:
//! - the result (Ok or the error name) equals the trace's;
//! - on `Err(e)` the receipt on C fails with exactly
//!   `Smart contract panicked: <e.as_str()>` and logs nothing;
//! - on `Ok` the receipt logs exactly the one expected NEP-297 line and
//!   returns the expected value;
//! - every `get_*` view equals the oracle's rendering, including `{}` args,
//!   explicit nulls, `limit = 0` and values above 2^53;
//! - the oracle's abstract post-state equals the trace's.
//!
//! The oracle is the real `approval-core` on the host (no borsh), over
//! `MemStore<String, String>` in the trace's own names, with each call's time
//! taken from the block the sandbox executed it in. `spec.rs` can't be the
//! oracle directly: its `ArrStore` holds at most 4 requests (Kani bounds).
//! The chain to `spec.rs` is: wasm = host core (this test) = spec.rs (Kani,
//! plain mode) and = tla.rs = step/4 (REF-5, MC-2, the trace files).
//! JSON is rendered here from the README field names, not by the shell.
//!
//! Environment: `RT_TRACE_FILES` (comma-separated paths), `RT_TRACE_LIMIT`
//! (traces per file), `RT_TRACE_JOBS` (traces in flight, default 4).

mod common;

use approval_core::{
    self as core, ActionRequest, ApprovalError as E, ApprovalProof, BlockTime, Caller, MemStore,
    Principal, RequestStatus, Role, Store,
};
use common::*;
use futures::{future::join_all, stream, StreamExt};
use near_workspaces::network::Sandbox;
use near_workspaces::result::ExecutionFinalResult;
use near_workspaces::types::{KeyType, NearToken, PublicKey, SecretKey};
use near_workspaces::{Account, AccountId, Contract, Worker};
use serde_json::{json, Value};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type M = MemStore<String, String>;
const ACCOUNTS: [&str; 4] = ["o", "a1", "a2", "a3"];
const KEYS: [&str; 4] = ["k0", "k1", "k2", "k3"];
/// kani/src/ids.rs ACTIONS: t1, t2, t3.
const ACTIONS: [&str; 3] = ["ab", "  ", "\u{e9}"];
const BIG: u64 = (1 << 53) + 1;

fn action_of(t: &str) -> String {
    match t {
        "empty" => String::new(),
        "too_long" => "x".repeat(MAX_ACTION_LEN + 1),
        t => ACTIONS[t[1..].parse::<usize>().unwrap() - 1].to_string(),
    }
}

fn class_of(a: &str) -> String {
    if a.is_empty() {
        "empty".into()
    } else if a.len() > MAX_ACTION_LEN {
        "too_long".into()
    } else {
        format!("t{}", ACTIONS.iter().position(|x| *x == a).unwrap() + 1)
    }
}

// ---------------------------------------------------------------------------
// Trace files
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Line {
    call: String,
    result: String,
    post: String,
}

fn load(path: &std::path::Path, limit: usize) -> Vec<Vec<Line>> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut out = vec![];
    let mut cur = vec![];
    for l in text.lines() {
        if l == "#" {
            out.push(std::mem::take(&mut cur));
            if out.len() == limit {
                break;
            }
            continue;
        }
        let f: Vec<&str> = l.split('\t').collect();
        cur.push(Line {
            call: f[0].into(),
            result: f[1].into(),
            post: f[2].into(),
        });
    }
    out
}

#[derive(Clone, Debug)]
enum Op {
    Add { caller: String, key: String, acct: String, role: Role },
    Revoke { caller: String, key: String },
    Req { c: Caller<String, String>, action: String },
    Appr { c: Caller<String, String>, id: u64, action: String },
    Rej { c: Caller<String, String>, id: u64 },
}

fn parse(call: &str) -> Op {
    let f: Vec<&str> = call.split(',').collect();
    let c = |f: &[&str]| Caller {
        predecessor: f[0].to_string(),
        signer: f[1].to_string(),
        signer_key: f[2].to_string(),
    };
    match f[0] {
        "add" => Op::Add {
            caller: f[1].into(),
            key: f[2].into(),
            acct: f[3].into(),
            role: if f[4] == "agent" { Role::Agent } else { Role::Approver },
        },
        "revoke" => Op::Revoke { caller: f[1].into(), key: f[2].into() },
        "request" => Op::Req { c: c(&f[1..4]), action: action_of(f[4]) },
        "approve" => Op::Appr { c: c(&f[1..4]), id: f[4].parse().unwrap(), action: action_of(f[5]) },
        "reject" => Op::Rej { c: c(&f[1..4]), id: f[4].parse().unwrap() },
        other => panic!("unknown call {other}"),
    }
}

// ---------------------------------------------------------------------------
// The oracle: the real core on the host, and its abstract text (mc2.rs `text`)
// ---------------------------------------------------------------------------

enum Res {
    Unit(Principal<String>),
    Revoked(Principal<String>),
    Req(ActionRequest<String, String>),
    Appr(ApprovalProof<String, String>),
    Rej(ActionRequest<String, String>),
}

fn oracle(m: &mut M, op: &Op, t: BlockTime) -> Result<Res, E> {
    match op {
        Op::Add { caller, key, acct, role } => {
            core::add_principal(m, caller, key.clone(), acct.clone(), *role).map(Res::Unit)
        }
        Op::Revoke { caller, key } => core::revoke_key(m, caller, key, t).map(Res::Revoked),
        Op::Req { c, action } => core::request_action(m, c, action.clone(), t).map(Res::Req),
        Op::Appr { c, id, action } => core::approve(m, c, *id, action, t).map(Res::Appr),
        Op::Rej { c, id } => core::reject(m, c, *id, t).map(Res::Rej),
    }
}

fn role_s(r: Role) -> &'static str {
    match r {
        Role::Agent => "agent",
        Role::Approver => "approver",
    }
}

/// graph_export.pl's store text, as kani/src/mc2.rs writes it.
fn text(m: &M) -> String {
    let mut ps: Vec<String> = KEYS
        .iter()
        .filter_map(|k| {
            m.principal(&k.to_string()).map(|p| {
                format!(
                    "{k},{},{},{},{},{}",
                    p.account_id,
                    role_s(p.role),
                    p.registration_id,
                    p.active_from,
                    p.pending
                )
            })
        })
        .collect();
    ps.sort();
    let rs: Vec<String> = m
        .requests
        .iter()
        .map(|r| {
            let ap = r.approval.as_ref().map_or("-".to_string(), |a| {
                format!(
                    "{}/{}/{}/{}",
                    a.approval_index, a.approver_account_id, a.approver_key, a.approver_registration_id
                )
            });
            let rj = r.rejection.as_ref().map_or("-".to_string(), |j| {
                format!("{}/{}/{}", j.approver_account_id, j.approver_key, j.approver_registration_id)
            });
            format!(
                "{},{},{},{},{ap},{rj}",
                r.agent_account_id,
                r.agent_key,
                r.agent_registration_id,
                class_of(&r.action)
            )
        })
        .collect();
    let mut v: Vec<u64> = m.revocations.iter().map(|(g, _)| *g).collect();
    v.sort();
    let join = |xs: &[u64]| xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    format!(
        "{}|{}|{}|{}|{}",
        ps.join(";"),
        rs.join(";"),
        join(&m.approval_log),
        m.registration_count,
        join(&v)
    )
}

// ---------------------------------------------------------------------------
// JSON rendering of the oracle (README "API" and "Events")
// ---------------------------------------------------------------------------

struct Names {
    accounts: HashMap<String, AccountId>,
    keys: HashMap<String, PublicKey>,
}

impl Names {
    fn a(&self, n: &str) -> Value {
        json!(self.accounts[n])
    }
    fn k(&self, n: &str) -> Value {
        json!(self.keys[n])
    }
}

fn bt(t: BlockTime) -> Value {
    json!({ "block": t.height, "ns": t.timestamp_ns.to_string() })
}

fn status_s(s: RequestStatus) -> &'static str {
    match s {
        RequestStatus::Pending => "pending",
        RequestStatus::Approved => "approved",
        RequestStatus::Rejected => "rejected",
        RequestStatus::Void => "void",
    }
}

fn request_view(n: &Names, m: &M, r: &ActionRequest<String, String>) -> Value {
    json!({
        "request_id": r.id,
        "agent_account_id": n.a(&r.agent_account_id),
        "agent_public_key": n.k(&r.agent_key),
        "agent_registration_id": r.agent_registration_id,
        "action": r.action,
        "requested_at_block": r.requested_at.height,
        "requested_at_ns": r.requested_at.timestamp_ns.to_string(),
        "status": status_s(core::status_of(m, r)),
    })
}

fn proof_view(n: &Names, m: &M, p: &ApprovalProof<String, String>) -> Value {
    let rv = core::proof_revocations(m, p);
    json!({
        "approval_index": p.approval_index,
        "request_id": p.request_id,
        "action": p.action,
        "agent_account_id": n.a(&p.agent_account_id),
        "agent_public_key": n.k(&p.agent_key),
        "agent_registration_id": p.agent_registration_id,
        "requested_at_block": p.requested_at.height,
        "requested_at_ns": p.requested_at.timestamp_ns.to_string(),
        "approver_account_id": n.a(&p.approver_account_id),
        "approver_public_key": n.k(&p.approver_key),
        "approver_registration_id": p.approver_registration_id,
        "approved_at_block": p.approved_at.height,
        "approved_at_ns": p.approved_at.timestamp_ns.to_string(),
        "agent_key_revoked_at": rv.agent.map(bt),
        "approver_key_revoked_at": rv.approver.map(bt),
    })
}

fn rejection_view(n: &Names, r: &ActionRequest<String, String>) -> Value {
    match &r.rejection {
        None => Value::Null,
        Some(j) => json!({
            "request_id": r.id,
            "action": r.action,
            "agent_account_id": n.a(&r.agent_account_id),
            "agent_public_key": n.k(&r.agent_key),
            "agent_registration_id": r.agent_registration_id,
            "requested_at_block": r.requested_at.height,
            "requested_at_ns": r.requested_at.timestamp_ns.to_string(),
            "approver_account_id": n.a(&j.approver_account_id),
            "approver_public_key": n.k(&j.approver_key),
            "approver_registration_id": j.approver_registration_id,
            "rejected_at_block": j.rejected_at.height,
            "rejected_at_ns": j.rejected_at.timestamp_ns.to_string(),
        }),
    }
}

fn principal_view(n: &Names, p: &Principal<String>) -> Value {
    json!({
        "account_id": n.a(&p.account_id),
        "role": role_s(p.role),
        "registration_id": p.registration_id,
        "pending": p.pending,
    })
}

fn event(name: &str, data: Value) -> Value {
    json!({ "standard": "trust_approval", "version": "1.0.0", "event": name, "data": data })
}

/// The expected event line and return value of a successful call.
fn expected_ok(n: &Names, m: &M, op: &Op, res: &Res, key: &str, t: BlockTime) -> (Value, Value) {
    match res {
        Res::Unit(p) => (
            event(
                "key_added",
                json!({
                    "public_key": n.k(key),
                    "account_id": n.a(&p.account_id),
                    "role": role_s(p.role),
                    "registration_id": p.registration_id,
                }),
            ),
            Value::Null,
        ),
        Res::Revoked(p) => (
            event(
                "key_revoked",
                json!({
                    "public_key": n.k(key),
                    "account_id": n.a(&p.account_id),
                    "role": role_s(p.role),
                    "registration_id": p.registration_id,
                    "revoked_at_block": t.height,
                    "revoked_at_ns": t.timestamp_ns.to_string(),
                    "voided_pending": p.pending,
                }),
            ),
            Value::Null,
        ),
        Res::Req(r) => (event("approval_requested", request_view(n, m, r)), json!(r.id)),
        Res::Appr(p) => {
            let v = proof_view(n, m, p);
            (event("action_approved", v.clone()), v)
        }
        Res::Rej(r) => {
            let v = rejection_view(n, r);
            let _ = op;
            (event("action_rejected", v.clone()), v)
        }
    }
}

/// Every view call and the oracle's answer.
fn expected_views(n: &Names, m: &M) -> Vec<(&'static str, Value, Value)> {
    let mut v = vec![
        ("get_owner", json!({}), n.a(&m.owner)),
        ("get_request_count", json!({}), json!(m.request_count())),
        ("get_approval_count", json!({}), json!(m.approval_count())),
    ];
    for k in KEYS {
        v.push((
            "get_principal",
            json!({ "public_key": n.k(k) }),
            m.principal(&k.to_string()).map_or(Value::Null, |p| principal_view(n, &p)),
        ));
    }
    for i in 0..=m.request_count() {
        let r = m.request(i);
        v.push((
            "get_request",
            json!({ "request_id": i }),
            r.as_ref().map_or(Value::Null, |r| request_view(n, m, r)),
        ));
        v.push((
            "get_approval",
            json!({ "request_id": i }),
            core::approval(m, i).map_or(Value::Null, |p| proof_view(n, m, &p)),
        ));
        v.push((
            "get_rejection",
            json!({ "request_id": i }),
            r.as_ref().map_or(Value::Null, |r| rejection_view(n, r)),
        ));
    }
    for g in 0..=m.registration_count {
        v.push((
            "get_revocation",
            json!({ "registration_id": g }),
            m.revocation(g).map_or(Value::Null, bt),
        ));
    }
    let page = |f: u64, l: u64| -> Value {
        Value::Array(core::approvals(m, f, l).iter().map(|p| proof_view(n, m, p)).collect())
    };
    for (args, f, l) in [
        (json!({}), 0, 50),
        (json!({ "from_index": null, "limit": null }), 0, 50),
        (json!({ "from_index": 0, "limit": 0 }), 0, 0),
        (json!({ "from_index": 1, "limit": 1 }), 1, 1),
        (json!({ "limit": BIG }), 0, BIG),
        (json!({ "from_index": BIG }), BIG, 50),
        (json!({ "from_index": u64::MAX, "limit": u64::MAX }), u64::MAX, u64::MAX),
    ] {
        v.push(("get_approvals", args, page(f, l)));
    }
    v.push(("get_request", json!({ "request_id": BIG }), Value::Null));
    v.push(("get_approval", json!({ "request_id": u64::MAX }), Value::Null));
    v.push(("get_revocation", json!({ "registration_id": u64::MAX }), Value::Null));
    v
}

// ---------------------------------------------------------------------------
// The sandbox side
// ---------------------------------------------------------------------------

struct Universe {
    worker: Worker<Sandbox>,
    contract: Contract,
    /// Each account signing with its own creation key (owner calls).
    admin: HashMap<String, Account>,
    /// (account, key) -> that account signing with that key.
    signer: HashMap<(String, String), Account>,
    names: Names,
}

async fn universe(worker: &Worker<Sandbox>, root_lock: &Mutex<()>, n: usize) -> Universe {
    let secrets: Vec<SecretKey> = (0..4)
        .map(|i| SecretKey::from_random(if i % 2 == 0 { KeyType::ED25519 } else { KeyType::SECP256K1 }))
        .collect();
    let relay = res("relay");
    let mut admin = HashMap::new();
    let mut signer = HashMap::new();
    let mut accounts = HashMap::new();
    for a in ACCOUNTS {
        let acc = {
            let _g = root_lock.lock().await;
            worker
                .root_account()
                .unwrap()
                .create_subaccount(&format!("t{n}{a}"))
                .keys(SecretKey::from_random(KeyType::ED25519))
                .initial_balance(NearToken::from_near(30))
                .transact()
                .await
                .unwrap()
                .into_result()
                .unwrap()
        };
        let mut batch = acc.batch(acc.id());
        for sk in &secrets {
            batch = batch.add_key(sk.public_key(), near_workspaces::AccessKey::full_access());
        }
        must(batch.deploy(&relay).transact().await);
        for (k, sk) in KEYS.iter().zip(&secrets) {
            signer.insert(
                (a.to_string(), k.to_string()),
                Account::from_secret_key(acc.id().clone(), sk.clone(), worker),
            );
        }
        accounts.insert(a.to_string(), acc.id().clone());
        admin.insert(a.to_string(), acc);
    }
    let c_account = {
        let _g = root_lock.lock().await;
        worker
            .root_account()
            .unwrap()
            .create_subaccount(&format!("t{n}c"))
            .keys(SecretKey::from_random(KeyType::ED25519))
            .initial_balance(NearToken::from_near(50))
            .transact()
            .await
            .unwrap()
            .into_result()
            .unwrap()
    };
    let contract = c_account.deploy(&wasm()).await.unwrap().into_result().unwrap();
    must(contract.call("new").args_json(json!({ "owner_id": accounts["o"] })).transact().await);
    let keys = KEYS.iter().zip(&secrets).map(|(k, sk)| (k.to_string(), sk.public_key())).collect();
    Universe {
        worker: worker.clone(),
        contract,
        admin,
        signer,
        names: Names { accounts, keys },
    }
}

async fn call(u: &Universe, cl: &Caller<String, String>, method: &str, args: Value) -> near_workspaces::Result<ExecutionFinalResult> {
    let c = u.contract.id();
    let who = &u.signer[&(cl.signer.clone(), cl.signer_key.clone())];
    if cl.predecessor == cl.signer {
        who.call(c, method).args_json(args).max_gas().transact().await
    } else {
        // predecessor != signer: the signer calls the relay deployed on the
        // predecessor's account.
        who.call(&u.names.accounts[&cl.predecessor], "forward")
            .args_json(json!({ "receiver": c, "method": method, "args": args.to_string() }))
            .max_gas()
            .transact()
            .await
    }
}

async fn send(u: &Universe, op: &Op) -> ExecutionFinalResult {
    let c = u.contract.id();
    let n = &u.names;
    let r = match op {
        Op::Add { caller, key, acct, role } => {
            let method = if *role == Role::Agent { "add_agent" } else { "add_approver" };
            u.admin[caller]
                .call(c, method)
                .args_json(json!({ "account_id": n.a(acct), "public_key": n.k(key) }))
                .max_gas()
                .transact()
                .await
        }
        Op::Revoke { caller, key } => {
            u.admin[caller]
                .call(c, "revoke_key")
                .args_json(json!({ "public_key": n.k(key) }))
                .max_gas()
                .transact()
                .await
        }
        Op::Req { c: cl, action } => call(u, cl, "request_action", json!({ "action": action })).await,
        Op::Appr { c: cl, id, action } => call(u, cl, "approve", json!({ "request_id": id, "action": action })).await,
        Op::Rej { c: cl, id } => call(u, cl, "reject", json!({ "request_id": id })).await,
    };
    r.expect("transaction rejected before execution")
}

fn key_of(op: &Op) -> String {
    match op {
        Op::Add { key, .. } | Op::Revoke { key, .. } => key.clone(),
        Op::Req { c, .. } | Op::Appr { c, .. } | Op::Rej { c, .. } => c.signer_key.clone(),
    }
}

/// Replays one trace on a fresh contract; returns the number of steps.
async fn replay(worker: Worker<Sandbox>, root_lock: Arc<Mutex<()>>, n: usize, label: String, trace: Vec<Line>) -> usize {
    let u = universe(&worker, &root_lock, n).await;
    let c = u.contract.id().clone();
    let mut m: M = MemStore::new("o".to_string());
    for (step, line) in trace.iter().enumerate() {
        let at = format!("{label} step {step}: {}", line.call);
        let op = parse(&line.call);
        let outcome = send(&u, &op).await;
        let on_c = receipts_on(&outcome, &c);
        assert_eq!(on_c.len(), 1, "{at}: receipts on C: {:?}", outcome.receipt_outcomes());
        let r = on_c[0];
        let (height, ns) = block_time(&u.worker, r).await;
        let t = BlockTime { height, timestamp_ns: ns };
        let res = oracle(&mut m, &op, t);
        let got_name = res.as_ref().err().map_or("Ok".to_string(), |e| format!("{e:?}"));
        assert_eq!(got_name, line.result, "{at}: host core disagrees with the trace");
        assert_eq!(text(&m), line.post, "{at}: host core post-state disagrees with the trace");
        match &res {
            Err(e) => {
                assert!(!r.is_success(), "{at}: wasm succeeded, expected {e:?}");
                let msg = format!("{:?}", r.clone().into_result().unwrap_err());
                let want = format!("\"{PANIC_PREFIX}{}\"", e.as_str());
                assert!(msg.contains(&want), "{at}: wasm failure {msg}, expected {want}");
                assert!(r.logs.is_empty(), "{at}: failed call logged {:?}", r.logs);
            }
            Ok(res) => {
                assert!(r.is_success() && outcome.is_success(), "{at}: wasm failed: {:?}", outcome.failures());
                let (ev, ret) = expected_ok(&u.names, &m, &op, res, &key_of(&op), t);
                assert_eq!(r.logs.len(), 1, "{at}: logs {:?}", r.logs);
                let line_json = r.logs[0].strip_prefix("EVENT_JSON:").unwrap_or_else(|| panic!("{at}: {}", r.logs[0]));
                let got: Value = serde_json::from_str(line_json).unwrap();
                assert_eq!(got, ev, "{at}: event");
                let raw = outcome.raw_bytes().unwrap();
                let got_ret: Value = if raw.is_empty() { Value::Null } else { serde_json::from_slice(&raw).unwrap() };
                assert_eq!(got_ret, ret, "{at}: return value");
            }
        }
        let want = expected_views(&u.names, &m);
        let got = join_all(want.iter().map(|(method, args, _)| async {
            u.contract.view(method).args_json(args.clone()).await.map(|r| r.json::<Value>().unwrap())
        }))
        .await;
        for ((method, args, exp), g) in want.iter().zip(got) {
            let g = g.unwrap_or_else(|e| panic!("{at}: view {method} {args}: {e:?}"));
            assert_eq!(&g, exp, "{at}: view {method} {args}");
        }
    }
    trace.len()
}

// PROP: RT-TRACE
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn rt_trace() {
    let files: Vec<std::path::PathBuf> = match std::env::var("RT_TRACE_FILES") {
        Ok(v) => v.split(',').map(Into::into).collect(),
        Err(_) => {
            let dir = sandbox_dir().join("../conformance/traces");
            let mut f: Vec<_> = std::fs::read_dir(&dir)
                .unwrap_or_else(|e| panic!("{}: {e}; run sandbox/scripts/gen-traces.sh", dir.display()))
                .map(|e| e.unwrap().path())
                .filter(|p| p.extension().is_some_and(|x| x == "txt"))
                .collect();
            f.sort();
            f
        }
    };
    let limit: usize = std::env::var("RT_TRACE_LIMIT").ok().and_then(|v| v.parse().ok()).unwrap_or(usize::MAX);
    let jobs: usize = std::env::var("RT_TRACE_JOBS").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
    let worker = sandbox().await;
    let root_lock = Arc::new(Mutex::new(()));
    let mut work = vec![];
    let mut per_file = serde_json::Map::new();
    for f in &files {
        let traces = load(f, limit);
        let name = f.file_name().unwrap().to_string_lossy().to_string();
        per_file.insert(
            name.clone(),
            json!({ "traces": traces.len(), "steps": traces.iter().map(Vec::len).sum::<usize>() }),
        );
        for (i, t) in traces.into_iter().enumerate() {
            work.push((format!("{name}#{i}"), t));
        }
    }
    assert!(!work.is_empty(), "no traces in {files:?}");
    let total = work.len();
    let started = std::time::Instant::now();
    let steps: usize = stream::iter(work.into_iter().enumerate().map(|(n, (label, t))| {
        let (w, l) = (worker.clone(), root_lock.clone());
        tokio::spawn(replay(w, l, n, label, t))
    }))
    .buffer_unordered(jobs)
    .map(|r| r.expect("trace task panicked"))
    .fold(0, |a, b| async move { a + b })
    .await;
    eprintln!("RT-TRACE: {total} traces, {steps} steps in {:?}", started.elapsed());
    // Only a full run updates the committed record.
    if limit == usize::MAX && std::env::var("RT_TRACE_FILES").is_err() {
        record(
            "RT-TRACE",
            json!({ "files": per_file, "traces": total, "steps": steps, "result": "every step equal" }),
        );
    }
}
