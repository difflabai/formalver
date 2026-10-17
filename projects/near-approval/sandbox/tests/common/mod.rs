//! Shared helpers for the M6 sandbox tests (strategy.md sections 5.9 and 9).
//!
//! Adapted from upstream `contracts/approval/sandbox/tests/sandbox.rs` at the
//! pin (`wasm`, `failure`, `events`, `subaccount`, `function_call_key`,
//! `setup`): the same patterns, extended with the helper contracts in
//! `res/`, outcome recording and block-time lookups.

#![allow(dead_code)]

use near_workspaces::network::Sandbox;
use near_workspaces::result::{ExecutionFinalResult, ExecutionOutcome};
use near_workspaces::types::{AccessKey, KeyType, NearToken, PublicKey, SecretKey};
use near_workspaces::{Account, AccountId, Contract, Worker};
use serde_json::{json, Value};
use std::path::PathBuf;

/// NEAR's limit on the total length of logs emitted by one receipt.
pub const MAX_TOTAL_LOG_LEN: usize = 16 * 1024;
/// Storage price: yoctoNEAR per byte.
pub const YOCTO_PER_BYTE: u128 = 10_000_000_000_000_000_000;
pub const MAX_ACTION_LEN: usize = 2048;
/// near-sdk's message prefix for `env::panic_str` (SH-3, on-chain form).
pub const PANIC_PREFIX: &str = "Smart contract panicked: ";

pub fn sandbox_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

pub fn wasm_path() -> PathBuf {
    std::env::var("APPROVAL_WASM").map(PathBuf::from).unwrap_or_else(|_| {
        sandbox_dir().join("target/approval/near/approval_contract/approval_contract.wasm")
    })
}

/// The approval contract wasm under test (`APPROVAL_WASM`, or the output of
/// `scripts/build-wasm.sh`).
pub fn wasm() -> Vec<u8> {
    let path = wasm_path();
    std::fs::read(&path).unwrap_or_else(|e| {
        panic!(
            "can't read {}: {e}. Run scripts/build-wasm.sh or set APPROVAL_WASM",
            path.display()
        )
    })
}

/// Which build `wasm()` is: `APPROVAL_WASM_KIND`, else the `BUILD_KIND`
/// file `scripts/build-wasm.sh` writes next to its output, else `unknown`.
pub fn wasm_kind() -> String {
    if let Ok(k) = std::env::var("APPROVAL_WASM_KIND") {
        return k;
    }
    std::fs::read_to_string(wasm_path().with_file_name("BUILD_KIND"))
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|_| "unknown".into())
}

/// A helper contract from `res/` (built by `scripts/build-res.sh`).
pub fn res(name: &str) -> Vec<u8> {
    let path = sandbox_dir().join(format!("res/wasm/{name}.wasm"));
    std::fs::read(&path).unwrap_or_else(|e| {
        panic!("can't read {}: {e}. Run scripts/build-res.sh", path.display())
    })
}

pub fn sha256(bytes: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    sha2::Sha256::digest(bytes).into()
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// NEAR's `code_hash`: base58 of the sha256 of the code.
pub fn code_hash_b58(code: &[u8]) -> String {
    bs58::encode(sha256(code)).into_string()
}

/// Checks `value` against the committed `results/<id>.json` (the observed
/// outcome of a test that records rather than asserts) and fails on any
/// difference, writing what it saw to `results/<id>.observed.json`. With
/// `SANDBOX_RECORD=1` it rewrites the committed file instead: the explicit
/// update mode after a reviewed runtime change. Keep values free of block
/// heights and other run-specific data, so they differ only if the
/// behaviour changed.
pub fn record(id: &str, value: Value) {
    let dir = sandbox_dir().join("results");
    std::fs::create_dir_all(&dir).unwrap();
    let mut v = value;
    if let Value::Object(m) = &mut v {
        m.insert("wasm_kind".into(), json!(wasm_kind()));
        m.insert("near_sandbox".into(), json!(near_workspaces_sandbox_version()));
    }
    let text = serde_json::to_string_pretty(&v).unwrap() + "\n";
    eprintln!("{id}: {v}");
    let path = dir.join(format!("{id}.json"));
    if std::env::var("SANDBOX_RECORD").as_deref() == Ok("1") {
        std::fs::write(&path, &text).unwrap();
        return;
    }
    let committed = std::fs::read_to_string(&path).unwrap_or_default();
    if committed != text {
        std::fs::write(dir.join(format!("{id}.observed.json")), &text).unwrap();
        panic!(
            "{id}: observed outcome differs from results/{id}.json \
             (rerun with SANDBOX_RECORD=1 to accept it)\n--- committed\n{committed}--- observed\n{text}"
        );
    }
}

pub fn near_workspaces_sandbox_version() -> String {
    std::env::var("NEAR_SANDBOX_VERSION").unwrap_or_else(|_| "2.13.4 (near-sandbox 0.3.16 default)".into())
}

pub async fn sandbox() -> Worker<Sandbox> {
    near_workspaces::sandbox().await.expect("start near-sandbox")
}

/// The text of a failed call: either the transaction was rejected before
/// execution (`Err`) or it executed and failed. Panics if it succeeded.
pub fn failure(result: near_workspaces::Result<ExecutionFinalResult>) -> String {
    match result {
        Err(e) => format!("{e:?}"),
        Ok(outcome) => match outcome.into_result() {
            Ok(success) => panic!("expected failure, got success: {:?}", success.logs()),
            Err(failure) => format!("{failure:?}"),
        },
    }
}

pub fn assert_fails_with(result: near_workspaces::Result<ExecutionFinalResult>, needle: &str) {
    let text = failure(result);
    assert!(text.contains(needle), "expected {needle:?} in {text}");
}

/// The failure text of an executed transaction (`Ok` from RPC, failed on chain).
pub fn executed_failure(result: near_workspaces::Result<ExecutionFinalResult>) -> (String, ExecutionFinalResult) {
    let outcome = result.expect("transaction was rejected before execution");
    assert!(outcome.is_failure(), "expected failure: {:?}", outcome.logs());
    let text = format!("{:?}", outcome.clone().into_result().unwrap_err());
    (text, outcome)
}

pub fn ok(result: near_workspaces::Result<ExecutionFinalResult>) -> ExecutionFinalResult {
    let outcome = result.expect("rpc");
    assert!(outcome.is_success(), "{:?}", outcome.failures());
    outcome
}

/// `ok` for a call whose outcome isn't needed.
pub fn must(result: near_workspaces::Result<ExecutionFinalResult>) {
    let _ = ok(result);
}

pub fn events(outcome: &ExecutionFinalResult) -> Vec<Value> {
    outcome
        .logs()
        .iter()
        .filter_map(|l| l.strip_prefix("EVENT_JSON:"))
        .map(|j| serde_json::from_str(j).unwrap())
        .collect()
}

pub fn single_event(outcome: &ExecutionFinalResult) -> Value {
    let all = events(outcome);
    assert_eq!(all.len(), 1, "expected one event: {all:?}");
    all.into_iter().next().unwrap()
}

/// Longest log total of any receipt in `outcome`.
pub fn max_receipt_log_len(outcome: &ExecutionFinalResult) -> usize {
    outcome
        .receipt_outcomes()
        .iter()
        .map(|r| r.logs.iter().map(String::len).sum::<usize>())
        .max()
        .unwrap_or(0)
}

/// The receipt outcomes executed on `executor`.
pub fn receipts_on<'a>(outcome: &'a ExecutionFinalResult, executor: &AccountId) -> Vec<&'a ExecutionOutcome> {
    outcome
        .receipt_outcomes()
        .iter()
        .filter(|r| &r.executor_id == executor)
        .collect()
}

/// Logs of every receipt executed on `executor`, success or failure.
pub fn logs_on(outcome: &ExecutionFinalResult, executor: &AccountId) -> Vec<String> {
    receipts_on(outcome, executor)
        .into_iter()
        .flat_map(|r| r.logs.clone())
        .collect()
}

/// A new subaccount of root with its own fresh ed25519 full-access key
/// (near-workspaces would otherwise reuse root's key for every account, so
/// accounts' full-access keys would coincide).
pub async fn subaccount(worker: &Worker<Sandbox>, name: &str, near: u128) -> Account {
    worker
        .root_account()
        .unwrap()
        .create_subaccount(name)
        .keys(SecretKey::from_random(KeyType::ED25519))
        .initial_balance(NearToken::from_near(near))
        .transact()
        .await
        .unwrap()
        .into_result()
        .unwrap()
}

/// Adds a new key with `permission` to `account` and returns a handle that
/// signs for `account` with it.
pub async fn add_key(
    worker: &Worker<Sandbox>,
    account: &Account,
    permission: AccessKey,
    key_type: KeyType,
) -> Account {
    let sk = SecretKey::from_random(key_type);
    account
        .batch(account.id())
        .add_key(sk.public_key(), permission)
        .transact()
        .await
        .unwrap()
        .into_result()
        .unwrap();
    Account::from_secret_key(account.id().clone(), sk, worker)
}

/// Gives `account` a function-call access key for `methods` on `contract`
/// and returns a handle that signs with that key.
pub async fn function_call_key(
    worker: &Worker<Sandbox>,
    account: &Account,
    contract: &AccountId,
    methods: &[&str],
    key_type: KeyType,
) -> Account {
    add_key(
        worker,
        account,
        AccessKey::function_call_access(contract, methods, None),
        key_type,
    )
    .await
}

pub fn pk(account: &Account) -> PublicKey {
    account.secret_key().public_key()
}

/// Creates `name`, deploys the approval wasm and calls `new(owner)` from the
/// contract account itself.
pub async fn deploy_init(worker: &Worker<Sandbox>, name: &str, owner: &AccountId) -> Contract {
    let account = subaccount(worker, name, 50).await;
    let contract = account.deploy(&wasm()).await.unwrap().into_result().unwrap();
    contract
        .call("new")
        .args_json(json!({ "owner_id": owner }))
        .transact()
        .await
        .unwrap()
        .into_result()
        .unwrap();
    contract
}

pub struct Setup {
    pub worker: Worker<Sandbox>,
    pub contract: Contract,
    pub owner: Account,
    /// The agent account, signing with its full-access key.
    pub agent_account: Account,
    /// The agent account, signing with its registered function-call key.
    pub agent: Account,
    /// The approver account, signing with its full-access key.
    pub approver_account: Account,
    pub approver: Account,
}

/// Deploys and initializes the contract, then registers one agent and one
/// approver, each signing with a function-call key scoped to the contract
/// (DEP-1.4). `long_names` uses 64-character account ids.
pub async fn setup(long_names: bool, key_type: KeyType) -> Setup {
    setup_on(sandbox().await, long_names, key_type).await
}

pub async fn setup_on(worker: Worker<Sandbox>, long_names: bool, key_type: KeyType) -> Setup {
    let root_len = worker.root_account().unwrap().id().as_str().len();
    let name = |c: char, short: &str| {
        if long_names {
            c.to_string().repeat(64 - root_len - 1)
        } else {
            short.to_string()
        }
    };
    let owner = subaccount(&worker, "owner", 10).await;
    let contract = deploy_init(&worker, "approvals", owner.id()).await;
    let agent_account = subaccount(&worker, &name('a', "agent"), 10).await;
    let approver_account = subaccount(&worker, &name('b', "approver"), 10).await;
    let agent = function_call_key(&worker, &agent_account, contract.id(), &["request_action"], key_type).await;
    let approver = function_call_key(
        &worker,
        &approver_account,
        contract.id(),
        &["approve", "reject"],
        key_type,
    )
    .await;
    for (method, account) in [("add_agent", &agent), ("add_approver", &approver)] {
        must(owner
            .call(contract.id(), method)
            .args_json(json!({ "account_id": account.id(), "public_key": pk(account) }))
            .transact()
            .await);
    }
    Setup {
        worker,
        contract,
        owner,
        agent_account,
        agent,
        approver_account,
        approver,
    }
}

impl Setup {
    pub async fn request(&self, action: &str) -> near_workspaces::Result<ExecutionFinalResult> {
        self.agent
            .call(self.contract.id(), "request_action")
            .args_json(json!({ "action": action }))
            .max_gas()
            .transact()
            .await
    }

    pub async fn approve(&self, id: u64, action: &str) -> near_workspaces::Result<ExecutionFinalResult> {
        self.approver
            .call(self.contract.id(), "approve")
            .args_json(json!({ "request_id": id, "action": action }))
            .max_gas()
            .transact()
            .await
    }

    pub async fn view(&self, method: &str, args: Value) -> Value {
        view(&self.contract, method, args).await
    }

    /// Counters and the agent principal: what RT-REVERT and RT-BATCH compare
    /// before and after a failure.
    pub async fn snapshot(&self) -> Value {
        json!({
            "request_count": self.view("get_request_count", json!({})).await,
            "approval_count": self.view("get_approval_count", json!({})).await,
            "agent": self.view("get_principal", json!({ "public_key": pk(&self.agent) })).await,
            "approvals": self.view("get_approvals", json!({})).await,
        })
    }
}

pub async fn view(contract: &Contract, method: &str, args: Value) -> Value {
    contract
        .view(method)
        .args_json(args)
        .await
        .unwrap_or_else(|e| panic!("view {method}: {e:?}"))
        .json()
        .unwrap()
}

/// `(height, timestamp_ns)` of the block a receipt outcome was recorded in:
/// the `now()` the contract saw while executing it.
pub async fn block_time(worker: &Worker<Sandbox>, r: &ExecutionOutcome) -> (u64, u64) {
    let block = worker.view_block().block_hash(r.block_hash).await.unwrap();
    (block.height(), block.timestamp())
}

pub fn all_view_methods() -> [&'static str; 9] {
    [
        "get_owner",
        "get_principal",
        "get_request",
        "get_request_count",
        "get_approval",
        "get_rejection",
        "get_revocation",
        "get_approvals",
        "get_approval_count",
    ]
}

/// The 16 `#[near]` methods at the pin (F-15: SH-10/SH-11 said 13).
pub const CHANGE_METHODS: [&str; 7] = [
    "new",
    "add_agent",
    "add_approver",
    "revoke_key",
    "request_action",
    "approve",
    "reject",
];

/// Function exports of a wasm module (export section, kind 0), in order.
/// A minimal parser: enough for SH-10/SH-11 on the wasm under test.
pub fn function_exports(wasm: &[u8]) -> Vec<String> {
    fn leb(b: &[u8], i: &mut usize) -> u64 {
        let (mut v, mut shift) = (0u64, 0);
        loop {
            let byte = b[*i];
            *i += 1;
            v |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return v;
            }
            shift += 7;
        }
    }
    assert_eq!(&wasm[..4], b"\0asm", "not a wasm module");
    let mut i = 8;
    let mut out = Vec::new();
    while i < wasm.len() {
        let id = wasm[i];
        i += 1;
        let len = leb(wasm, &mut i) as usize;
        let end = i + len;
        if id == 7 {
            let n = leb(wasm, &mut i);
            for _ in 0..n {
                let l = leb(wasm, &mut i) as usize;
                let name = String::from_utf8(wasm[i..i + l].to_vec()).unwrap();
                i += l;
                let kind = wasm[i];
                i += 1;
                let _index = leb(wasm, &mut i);
                if kind == 0 {
                    out.push(name);
                }
            }
        }
        i = end;
    }
    out
}

/// Runs `goal` in scryer-prolog with `verifier_rules.pl` and `facts` loaded;
/// returns stdout. Requires `scryer-prolog` on PATH (or `SCRYER`).
pub fn prolog(facts: &str, goal: &str) -> String {
    let rules = sandbox_dir().join("../prolog/verification/verifier_rules.pl").canonicalize().unwrap();
    let dir = std::env::temp_dir().join(format!("m6-prolog-{}-{}", std::process::id(), rand_suffix()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("facts.pl");
    std::fs::write(
        &file,
        format!(
            ":- use_module(library(iso_ext)).\n:- use_module(library(format)).\n:- use_module(library(lists)).\n:- use_module('{}').\n{facts}",
            rules.display()
        ),
    )
    .unwrap();
    let bin = std::env::var("SCRYER").unwrap_or_else(|_| "scryer-prolog".into());
    let out = std::process::Command::new(&bin)
        .arg(&file)
        .arg("-g")
        .arg(format!("({goal}) -> halt(0) ; halt(1)"))
        .stdin(std::process::Stdio::null())
        .output()
        .unwrap_or_else(|e| panic!("{bin}: {e} (install scryer-prolog, see tools/versions.env SCRYER)"));
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    assert!(out.status.success(), "prolog failed: {stdout}{}", String::from_utf8_lossy(&out.stderr));
    stdout
}

fn rand_suffix() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64
}
