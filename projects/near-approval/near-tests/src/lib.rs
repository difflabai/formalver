//! Shared harness for the near-sdk shell tests (strategy.md sections 5.6-5.8, 9; M3).
//!
//! Upstream: difflabai/trust-framework `contracts/approval/contract/src/lib.rs`
//!           and `contracts/approval/core/src/lib.rs`
//! Pin:      8635ca7b8b1d64bb226eb0b3b3a35779fcbf461b (contract code = PR #15 head 3426c92)
//! sha256:   contract/src/lib.rs 7033fc7acf27d8c678c0f28167ed8cd01ad0c851382d83a661d8f96b83357900
//!           core/src/lib.rs     f5d72cc7bedd0866dfb7891246999315338410f06be00210e3ffd21452ea0d0c
//! Covers:   every `#[near]` method of `ApprovalContract`, its `Store` impl, `caller()`,
//!           `now()`, `ok()`, the views and event payloads, run under near-sdk's
//!           mocked runtime (`unit-testing`, real `VMLogic` from near-vm-runner).
//!
//! The contract is driven exactly as the runtime drives it: every call starts
//! from storage (`state_read`), and a successful call ends with `state_write`
//! and a drop of the struct (which flushes the `LookupMap` caches). A failed
//! call (a panic) is discarded together with every write it made, as the
//! runtime reverts a failed receipt (ASM-ATOMIC): the storage map from before
//! the call is reinstalled.
//!
//! Expected values are built here, from the README's field names and the core's
//! own results on a `MemStore` (never from the contract's view types), so a
//! renamed field or a wrong conversion shows up as a difference.
//!
//! Simplifications / trusted items:
//! - `#[init]`, `#[private]` and the JSON argument wrappers exist only in the
//!   wasm build; on the host the methods are called as plain Rust functions
//!   (SH-9, SH-10 and the argument half of SH-8 are sandbox properties, M6).
//! - α of the contract reads its `Store` impl over the fixed key universe
//!   [`keys`]; `tests/store_diff.rs` additionally checks that the raw storage
//!   holds no key outside what α accounts for, so nothing is hidden from it.

use approval_contract::ApprovalContract;
use approval_core::{
    ActionRequest, ApprovalError, ApprovalProof, BlockTime, MemStore, Principal, ProofRevocations,
    RequestStatus, Role, Store,
};
use near_sdk::serde_json::{json, Value};
use near_sdk::test_utils::VMContextBuilder;
use near_sdk::{env, test_vm_config, AccountId, CurveType, MockedBlockchain, PublicKey};
use near_sdk::{NearToken, RuntimeFeesConfig};
use std::cell::Cell;
use std::collections::HashMap;
use std::panic::{self, AssertUnwindSafe};

pub use near_sdk::serde_json;

pub type Request = ActionRequest<AccountId, PublicKey>;
pub type Proof = ApprovalProof<AccountId, PublicKey>;
pub type Mem = MemStore<AccountId, PublicKey>;
pub type Storage = HashMap<Vec<u8>, Vec<u8>>;

// ---------------------------------------------------------------------------
// Universe: 4 accounts and 4 real keys (section 9)
// ---------------------------------------------------------------------------

pub fn contract_id() -> AccountId {
    "approvals.near".parse().unwrap()
}

/// `accounts()[0]` is the owner. The last one is 64 characters long, the
/// maximum, which RES-1/RES-2 need.
pub fn accounts() -> [AccountId; 4] {
    [
        "owner.near".parse().unwrap(),
        "alice.near".parse().unwrap(),
        "bob.near".parse().unwrap(),
        long_account('c'),
    ]
}

pub fn owner() -> AccountId {
    accounts()[0].clone()
}

/// A valid account id of exactly 64 characters.
pub fn long_account(c: char) -> AccountId {
    let s = format!("{}.near", c.to_string().repeat(59));
    assert_eq!(s.len(), 64);
    s.parse().unwrap()
}

pub fn ed25519(seed: u8) -> PublicKey {
    PublicKey::from_parts(CurveType::ED25519, vec![seed; 32]).unwrap()
}

pub fn secp256k1(seed: u8) -> PublicKey {
    PublicKey::from_parts(CurveType::SECP256K1, vec![seed; 64]).unwrap()
}

/// ML-DSA-65 (FIPS 204) public key: 1952 bytes. near-sdk-core 4.2.3 accepts
/// it as a third curve (nearcore 2.13, protocol 85). See F-17.
pub fn mldsa65(seed: u8) -> PublicKey {
    PublicKey::from_parts(CurveType::MLDSA65, vec![seed; 1952]).unwrap()
}

/// Two ed25519 and two secp256k1 keys.
pub fn keys() -> [PublicKey; 4] {
    [ed25519(1), secp256k1(2), ed25519(3), secp256k1(4)]
}

pub fn pk_str(k: &PublicKey) -> String {
    String::from(k)
}

// ---------------------------------------------------------------------------
// Mocked runtime
// ---------------------------------------------------------------------------

/// Who calls and when (the five runtime inputs `caller()` and `now()` read).
#[derive(Clone, Debug)]
pub struct Ctx {
    pub predecessor: AccountId,
    pub signer: AccountId,
    pub signer_pk: PublicKey,
    pub at: BlockTime,
}

impl Ctx {
    pub fn new(predecessor: &AccountId, signer: &AccountId, pk: &PublicKey, at: BlockTime) -> Self {
        Self {
            predecessor: predecessor.clone(),
            signer: signer.clone(),
            signer_pk: pk.clone(),
            at,
        }
    }

    /// A direct call: the signer is the predecessor.
    pub fn signed(account: &AccountId, pk: &PublicKey, at: BlockTime) -> Self {
        Self::new(account, account, pk, at)
    }

    pub fn caller(&self) -> approval_core::Caller<AccountId, PublicKey> {
        approval_core::Caller {
            predecessor: self.predecessor.clone(),
            signer: self.signer.clone(),
            signer_key: self.signer_pk.clone(),
        }
    }
}

pub fn at(height: u64, ns: u64) -> BlockTime {
    BlockTime {
        height,
        timestamp_ns: ns,
    }
}

/// Replaces the mocked blockchain with a fresh one for `ctx`, holding
/// `storage`. Logs start empty.
pub fn install(ctx: &Ctx, storage: Storage) {
    let context = VMContextBuilder::new()
        .current_account_id(contract_id())
        .predecessor_account_id(ctx.predecessor.clone())
        .signer_account_id(ctx.signer.clone())
        .signer_account_pk(ctx.signer_pk.clone())
        .block_height(ctx.at.height)
        .block_timestamp(ctx.at.timestamp_ns)
        .attached_deposit(NearToken::from_yoctonear(0))
        .build();
    env::set_blockchain_interface(MockedBlockchain::new(
        context,
        cached(test_vm_config),
        cached(RuntimeFeesConfig::test),
        vec![],
        storage,
        Default::default(),
        None,
    ));
}

/// `f()`, computed once per thread. `test_vm_config()` builds a whole
/// `RuntimeConfigStore` each time, which dominates a step's cost otherwise.
fn cached<T: Clone + 'static>(f: fn() -> T) -> T {
    use std::any::{Any, TypeId};
    thread_local! {
        static CACHE: std::cell::RefCell<HashMap<TypeId, Box<dyn Any>>> = Default::default();
    }
    CACHE.with(|c| {
        c.borrow_mut()
            .entry(TypeId::of::<T>())
            .or_insert_with(|| Box::new(f()))
            .downcast_ref::<T>()
            .unwrap()
            .clone()
    })
}

/// The current storage map (taken, then reinstalled under the same context).
pub fn storage_snapshot(ctx: &Ctx) -> Storage {
    let s = take_storage();
    install(ctx, s.clone());
    s
}

pub fn take_storage() -> Storage {
    near_sdk::mock::with_mocked_blockchain(|b| b.take_storage())
}

pub fn logs() -> Vec<String> {
    near_sdk::test_utils::get_logs()
}

thread_local! {
    static EXPECT_PANIC: Cell<bool> = const { Cell::new(false) };
}

/// Silences the default panic hook while a contract call is expected to
/// panic, so hundreds of thousands of expected failures don't flood stderr.
/// Every other panic (a failing assertion) is reported as usual.
pub fn quiet_expected_panics() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let default = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            if !EXPECT_PANIC.with(|e| e.get()) {
                default(info)
            }
        }));
    });
}

/// `catch_unwind` with the panic hook silenced (see `quiet_expected_panics`).
pub fn catch_quiet<R>(f: impl FnOnce() -> R) -> std::thread::Result<R> {
    EXPECT_PANIC.with(|e| e.set(true));
    let r = panic::catch_unwind(AssertUnwindSafe(f));
    EXPECT_PANIC.with(|e| e.set(false));
    r
}

/// SH-3: the payload format of a contract panic under near-sdk 5.29.1's
/// mocked runtime. `env::panic_str(m)` calls the `panic_utf8` host function,
/// `VMLogic` returns `HostError::GuestPanic { panic_msg: m }`, and the mock
/// unwraps it, so the payload is
/// `called `Result::unwrap()` on an `Err` value: HostError(GuestPanic { panic_msg: "<m>" })`
/// with `<m>` in Rust `Debug` escaping. On-chain the receipt fails with
/// `Smart contract panicked: <m>`.
pub const PANIC_PREFIX: &str =
    "called `Result::unwrap()` on an `Err` value: HostError(GuestPanic { panic_msg: \"";
pub const PANIC_SUFFIX: &str = "\" })";

/// Extracts `panic_msg` from a contract panic payload, or returns the whole
/// payload, marked, if it has another shape (a test then fails on it).
pub fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    let raw = if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else {
        return "<non-string panic payload>".into();
    };
    match raw
        .strip_prefix(PANIC_PREFIX)
        .and_then(|r| r.strip_suffix(PANIC_SUFFIX))
    {
        // The core's messages are plain ASCII without quotes or backslashes,
        // so Debug escaping is the identity on them; anything else is kept
        // escaped and will not compare equal.
        Some(m) => m.to_string(),
        None => format!("<unexpected panic payload: {raw}>"),
    }
}

/// Outcome of one contract call.
#[derive(Debug)]
pub struct Outcome<R> {
    /// The return value, or the extracted panic message.
    pub result: Result<R, String>,
    /// Logs of the call, including the logs of a call that failed (they
    /// survive in a failed outcome on-chain too, ASM-ATOMIC).
    pub logs: Vec<String>,
    /// Storage after the call: written back on success, unchanged on failure.
    pub storage: Storage,
}

/// Runs one change call the way the runtime does: fresh mocked blockchain for
/// `ctx` over `storage`, `state_read`, the method, then `state_write` and a
/// drop on success. On a panic every write is discarded.
pub fn call<R>(
    ctx: &Ctx,
    storage: Storage,
    f: impl FnOnce(&mut ApprovalContract) -> R,
) -> Outcome<R> {
    let before = storage.clone();
    install(ctx, storage);
    let mut c: ApprovalContract = env::state_read().expect("contract state");
    let r = catch_quiet(|| f(&mut c));
    let logs = logs();
    match r {
        Ok(v) => {
            env::state_write(&c);
            drop(c); // flushes the LookupMap write caches
            Outcome {
                result: Ok(v),
                logs,
                storage: take_storage(),
            }
        }
        Err(payload) => {
            // The runtime reverts a failed receipt. The struct may hold cached
            // writes; dropping it would flush them into storage we discard.
            drop(c);
            let _ = take_storage();
            Outcome {
                result: Err(panic_message(payload)),
                logs,
                storage: before,
            }
        }
    }
}

/// Runs a view (`&self`) on a contract freshly read from `storage`, and
/// checks it logged nothing.
pub fn view<R>(storage: &Storage, f: impl FnOnce(&ApprovalContract) -> R) -> R {
    let ctx = Ctx::signed(&accounts()[1], &keys()[0], at(1, 1));
    install(&ctx, storage.clone());
    let c: ApprovalContract = env::state_read().expect("contract state");
    let r = f(&c);
    assert!(logs().is_empty(), "a view logged: {:?}", logs());
    r
}

/// Deploys and initialises a contract with `owner` (called by the contract
/// account itself, as `#[private]` requires on-chain).
pub fn deploy(owner: &AccountId) -> Storage {
    let ctx = Ctx::signed(&contract_id(), &keys()[0], at(1, 1_000_000_000));
    install(&ctx, Storage::new());
    let c = ApprovalContract::new(owner.clone());
    assert!(logs().is_empty(), "new() must not log");
    env::state_write(&c);
    drop(c);
    take_storage()
}

// ---------------------------------------------------------------------------
// Operations, run on both the contract and the core over a MemStore
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum Op {
    AddAgent { account: AccountId, key: PublicKey },
    AddApprover { account: AccountId, key: PublicKey },
    Revoke { key: PublicKey },
    Request { action: String },
    Approve { id: u64, action: String },
    Reject { id: u64 },
}

/// What the core returned, as the shell must expose it.
#[derive(Clone, Debug, PartialEq)]
pub enum CoreOk {
    Added(Principal<AccountId>),
    Revoked(Principal<AccountId>),
    Requested(Request),
    Approved(Proof),
    Rejected(Request),
}

/// Applies `op` to the core over `mem` with the caller and time of `ctx`.
/// Owner methods pass the predecessor; request/approve/reject the full caller.
pub fn core_step(mem: &mut Mem, ctx: &Ctx, op: &Op) -> Result<CoreOk, ApprovalError> {
    let c = ctx.caller();
    match op {
        Op::AddAgent { account, key } => approval_core::add_principal(
            mem,
            &ctx.predecessor,
            key.clone(),
            account.clone(),
            Role::Agent,
        )
        .map(CoreOk::Added),
        Op::AddApprover { account, key } => approval_core::add_principal(
            mem,
            &ctx.predecessor,
            key.clone(),
            account.clone(),
            Role::Approver,
        )
        .map(CoreOk::Added),
        Op::Revoke { key } => {
            approval_core::revoke_key(mem, &ctx.predecessor, key, ctx.at).map(CoreOk::Revoked)
        }
        Op::Request { action } => {
            approval_core::request_action(mem, &c, action.clone(), ctx.at).map(CoreOk::Requested)
        }
        Op::Approve { id, action } => {
            approval_core::approve(mem, &c, *id, action, ctx.at).map(CoreOk::Approved)
        }
        Op::Reject { id } => approval_core::reject(mem, &c, *id, ctx.at).map(CoreOk::Rejected),
    }
}

/// Applies `op` through the contract's public method; the return value is
/// serialized to JSON (unit for the owner methods).
pub fn contract_step(ctx: &Ctx, storage: Storage, op: &Op) -> Outcome<Value> {
    let op = op.clone();
    call(ctx, storage, move |c| match op {
        Op::AddAgent { account, key } => {
            c.add_agent(account, key);
            Value::Null
        }
        Op::AddApprover { account, key } => {
            c.add_approver(account, key);
            Value::Null
        }
        Op::Revoke { key } => {
            c.revoke_key(key);
            Value::Null
        }
        Op::Request { action } => json!(c.request_action(action)),
        Op::Approve { id, action } => serde_json::to_value(c.approve(id, action)).unwrap(),
        Op::Reject { id } => serde_json::to_value(c.reject(id)).unwrap(),
    })
}

// ---------------------------------------------------------------------------
// Expected JSON (README field names; written here, not taken from the contract)
// ---------------------------------------------------------------------------

pub fn role_json(r: Role) -> Value {
    json!(match r {
        Role::Agent => "agent",
        Role::Approver => "approver",
    })
}

pub fn status_json(s: RequestStatus) -> Value {
    json!(match s {
        RequestStatus::Pending => "pending",
        RequestStatus::Approved => "approved",
        RequestStatus::Rejected => "rejected",
        RequestStatus::Void => "void",
    })
}

pub fn time_json(t: Option<BlockTime>) -> Value {
    match t {
        None => Value::Null,
        Some(t) => json!({ "block": t.height, "ns": t.timestamp_ns.to_string() }),
    }
}

pub fn request_json(r: &Request, status: RequestStatus) -> Value {
    json!({
        "request_id": r.id,
        "agent_account_id": r.agent_account_id,
        "agent_public_key": pk_str(&r.agent_key),
        "agent_registration_id": r.agent_registration_id,
        "action": r.action,
        "requested_at_block": r.requested_at.height,
        "requested_at_ns": r.requested_at.timestamp_ns.to_string(),
        "status": status_json(status),
    })
}

pub fn proof_json(p: &Proof, rev: ProofRevocations) -> Value {
    json!({
        "approval_index": p.approval_index,
        "request_id": p.request_id,
        "action": p.action,
        "agent_account_id": p.agent_account_id,
        "agent_public_key": pk_str(&p.agent_key),
        "agent_registration_id": p.agent_registration_id,
        "requested_at_block": p.requested_at.height,
        "requested_at_ns": p.requested_at.timestamp_ns.to_string(),
        "approver_account_id": p.approver_account_id,
        "approver_public_key": pk_str(&p.approver_key),
        "approver_registration_id": p.approver_registration_id,
        "approved_at_block": p.approved_at.height,
        "approved_at_ns": p.approved_at.timestamp_ns.to_string(),
        "agent_key_revoked_at": time_json(rev.agent),
        "approver_key_revoked_at": time_json(rev.approver),
    })
}

/// `None` unless `r` is rejected.
pub fn rejection_json(r: &Request) -> Option<Value> {
    let x = r.rejection.as_ref()?;
    Some(json!({
        "request_id": r.id,
        "action": r.action,
        "agent_account_id": r.agent_account_id,
        "agent_public_key": pk_str(&r.agent_key),
        "agent_registration_id": r.agent_registration_id,
        "requested_at_block": r.requested_at.height,
        "requested_at_ns": r.requested_at.timestamp_ns.to_string(),
        "approver_account_id": x.approver_account_id,
        "approver_public_key": pk_str(&x.approver_key),
        "approver_registration_id": x.approver_registration_id,
        "rejected_at_block": x.rejected_at.height,
        "rejected_at_ns": x.rejected_at.timestamp_ns.to_string(),
    }))
}

pub fn principal_json(p: &Principal<AccountId>) -> Value {
    json!({
        "account_id": p.account_id,
        "role": role_json(p.role),
        "registration_id": p.registration_id,
        "pending": p.pending,
    })
}

/// The NEP-297 envelope, as one JSON value.
pub fn event_json(event: &str, data: Value) -> Value {
    json!({ "standard": "trust_approval", "version": "1.0.0", "event": event, "data": data })
}

/// The exact log line: `EVENT_JSON:` and the envelope fields in README order,
/// with `data` serialized by `serde_json` in struct field order.
pub fn event_line(event: &str, data_compact: &str) -> String {
    format!(
        "EVENT_JSON:{{\"standard\":\"trust_approval\",\"version\":\"1.0.0\",\"event\":\"{event}\",\"data\":{data_compact}}}"
    )
}

/// Parses one log line as a NEP-297 event, failing on any other shape.
pub fn parse_event(line: &str) -> Value {
    let body = line
        .strip_prefix("EVENT_JSON:")
        .unwrap_or_else(|| panic!("not a NEP-297 log: {line}"));
    serde_json::from_str(body).unwrap_or_else(|e| panic!("bad event JSON ({e}): {line}"))
}

/// The return value and event a successful core step must produce through
/// the shell: `(return value, event name, event data)`. `mem` is the store
/// after the step.
pub fn expected_effect(mem: &Mem, ctx: &Ctx, op: &Op, ok: &CoreOk) -> (Value, &'static str, Value) {
    match (op, ok) {
        (Op::AddAgent { key, .. } | Op::AddApprover { key, .. }, CoreOk::Added(p)) => (
            Value::Null,
            "key_added",
            json!({
                "public_key": pk_str(key),
                "account_id": p.account_id,
                "role": role_json(p.role),
                "registration_id": p.registration_id,
            }),
        ),
        (Op::Revoke { key }, CoreOk::Revoked(p)) => (
            Value::Null,
            "key_revoked",
            json!({
                "public_key": pk_str(key),
                "account_id": p.account_id,
                "role": role_json(p.role),
                "registration_id": p.registration_id,
                "revoked_at_block": ctx.at.height,
                "revoked_at_ns": ctx.at.timestamp_ns.to_string(),
                "voided_pending": p.pending,
            }),
        ),
        (Op::Request { .. }, CoreOk::Requested(r)) => {
            let status = approval_core::status_of(mem, r);
            assert_eq!(status, RequestStatus::Pending, "a new request is pending");
            (json!(r.id), "approval_requested", request_json(r, status))
        }
        (Op::Approve { .. }, CoreOk::Approved(p)) => {
            let v = proof_json(p, approval_core::proof_revocations(mem, p));
            (v.clone(), "action_approved", v)
        }
        (Op::Reject { .. }, CoreOk::Rejected(r)) => {
            let v = rejection_json(r).expect("a rejected request has a rejection");
            (v.clone(), "action_rejected", v)
        }
        _ => panic!("core result {ok:?} does not match {op:?}"),
    }
}

// ---------------------------------------------------------------------------
// The abstraction α (ST-3/ST-4): the store as plain data
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
pub struct Abs {
    pub owner: AccountId,
    /// Sorted by the key's Borsh bytes.
    pub principals: Vec<(Vec<u8>, Principal<AccountId>)>,
    pub requests: Vec<Request>,
    pub log: Vec<u64>,
    pub registration_count: u64,
    /// Sorted by registration id.
    pub revocations: Vec<(u64, BlockTime)>,
}

fn borsh_key(k: &PublicKey) -> Vec<u8> {
    near_sdk::borsh::to_vec(k).unwrap()
}

/// α of a `MemStore`, from its fields. `MemStore` keeps the first write of a
/// revocation id and the contract the last (F-16); INV-12 makes ids unique,
/// which this asserts.
pub fn abs_mem(m: &Mem) -> Abs {
    let mut principals: Vec<_> = m
        .principals
        .iter()
        .map(|(k, p)| (borsh_key(k), p.clone()))
        .collect();
    principals.sort_by(|a, b| a.0.cmp(&b.0));
    let mut revocations = m.revocations.clone();
    revocations.sort_by_key(|(g, _)| *g);
    assert!(
        revocations.windows(2).all(|w| w[0].0 != w[1].0),
        "a registration id was revoked twice (INV-12)"
    );
    Abs {
        owner: m.owner.clone(),
        principals,
        requests: m.requests.clone(),
        log: m.approval_log.clone(),
        registration_count: m.registration_count,
        revocations,
    }
}

/// α of any store, read through the `Store` trait over the key universe
/// `universe`: registrations ids `0..registration_count`, request ids
/// `0..request_count`, log indices `0..approval_count`.
pub fn abs_store<S: Store<AccountId, PublicKey>>(s: &S, universe: &[PublicKey]) -> Abs {
    let mut principals: Vec<_> = universe
        .iter()
        .filter_map(|k| s.principal(k).map(|p| (borsh_key(k), p)))
        .collect();
    principals.sort_by(|a, b| a.0.cmp(&b.0));
    let requests = (0..s.request_count())
        .map(|i| {
            s.request(i)
                .unwrap_or_else(|| panic!("request {i} < count missing"))
        })
        .collect();
    let log = (0..s.approval_count())
        .map(|j| {
            s.approved_request_id(j)
                .unwrap_or_else(|| panic!("log entry {j} < count missing"))
        })
        .collect();
    let revocations = (0..s.registration_count())
        .filter_map(|g| s.revocation(g).map(|t| (g, t)))
        .collect();
    Abs {
        owner: s.owner().clone(),
        principals,
        requests,
        log,
        registration_count: s.registration_count(),
        revocations,
    }
}

/// α of the contract held in `storage`.
pub fn abs_contract(storage: &Storage, universe: &[PublicKey]) -> Abs {
    view(storage, |c| abs_store(c, universe))
}

// ---------------------------------------------------------------------------
// Storage layout (ST-5, ST-6)
// ---------------------------------------------------------------------------

/// The top-level `STATE` value, decoded field by field. A mirror of
/// `ApprovalContract`'s Borsh layout as the README and the struct definition
/// describe it; `tests/shell.rs` checks it round-trips the real struct.
#[derive(
    near_sdk::borsh::BorshSerialize, near_sdk::borsh::BorshDeserialize, Clone, Debug, PartialEq,
)]
#[borsh(crate = "near_sdk::borsh")]
pub struct StateMirror {
    pub owner: String,
    pub principals_prefix: Vec<u8>,
    pub requests_prefix: Vec<u8>,
    pub request_count: u64,
    pub approval_log_prefix: Vec<u8>,
    pub approval_count: u64,
    pub registration_count: u64,
    pub revocations_prefix: Vec<u8>,
}

pub const STATE_KEY: &[u8] = b"STATE";

pub fn state_of(storage: &Storage) -> StateMirror {
    let bytes = storage.get(STATE_KEY).expect("STATE present");
    near_sdk::borsh::from_slice(bytes).expect("STATE decodes as StateMirror")
}

/// The exact set of storage keys a contract with abstraction `a` must hold:
/// `STATE`, and `prefix ‖ borsh(key)` for every entry of each map (ST-5).
pub fn expected_keys(a: &Abs, st: &StateMirror) -> Vec<Vec<u8>> {
    let cat = |p: &[u8], k: Vec<u8>| [p.to_vec(), k].concat();
    let b = |x: u64| near_sdk::borsh::to_vec(&x).unwrap();
    let mut keys = vec![STATE_KEY.to_vec()];
    keys.extend(
        a.principals
            .iter()
            .map(|(k, _)| cat(&st.principals_prefix, k.clone())),
    );
    keys.extend((0..a.requests.len() as u64).map(|i| cat(&st.requests_prefix, b(i))));
    keys.extend((0..a.log.len() as u64).map(|j| cat(&st.approval_log_prefix, b(j))));
    keys.extend(
        a.revocations
            .iter()
            .map(|(g, _)| cat(&st.revocations_prefix, b(*g))),
    );
    keys.sort();
    keys
}

pub fn sorted_keys(storage: &Storage) -> Vec<Vec<u8>> {
    let mut k: Vec<_> = storage.keys().cloned().collect();
    k.sort();
    k
}

// ---------------------------------------------------------------------------
// Random source
// ---------------------------------------------------------------------------

/// xorshift64*: deterministic, dependency-free.
pub struct Rng(pub u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    pub fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
    pub fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }
}

pub fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .map(|v| {
            v.parse()
                .unwrap_or_else(|_| panic!("{name} must be a number"))
        })
        .unwrap_or(default)
}

// ---------------------------------------------------------------------------
// Differential step and view check (shared by store_diff.rs and shell.rs)
// ---------------------------------------------------------------------------

/// SH-7: every view of the contract in `storage` equals the core's reads on `mem`.
pub fn check_views(storage: &Storage, mem: &Mem, rng: &mut Rng, ctx: &str) {
    let ks = keys();
    let n = mem.request_count();
    let g = mem.registration_count();
    let (f, l) = (
        [
            None,
            Some(0),
            Some(1),
            Some(rng.below(n + 2)),
            Some(u64::MAX),
        ][rng.below(5) as usize],
        [None, Some(0), Some(1), Some(rng.below(120)), Some(u64::MAX)][rng.below(5) as usize],
    );
    let got = view(storage, |c| {
        let mut v = vec![
            json!(c.get_owner()),
            json!(c.get_request_count()),
            json!(c.get_approval_count()),
        ];
        for i in 0..=n {
            v.push(serde_json::to_value(c.get_request(i)).unwrap());
            v.push(serde_json::to_value(c.get_approval(i)).unwrap());
            v.push(serde_json::to_value(c.get_rejection(i)).unwrap());
        }
        for r in 0..=g {
            v.push(serde_json::to_value(c.get_revocation(r)).unwrap());
        }
        for k in &ks {
            v.push(serde_json::to_value(c.get_principal(k.clone())).unwrap());
        }
        v.push(serde_json::to_value(c.get_approvals(None, None)).unwrap());
        v.push(serde_json::to_value(c.get_approvals(f, l)).unwrap());
        v
    });
    let proof = |p: approval_core::ApprovalProof<AccountId, PublicKey>| {
        proof_json(&p, approval_core::proof_revocations(mem, &p))
    };
    let mut want = vec![
        json!(mem.owner),
        json!(mem.request_count()),
        json!(mem.approval_count()),
    ];
    for i in 0..=n {
        want.push(match mem.request(i) {
            Some(r) => request_json(&r, approval_core::request_status(mem, i).unwrap()),
            None => Value::Null,
        });
        want.push(
            approval_core::approval(mem, i)
                .map(proof)
                .unwrap_or(Value::Null),
        );
        want.push(
            mem.request(i)
                .and_then(|r| rejection_json(&r))
                .unwrap_or(Value::Null),
        );
    }
    for r in 0..=g {
        want.push(time_json(mem.revocation(r)));
    }
    for k in &ks {
        want.push(
            mem.principal(k)
                .map(|p| principal_json(&p))
                .unwrap_or(Value::Null),
        );
    }
    let page = |f: u64, l: u64| {
        Value::Array(
            approval_core::approvals(mem, f, l)
                .into_iter()
                .map(proof)
                .collect(),
        )
    };
    want.push(page(0, 50));
    want.push(page(f.unwrap_or(0), l.unwrap_or(50)));
    assert_eq!(got.len(), want.len());
    for (i, (a, b)) in got.iter().zip(&want).enumerate() {
        assert_eq!(a, b, "{ctx}: view #{i} differs (page args {f:?}, {l:?})");
    }
}

/// One step on both sides, with every per-step check.
/// Returns the contract's outcome (its storage is the post-state).
pub fn step(storage: Storage, mem: &mut Mem, c: &Ctx, op: &Op, what: &str) -> Outcome<Value> {
    let core = core_step(mem, c, op);
    let out = contract_step(c, storage, op);
    match (&core, &out.result) {
        (Err(e), Err(msg)) => {
            assert_eq!(msg, e.as_str(), "{what}: wrong panic message");
            assert!(
                out.logs.is_empty(),
                "{what}: failed call logged {:?}",
                out.logs
            );
        }
        (Ok(ok), Ok(ret)) => {
            let (want_ret, event, data) = expected_effect(mem, c, op, ok);
            assert_eq!(ret, &want_ret, "{what}: return value");
            assert_eq!(
                out.logs.len(),
                1,
                "{what}: expected one log, got {:?}",
                out.logs
            );
            assert_eq!(
                parse_event(&out.logs[0]),
                event_json(event, data),
                "{what}: event"
            );
        }
        _ => panic!("{what}: core {core:?} but contract {:?}", out.result),
    }
    // ST-4: α equal. ST-5/SH-2: no storage key outside α.
    let a = abs_contract(&out.storage, &keys());
    assert_eq!(a, abs_mem(mem), "{what}: α differs");
    let st = state_of(&out.storage);
    assert_eq!(
        sorted_keys(&out.storage),
        expected_keys(&a, &st),
        "{what}: storage keys"
    );
    out
}
