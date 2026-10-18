//! Exact shell tests (strategy.md 5.6-5.8, section 9): SH-1, SH-3..SH-8,
//! ST-5, ST-6, RES-1 (computed and measured), RES-2 (explicit limit, F-4),
//! and F-17 (ML-DSA-65 keys, refused by add_agent/add_approver).
//!
//! Every scenario runs the contract (mocked runtime, reload around every call)
//! and the core over a `MemStore` side by side through `step`, which also
//! checks results, events, α and the storage keys after every call.
//!
// PROP: SH-1 SH-3 SH-4 SH-5 SH-6 SH-7 SH-8 ST-5 ST-6 RES-1 RES-2 SH-13

use approval_contract::ApprovalContract;
use approval_core::{ApprovalError as E, MemStore, MAX_ACTION_LEN, MAX_PENDING_PER_KEY};
use near_approval_near_tests::serde_json::{self, json, Value};
use near_approval_near_tests::*;
use near_sdk::{env, AccountId, PublicKey};

/// Contract and core side by side.
struct Sim {
    storage: Storage,
    mem: Mem,
    n: usize,
}

impl Sim {
    fn new() -> Self {
        Sim {
            storage: deploy(&owner()),
            mem: MemStore::new(owner()),
            n: 0,
        }
    }

    /// Runs `op` on both sides with all of `step`'s checks.
    fn run(&mut self, c: &Ctx, op: Op) -> Outcome<Value> {
        self.n += 1;
        let what = format!("call {}: {op:?}", self.n);
        let out = step(self.storage.clone(), &mut self.mem, c, &op, &what);
        self.storage = out.storage.clone();
        out
    }

    fn ok(&mut self, c: &Ctx, op: Op) -> Outcome<Value> {
        let out = self.run(c, op.clone());
        assert!(out.result.is_ok(), "{op:?} failed: {:?}", out.result);
        out
    }

    fn err(&mut self, c: &Ctx, op: Op, e: E) {
        let before = self.storage.clone();
        let out = self.run(c, op.clone());
        assert_eq!(out.result.as_ref().unwrap_err(), e.as_str(), "{op:?}");
        assert!(out.logs.is_empty());
        assert_eq!(out.storage, before, "a failed call changed storage");
    }

    fn views(&self, label: &str) {
        let mut rng = Rng::new(self.n as u64);
        check_views(&self.storage, &self.mem, &mut rng, label);
    }
}

fn by_owner(t: u64) -> Ctx {
    Ctx::signed(&owner(), &keys()[3], at(t, t * 1_000_000_000))
}

fn signed(a: &AccountId, k: &PublicKey, t: u64) -> Ctx {
    Ctx::signed(a, k, at(t, t * 1_000_000_000 + 7))
}

fn alice() -> AccountId {
    accounts()[1].clone()
}
fn bob() -> AccountId {
    accounts()[2].clone()
}
fn carol() -> AccountId {
    accounts()[3].clone()
}

fn add_agent(a: &AccountId, k: &PublicKey) -> Op {
    Op::AddAgent {
        account: a.clone(),
        key: k.clone(),
    }
}
fn add_approver(a: &AccountId, k: &PublicKey) -> Op {
    Op::AddApprover {
        account: a.clone(),
        key: k.clone(),
    }
}
fn req(a: &str) -> Op {
    Op::Request { action: a.into() }
}
fn appr(id: u64, a: &str) -> Op {
    Op::Approve {
        id,
        action: a.into(),
    }
}

/// Owner registers alice/k0 as agent and bob/k1 as approver.
fn setup() -> Sim {
    let mut s = Sim::new();
    s.ok(&by_owner(1), add_agent(&alice(), &keys()[0]));
    s.ok(&by_owner(1), add_approver(&bob(), &keys()[1]));
    s
}

/// The single event logged by `out`.
fn event_of(out: &Outcome<Value>) -> Value {
    assert_eq!(
        out.logs.len(),
        1,
        "expected exactly one log: {:?}",
        out.logs
    );
    parse_event(&out.logs[0])
}

// ---------------------------------------------------------------------------
// SH-1 env mapping
// ---------------------------------------------------------------------------

#[test]
fn sh1_env_mapping() {
    quiet_expected_panics();
    let (k0, k1, k2, k3) = (&keys()[0], &keys()[1], &keys()[2], &keys()[3]);
    let mut s = Sim::new();
    // Owner methods use the predecessor, whoever signed: a DAO owner works...
    let dao = Ctx::new(&owner(), &carol(), k3, at(5, 6));
    s.ok(&dao, add_agent(&alice(), k0));
    s.ok(&dao, add_approver(&bob(), k1));
    s.ok(&dao, add_agent(&carol(), k2));
    let roles = view(&s.storage, |c| {
        [k0, k1].map(|k| serde_json::to_value(c.get_principal(k.clone())).unwrap()["role"].clone())
    });
    assert_eq!(roles, [json!("agent"), json!("approver")]);
    // ...and an owner signature relayed by another contract fails, for all three.
    let relayed = Ctx::new(&carol(), &owner(), k3, at(5, 6));
    s.err(&relayed, add_agent(&carol(), k3), E::NotOwner);
    s.err(&relayed, add_approver(&carol(), k3), E::NotOwner);
    s.err(&relayed, Op::Revoke { key: k2.clone() }, E::NotOwner);

    // caller() = (predecessor, signer, signer_pk); now() = (height, timestamp),
    // probed with pairwise-distinct values.
    let t_req = at(7, 123_456_789_012);
    let out = s.ok(&Ctx::signed(&alice(), k0, t_req), req("x"));
    let r = &event_of(&out)["data"];
    assert_eq!(r["agent_account_id"], json!(alice()));
    assert_eq!(r["agent_public_key"], json!(pk_str(k0)));
    assert_eq!(r["requested_at_block"], json!(7));
    assert_eq!(r["requested_at_ns"], json!("123456789012"));
    // predecessor != signer in either direction is an indirect call.
    s.err(
        &Ctx::new(&bob(), &alice(), k0, t_req),
        req("x"),
        E::IndirectCall,
    );
    s.err(
        &Ctx::new(&alice(), &bob(), k1, t_req),
        appr(0, "x"),
        E::IndirectCall,
    );
    s.err(
        &Ctx::new(&alice(), &bob(), k1, t_req),
        Op::Reject { id: 0 },
        E::IndirectCall,
    );

    let out = s.ok(
        &Ctx::signed(&bob(), k1, at(9, 987_654_321_000)),
        appr(0, "x"),
    );
    let p = &event_of(&out)["data"];
    assert_eq!(p["approver_account_id"], json!(bob()));
    assert_eq!(p["approver_public_key"], json!(pk_str(k1)));
    assert_eq!(
        (p["approved_at_block"].clone(), p["approved_at_ns"].clone()),
        (json!(9), json!("987654321000"))
    );

    s.ok(&Ctx::signed(&carol(), k2, at(10, 11)), req("y"));
    let out = s.ok(
        &Ctx::signed(&bob(), k1, at(12, 345_000_000_013)),
        Op::Reject { id: 1 },
    );
    let j = &event_of(&out)["data"];
    assert_eq!(
        (
            j["approver_account_id"].clone(),
            j["rejected_at_block"].clone(),
            j["rejected_at_ns"].clone()
        ),
        (json!(bob()), json!(12), json!("345000000013"))
    );

    // revoke_key passes the predecessor (DAO owner) and records now().
    let out = s.ok(
        &Ctx::new(&owner(), &alice(), k3, at(20, 21)),
        Op::Revoke { key: k2.clone() },
    );
    let d = &event_of(&out)["data"];
    assert_eq!(
        (d["revoked_at_block"].clone(), d["revoked_at_ns"].clone()),
        (json!(20), json!("21"))
    );
    s.views("sh1 end");
}

// ---------------------------------------------------------------------------
// SH-3 exact errors
// ---------------------------------------------------------------------------

/// Rewrites the counters in `STATE` (non-reachable states for the LogFull
/// guards; the core decides on them exactly as on reachable ones).
fn with_counters(
    storage: &Storage,
    reqs: Option<u64>,
    apprs: Option<u64>,
    regs: Option<u64>,
) -> Storage {
    let mut st = state_of(storage);
    st.request_count = reqs.unwrap_or(st.request_count);
    st.approval_count = apprs.unwrap_or(st.approval_count);
    st.registration_count = regs.unwrap_or(st.registration_count);
    let mut out = storage.clone();
    out.insert(STATE_KEY.to_vec(), near_sdk::borsh::to_vec(&st).unwrap());
    out
}

/// The `MemStore` twin of `with_counters`, for the parts a MemStore can hold.
#[test]
fn sh3_every_error_is_the_exact_message_and_logs_nothing() {
    quiet_expected_panics();
    let (k0, k1, k2, k3) = (&keys()[0], &keys()[1], &keys()[2], &keys()[3]);
    let mut s = setup();
    let ag = |t| signed(&alice(), k0, t);
    let ap = |t| signed(&bob(), k1, t);
    s.err(
        &signed(&alice(), k0, 2),
        add_agent(&carol(), k2),
        E::NotOwner,
    );
    s.err(
        &by_owner(2),
        add_approver(&carol(), k0),
        E::KeyAlreadyRegistered,
    );
    s.err(
        &by_owner(2),
        Op::Revoke { key: k2.clone() },
        E::KeyNotRegistered,
    );
    s.err(
        &Ctx::new(&bob(), &alice(), k0, at(2, 2)),
        req("x"),
        E::IndirectCall,
    );
    s.err(&signed(&alice(), k2, 2), req("x"), E::UnknownKey);
    s.err(&signed(&bob(), k1, 2), req("x"), E::WrongRole);
    s.err(&signed(&bob(), k0, 2), req("x"), E::KeyAccountMismatch);
    s.err(&ag(2), req(""), E::EmptyAction);
    s.err(
        &ag(2),
        Op::Request {
            action: "a".repeat(MAX_ACTION_LEN + 1),
        },
        E::ActionTooLong,
    );
    s.err(
        &ag(2),
        Op::Request {
            action: "é".repeat(1025),
        },
        E::ActionTooLong,
    );
    for _ in 0..MAX_PENDING_PER_KEY {
        s.ok(&ag(3), req("x"));
    }
    s.err(&ag(3), req("x"), E::TooManyPending);
    s.err(&ap(4), appr(99, "x"), E::RequestNotFound);
    s.ok(&ap(4), appr(0, "x"));
    s.err(&ap(4), appr(0, "x"), E::AlreadyApproved);
    s.ok(&ap(4), Op::Reject { id: 1 });
    s.err(&ap(4), appr(1, "x"), E::AlreadyRejected);
    s.err(&ap(4), Op::Reject { id: 1 }, E::AlreadyRejected);
    s.err(&ap(4), appr(2, "y"), E::ActionMismatch);
    // An approver key of the agent's own account.
    s.ok(&by_owner(5), add_approver(&alice(), k3));
    s.err(&signed(&alice(), k3, 6), appr(2, "x"), E::SelfApproval);
    s.err(
        &signed(&alice(), k3, 6),
        Op::Reject { id: 2 },
        E::SelfApproval,
    );
    s.ok(&by_owner(7), Op::Revoke { key: k0.clone() });
    s.err(&ap(8), appr(2, "x"), E::AgentRevoked);
    s.err(&ap(8), Op::Reject { id: 2 }, E::AgentRevoked);

    // The three LogFull guards, on states with a counter at u64::MAX. These
    // states are not reachable (LEM-3; 2^64 calls), so only the contract runs.
    let lf = E::LogFull.as_str();
    let st = with_counters(&s.storage, None, None, Some(u64::MAX));
    let out = contract_step(&by_owner(9), st.clone(), &add_agent(&carol(), k2));
    assert_eq!((out.result.unwrap_err().as_str(), out.logs.len()), (lf, 0));
    let mut t = setup();
    let st = with_counters(&t.storage, Some(u64::MAX), None, None);
    let out = contract_step(&signed(&alice(), k0, 9), st, &req("x"));
    assert_eq!((out.result.unwrap_err().as_str(), out.logs.len()), (lf, 0));
    t.ok(&signed(&alice(), k0, 9), req("x"));
    let st = with_counters(&t.storage, None, Some(u64::MAX), None);
    let out = contract_step(&signed(&bob(), k1, 9), st.clone(), &appr(0, "x"));
    assert_eq!((out.result.unwrap_err().as_str(), out.logs.len()), (lf, 0));
    assert_eq!(out.storage, st);
    s.views("sh3 end");
}

#[test]
fn sh3_panic_payload_format() {
    quiet_expected_panics();
    let s = setup();
    install(&signed(&alice(), &keys()[2], 2), s.storage.clone());
    let mut c: ApprovalContract = env::state_read().unwrap();
    let p = catch_quiet(|| c.request_action("x".into())).unwrap_err();
    let raw = p.downcast_ref::<String>().expect("String payload").clone();
    assert_eq!(
        raw,
        format!("{PANIC_PREFIX}{}{PANIC_SUFFIX}", E::UnknownKey.as_str())
    );
    std::mem::forget(c);
}

// ---------------------------------------------------------------------------
// SH-4, SH-5, SH-6 events
// ---------------------------------------------------------------------------

/// The envelope is exactly `EVENT_JSON:{"standard":...,"version":...,"event":...,"data":{...}}`.
fn assert_envelope(line: &str, event: &str) {
    let full = event_line(event, "{");
    let head = &full[..full.len() - 1];
    assert!(line.starts_with(head), "envelope: {line}");
    assert!(
        line.ends_with('}') && !line.contains('\n'),
        "one compact line: {line}"
    );
}

#[test]
fn sh4_approval_requested_is_one_exact_line() {
    quiet_expected_panics();
    let mut s = setup();
    let out = s.ok(&signed(&alice(), &keys()[0], 10), req("transfer 5 NEAR"));
    assert_eq!(out.result.as_ref().unwrap(), &json!(0));
    assert_eq!(out.logs.len(), 1);
    assert_envelope(&out.logs[0], "approval_requested");
    let data = &parse_event(&out.logs[0])["data"];
    assert_eq!(data["status"], json!("pending"));
    // The event data equals get_request at that point.
    let now = view(&s.storage, |c| {
        serde_json::to_value(c.get_request(0)).unwrap()
    });
    assert_eq!(data, &now);
}

#[test]
fn sh5_action_approved_equals_return_value_and_get_approval_forever() {
    quiet_expected_panics();
    let (k0, k1) = (&keys()[0], &keys()[1]);
    let mut s = setup();
    s.ok(&signed(&alice(), k0, 2), req("x"));
    let out = s.ok(&signed(&bob(), k1, 3), appr(0, "x"));
    assert_envelope(&out.logs[0], "action_approved");
    let data = event_of(&out)["data"].clone();
    assert_eq!(out.result.as_ref().unwrap(), &data, "data = return value");
    let get = |s: &Sim| {
        view(&s.storage, |c| {
            serde_json::to_value(c.get_approval(0)).unwrap()
        })
    };
    assert_eq!(get(&s), data, "= get_approval now");
    assert_eq!(data["agent_key_revoked_at"], Value::Null);
    // Later: only the revocation fields may change (F-15), and they report
    // the revocation of the registration the key acted under (RD-8).
    s.ok(&signed(&alice(), k0, 4), req("y"));
    s.ok(&by_owner(9), Op::Revoke { key: k1.clone() });
    s.ok(&by_owner(9), add_approver(&bob(), k1));
    s.ok(&by_owner(11), Op::Revoke { key: k0.clone() });
    let later = get(&s);
    let mut want = data.clone();
    want["approver_key_revoked_at"] = json!({"block": 9, "ns": "9000000000"});
    want["agent_key_revoked_at"] = json!({"block": 11, "ns": "11000000000"});
    assert_eq!(later, want);
    s.views("sh5 end");
}

#[test]
fn sh6_each_change_method_logs_exactly_its_event_and_nothing_else_logs() {
    quiet_expected_panics();
    let (k0, k1) = (&keys()[0], &keys()[1]);
    let mut s = Sim::new(); // deploy() asserts that new() logs nothing
    let cases: Vec<(Ctx, Op, &str)> = vec![
        (by_owner(1), add_agent(&alice(), k0), "key_added"),
        (by_owner(1), add_approver(&bob(), k1), "key_added"),
        (signed(&alice(), k0, 2), req("x"), "approval_requested"),
        (signed(&alice(), k0, 2), req("y"), "approval_requested"),
        (signed(&bob(), k1, 3), appr(0, "x"), "action_approved"),
        (
            signed(&bob(), k1, 3),
            Op::Reject { id: 1 },
            "action_rejected",
        ),
        (by_owner(4), Op::Revoke { key: k0.clone() }, "key_revoked"),
    ];
    for (c, op, event) in cases {
        let out = s.ok(&c, op);
        assert_eq!(out.logs.len(), 1);
        assert_envelope(&out.logs[0], event);
    }
    // Every view, on every id, logs nothing (`view` asserts it).
    s.views("sh6 views");
}

// ---------------------------------------------------------------------------
// SH-7 view mapping, SH-8 JSON shape
// ---------------------------------------------------------------------------

#[test]
fn sh7_views_equal_core_reads_in_every_status() {
    quiet_expected_panics();
    let (k0, k1, k2, k3) = (&keys()[0], &keys()[1], &keys()[2], &keys()[3]);
    let mut s = setup();
    s.ok(&by_owner(1), add_agent(&carol(), k2));
    s.ok(&by_owner(1), add_approver(&carol(), k3));
    for i in 0..6 {
        s.ok(
            &signed(&alice(), k0, 2 + i),
            Op::Request {
                action: format!("a{i}"),
            },
        );
        s.ok(
            &signed(&carol(), k2, 2 + i),
            Op::Request {
                action: format!("c{i}"),
            },
        );
    }
    // approved (out of order), rejected, pending, void, and void after re-add.
    for (id, a) in [(4, "a2"), (0, "a0"), (7, "c3")] {
        s.ok(&signed(&bob(), k1, 20), appr(id, a));
    }
    s.ok(&signed(&carol(), k3, 21), Op::Reject { id: 2 });
    s.ok(&signed(&bob(), k1, 21), Op::Reject { id: 3 });
    s.ok(&by_owner(22), Op::Revoke { key: k2.clone() });
    s.ok(&by_owner(23), add_agent(&carol(), k2));
    s.ok(&signed(&carol(), k2, 24), req("c-new"));
    let statuses = view(&s.storage, |c| {
        (0..c.get_request_count())
            .map(|i| serde_json::to_value(c.get_request(i).unwrap()).unwrap()["status"].clone())
            .collect::<Vec<_>>()
    });
    for st in ["pending", "approved", "rejected", "void"] {
        assert!(
            statuses.contains(&json!(st)),
            "no {st} request: {statuses:?}"
        );
    }
    for seed in 0..20 {
        check_views(&s.storage, &s.mem, &mut Rng::new(seed), "sh7");
    }
}

#[test]
fn sh7_get_approvals_defaults_and_cap() {
    quiet_expected_panics();
    let (k0, k1) = (&keys()[0], &keys()[1]);
    let mut s = setup();
    for i in 0..105 {
        s.ok(&signed(&alice(), k0, 2), req("x"));
        s.ok(&signed(&bob(), k1, 3), appr(i, "x"));
    }
    let lens = view(&s.storage, |c| {
        [
            c.get_approvals(None, None).len(),
            c.get_approvals(Some(0), None).len(),
            c.get_approvals(None, Some(500)).len(),
            c.get_approvals(Some(100), Some(500)).len(),
            c.get_approvals(Some(3), Some(0)).len(),
            c.get_approvals(Some(u64::MAX), Some(u64::MAX)).len(),
            c.get_approvals(Some(104), None).len(),
        ]
    });
    assert_eq!(lens, [50, 50, 100, 5, 0, 0, 1]);
    for seed in 0..10 {
        check_views(&s.storage, &s.mem, &mut Rng::new(seed), "sh7 paging");
    }
}

fn keys_of(v: &Value) -> Vec<String> {
    let mut k: Vec<_> = v.as_object().expect("object").keys().cloned().collect();
    k.sort();
    k
}

fn sorted(xs: &[&str]) -> Vec<String> {
    let mut v: Vec<String> = xs.iter().map(|s| s.to_string()).collect();
    v.sort();
    v
}

#[test]
fn sh8_json_shape() {
    quiet_expected_panics();
    let (k0, k1) = (&keys()[0], &keys()[1]);
    let mut s = setup();
    // Values above 2^53: heights stay exact JSON numbers, *_ns are strings.
    let big = at((1 << 60) + 1, u64::MAX);
    s.ok(&Ctx::signed(&alice(), k0, big), req("x"));
    s.ok(&Ctx::signed(&alice(), k0, big), req("y"));
    s.ok(&Ctx::signed(&bob(), k1, big), appr(0, "x"));
    s.ok(&Ctx::signed(&bob(), k1, big), Op::Reject { id: 1 });
    s.ok(
        &Ctx::new(&owner(), &owner(), k1, big),
        Op::Revoke { key: k1.clone() },
    );
    let (r, p, j, pr, rv) = view(&s.storage, |c| {
        (
            serde_json::to_value(c.get_request(0)).unwrap(),
            serde_json::to_value(c.get_approval(0)).unwrap(),
            serde_json::to_value(c.get_rejection(1)).unwrap(),
            serde_json::to_value(c.get_principal(k0.clone())).unwrap(),
            serde_json::to_value(c.get_revocation(1)).unwrap(),
        )
    });
    // README field names.
    assert_eq!(
        keys_of(&r),
        sorted(&[
            "request_id",
            "agent_account_id",
            "agent_public_key",
            "agent_registration_id",
            "action",
            "requested_at_block",
            "requested_at_ns",
            "status"
        ])
    );
    assert_eq!(
        keys_of(&p),
        sorted(&[
            "approval_index",
            "request_id",
            "action",
            "agent_account_id",
            "agent_public_key",
            "agent_registration_id",
            "requested_at_block",
            "requested_at_ns",
            "approver_account_id",
            "approver_public_key",
            "approver_registration_id",
            "approved_at_block",
            "approved_at_ns",
            "agent_key_revoked_at",
            "approver_key_revoked_at"
        ])
    );
    assert_eq!(
        keys_of(&j),
        sorted(&[
            "request_id",
            "action",
            "agent_account_id",
            "agent_public_key",
            "agent_registration_id",
            "requested_at_block",
            "requested_at_ns",
            "approver_account_id",
            "approver_public_key",
            "approver_registration_id",
            "rejected_at_block",
            "rejected_at_ns"
        ])
    );
    assert_eq!(
        keys_of(&pr),
        sorted(&["account_id", "role", "registration_id", "pending"])
    );
    assert_eq!(keys_of(&rv), sorted(&["block", "ns"]));
    // Types: ids, indices and heights are numbers (exact past 2^53); *_ns strings.
    let ns = u64::MAX.to_string();
    assert_eq!(r["requested_at_block"].as_u64(), Some((1 << 60) + 1));
    assert_eq!(r["requested_at_ns"], json!(ns));
    assert_eq!(p["approved_at_ns"], json!(ns));
    assert_eq!(j["rejected_at_ns"], json!(ns));
    assert_eq!(
        p["approver_key_revoked_at"],
        json!({"block": (1u64 << 60) + 1, "ns": ns})
    );
    assert_eq!(rv["ns"], json!(ns));
    for v in [&r, &p, &j] {
        for (k, x) in v.as_object().unwrap() {
            if k.ends_with("_ns") {
                assert!(x.is_string(), "{k} must be a string");
            } else if k.ends_with("_id") && !k.contains("account") && !k.contains("public") {
                assert!(x.is_u64(), "{k} must be a number");
            }
        }
    }
    assert!(pr["pending"].is_u64() && pr["registration_id"].is_u64());
    assert_eq!(pr["role"], json!("agent"));
    // `null` for absent results.
    let nulls = view(&s.storage, |c| {
        serde_json::to_value((
            c.get_request(9),
            c.get_approval(1),
            c.get_rejection(0),
            c.get_revocation(0),
            c.get_principal(keys()[2].clone()),
        ))
        .unwrap()
    });
    assert_eq!(nulls, json!([null, null, null, null, null]));
}

// ---------------------------------------------------------------------------
// ST-5 prefixes, ST-6 golden Borsh bytes
// ---------------------------------------------------------------------------

#[test]
fn st5_prefixes_distinct_and_state_roundtrips() {
    let storage = deploy(&owner());
    assert_eq!(
        sorted_keys(&storage),
        vec![STATE_KEY.to_vec()],
        "new() writes only STATE"
    );
    let st = state_of(&storage);
    let prefixes = [
        &st.principals_prefix,
        &st.requests_prefix,
        &st.approval_log_prefix,
        &st.revocations_prefix,
    ];
    assert_eq!(
        prefixes.map(|p| p.as_slice()),
        [b"p".as_slice(), b"r", b"a", b"v"]
    );
    for (i, a) in prefixes.iter().enumerate() {
        assert!(
            !STATE_KEY.starts_with(a) && !a.starts_with(STATE_KEY),
            "prefix {a:?} overlaps STATE"
        );
        for b in &prefixes[i + 1..] {
            assert!(
                !a.starts_with(b) && !b.starts_with(a),
                "prefixes {a:?} and {b:?} overlap"
            );
        }
    }
    // The mirror struct is the real layout: re-encoding gives the same bytes.
    assert_eq!(
        &near_sdk::borsh::to_vec(&st).unwrap(),
        storage.get(STATE_KEY).unwrap()
    );
    assert_eq!(st.owner, owner().to_string());
    assert_eq!(
        (st.request_count, st.approval_count, st.registration_count),
        (0, 0, 0)
    );
}

/// A fixed scenario touching every map with both curve types.
fn golden_scenario() -> Sim {
    quiet_expected_panics();
    let (k0, k1) = (&keys()[0], &keys()[1]);
    let mut s = Sim::new();
    s.ok(&by_owner(1), add_agent(&alice(), k0));
    s.ok(&by_owner(1), add_approver(&bob(), k1));
    s.ok(&Ctx::signed(&alice(), k0, at(2, 20)), req("pay 5"));
    s.ok(&Ctx::signed(&alice(), k0, at(2, 21)), req("pay 6"));
    s.ok(&Ctx::signed(&alice(), k0, at(2, 22)), req("pay 7"));
    s.ok(&Ctx::signed(&bob(), k1, at(3, 30)), appr(0, "pay 5"));
    s.ok(&Ctx::signed(&bob(), k1, at(3, 31)), Op::Reject { id: 1 });
    s.ok(
        &Ctx::new(&owner(), &owner(), k1, at(4, 40)),
        Op::Revoke { key: k1.clone() },
    );
    s
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[test]
fn st6_golden_borsh_bytes() {
    let s = golden_scenario();
    let st = state_of(&s.storage);
    let b = |x: u64| near_sdk::borsh::to_vec(&x).unwrap();
    let key = |p: &[u8], k: Vec<u8>| [p.to_vec(), k].concat();
    let entries: Vec<(&str, Vec<u8>)> = vec![
        ("state_new", STATE_KEY.to_vec()),
        (
            "principal_ed25519",
            key(
                &st.principals_prefix,
                near_sdk::borsh::to_vec(&keys()[0]).unwrap(),
            ),
        ),
        ("request_approved", key(&st.requests_prefix, b(0))),
        ("request_rejected", key(&st.requests_prefix, b(1))),
        ("request_pending", key(&st.requests_prefix, b(2))),
        ("approval_log_0", key(&st.approval_log_prefix, b(0))),
        ("revocation_1", key(&st.revocations_prefix, b(1))),
    ];
    let mut lines = vec![
        "# ST-6 golden storage layout: name, storage key (hex), value (hex).".to_string(),
        "# A difference is a STORAGE-BREAKING change: flag it in the pin-bump PR.".to_string(),
        "# Regenerate: UPDATE_GOLDEN=1 cargo test --locked --test shell st6".to_string(),
    ];
    let state_new = deploy(&owner());
    for (name, k) in &entries {
        let v = if *name == "state_new" {
            state_new.get(STATE_KEY)
        } else {
            s.storage.get(k)
        };
        let v = v.unwrap_or_else(|| panic!("{name}: key missing"));
        lines.push(format!("{name} {} {}", hex(k), hex(v)));
    }
    lines.push(format!(
        "state_after_scenario {} {}",
        hex(STATE_KEY),
        hex(&s.storage[STATE_KEY])
    ));
    // A secp256k1 principal: re-register the revoked approver key's slot.
    let mut s2 = golden_scenario();
    s2.ok(&by_owner(5), add_approver(&bob(), &keys()[1]));
    let k = key(
        &st.principals_prefix,
        near_sdk::borsh::to_vec(&keys()[1]).unwrap(),
    );
    lines.push(format!(
        "principal_secp256k1 {} {}",
        hex(&k),
        hex(&s2.storage[&k])
    ));
    let text = lines.join("\n") + "\n";
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden/layout.txt");
    if std::env::var_os("UPDATE_GOLDEN").is_some() {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, &text).unwrap();
    }
    let golden = std::fs::read_to_string(&path).expect("tests/golden/layout.txt");
    assert!(
        golden == text,
        "STORAGE-BREAKING: the Borsh layout differs from tests/golden/layout.txt\n--- golden\n{golden}\n--- now\n{text}"
    );
}

// ---------------------------------------------------------------------------
// RES-1 storage growth, computed from the Borsh layout and measured
// ---------------------------------------------------------------------------

/// Borsh size of a `PublicKey`: a `Vec<u8>` of curve tag and key bytes.
fn key_len(k: &PublicKey) -> u64 {
    4 + k.as_bytes().len() as u64
}

const EXTRA: u64 = 40; // storage_num_extra_bytes_record (ASM-STAKE)
const ACC: u64 = 4 + 64; // a 64-character AccountId
const TIME: u64 = 16;

struct Bounds {
    p: u64,
    req: u64,
    ap: u64,
    log: u64,
    rej: u64,
    v: u64,
}

/// The RES-1 bounds for keys of the size of `k` (worst case for its curve).
fn bounds(k: &PublicKey) -> Bounds {
    let kl = key_len(k);
    let principal = ACC + 1 + 8 + 8 + 4;
    let request = 8 + ACC + kl + 8 + (4 + MAX_ACTION_LEN as u64) + TIME + 1 + 1;
    Bounds {
        p: (1 + kl) + principal + EXTRA,
        req: (1 + 8) + request + EXTRA,
        ap: 8 + ACC + kl + 8 + TIME,
        log: (1 + 8) + 8 + EXTRA,
        rej: ACC + kl + 8 + TIME,
        v: (1 + 8) + TIME + EXTRA,
    }
}

/// Storage usage change of one successful call, as the runtime meters it.
fn measured(ctx: &Ctx, storage: Storage, f: impl FnOnce(&mut ApprovalContract)) -> (i64, Storage) {
    install(ctx, storage);
    let u0 = env::storage_usage();
    let mut c: ApprovalContract = env::state_read().unwrap();
    f(&mut c);
    env::state_write(&c);
    drop(c);
    let u1 = env::storage_usage();
    (u1 as i64 - u0 as i64, take_storage())
}

fn res1_for(k_agent: PublicKey, k_appr: PublicKey) -> Bounds {
    let agent = long_account('a');
    let approver = long_account('b');
    let action = "a".repeat(MAX_ACTION_LEN);
    let st = deploy(&owner());
    let b = bounds(&k_agent);
    let ba = bounds(&k_appr);
    let (d, st) = measured(&by_owner(1), st, |c| {
        c.add_agent(agent.clone(), k_agent.clone())
    });
    assert_eq!(d as u64, b.p, "Add (agent)");
    let (d, st) = measured(&by_owner(1), st, |c| {
        c.add_approver(approver.clone(), k_appr.clone())
    });
    assert_eq!(d as u64, ba.p, "Add (approver)");
    // Req: one new record; the principal is rewritten at the same size.
    let (d, st) = measured(&Ctx::signed(&agent, &k_agent, at(2, 2)), st, |c| {
        c.request_action(action.clone());
    });
    assert_eq!(d as u64, b.req, "Req");
    let (d, st) = measured(&Ctx::signed(&agent, &k_agent, at(2, 2)), st, |c| {
        c.request_action(action.clone());
    });
    assert_eq!(d as u64, b.req, "Req again");
    let (d, st) = measured(&Ctx::signed(&approver, &k_appr, at(3, 3)), st, |c| {
        c.approve(0, action.clone());
    });
    assert_eq!(d as u64, ba.ap + b.log, "Appr");
    let (d, st) = measured(&Ctx::signed(&approver, &k_appr, at(3, 3)), st, |c| {
        c.reject(1);
    });
    assert_eq!(d as u64, ba.rej, "Rej");
    let (d, _) = measured(&by_owner(4), st, |c| c.revoke_key(k_agent.clone()));
    assert_eq!(d, b.v as i64 - b.p as i64, "Revoke");
    b
}

#[test]
fn res1_storage_growth_bounds() {
    // ed25519 and secp256k1: the strategy's universe. secp256k1 is the worst.
    let ed = res1_for(ed25519(1), ed25519(2));
    let secp = res1_for(secp256k1(1), secp256k1(2));
    assert!(secp.req > ed.req);
    // 16 x B_req per agent key without an approver: about 0.36 NEAR.
    let yocto = MAX_PENDING_PER_KEY as u128 * secp.req as u128 * 10u128.pow(19);
    assert!(yocto <= 37 * 10u128.pow(22), "16 x B_req = {yocto} yocto");
    // ML-DSA-65 keys cannot be registered (F-17), so these are all key types.
    eprintln!(
        "RES-1 bounds (bytes incl. 40 B/record): secp256k1 B_p={} B_req={} B_ap={} B_log={} B_rej={} B_v={}; \
         16 x B_req = {:.3} NEAR",
        secp.p, secp.req, secp.ap, secp.log, secp.rej, secp.v,
        yocto as f64 / 1e24
    );
}

// ---------------------------------------------------------------------------
// RES-2 worst-case event lines fit the 16384-byte log limit (F-4)
// ---------------------------------------------------------------------------

const LOG_LIMIT: u64 = 16384;

/// Runs request, approve and reject at the worst case for keys `ka`/`kb`:
/// 64-character accounts, a 2048-byte action of control bytes (each escaped
/// to six bytes), `u64::MAX` times and 20-digit ids. Returns the three log
/// lines' lengths, or the failure of the call that broke the limit.
fn worst_case_lines(ka: &PublicKey, kb: &PublicKey) -> Result<[usize; 3], String> {
    quiet_expected_panics();
    let agent = long_account('a');
    let approver = long_account('b');
    let action = "\u{1}".repeat(MAX_ACTION_LEN);
    let t = at(u64::MAX, u64::MAX);
    let base = with_counters(
        &deploy(&owner()),
        Some(u64::MAX - 2),
        Some(u64::MAX - 1),
        Some(u64::MAX - 3),
    );
    let ok = |o: Outcome<Value>| -> Result<(Storage, usize), String> {
        let r = o.result?;
        let _ = r;
        assert_eq!(o.logs.len(), 1);
        Ok((o.storage, o.logs[0].len()))
    };
    let (st, _) = ok(contract_step(
        &Ctx::signed(&owner(), ka, t),
        base,
        &add_agent(&agent, ka),
    ))?;
    let (st, _) = ok(contract_step(
        &Ctx::signed(&owner(), ka, t),
        st,
        &add_approver(&approver, kb),
    ))?;
    let (st, l_req) = ok(contract_step(
        &Ctx::signed(&agent, ka, t),
        st,
        &Op::Request {
            action: action.clone(),
        },
    ))?;
    let (st, _) = ok(contract_step(
        &Ctx::signed(&agent, ka, t),
        st,
        &Op::Request {
            action: action.clone(),
        },
    ))?;
    let (st, l_rej) = ok(contract_step(
        &Ctx::signed(&approver, kb, t),
        st,
        &Op::Reject { id: u64::MAX - 1 },
    ))?;
    let (_, l_appr) = ok(contract_step(
        &Ctx::signed(&approver, kb, t),
        st,
        &Op::Approve {
            id: u64::MAX - 2,
            action,
        },
    ))?;
    Ok([l_req, l_appr, l_rej])
}

#[test]
fn res2_worst_case_event_lines_fit_16384_bytes() {
    // The mocked runtime enforces the protocol's limit itself.
    assert_eq!(
        near_sdk::test_vm_config().limit_config.max_total_log_length,
        LOG_LIMIT
    );
    let mut worst = 0;
    for (ka, kb) in [
        (ed25519(1), ed25519(2)),
        (secp256k1(1), secp256k1(2)),
        (ed25519(1), secp256k1(2)),
        (secp256k1(1), ed25519(2)),
    ] {
        let lens = worst_case_lines(&ka, &kb).unwrap_or_else(|e| panic!("worst case failed: {e}"));
        for l in lens {
            assert!(l as u64 <= LOG_LIMIT, "{l} B > {LOG_LIMIT}");
        }
        worst = worst.max(*lens.iter().max().unwrap());
    }
    // Non-vacuity: the escaping really produced the ~13 KB worst case (F-4).
    assert!(worst > 12_800, "worst line only {worst} B");
    eprintln!(
        "RES-2: worst event line with ed25519/secp256k1 keys = {worst} B (limit {LOG_LIMIT})"
    );
}

/// SH-13 (F-17): an ML-DSA-65 key on both sides would push the worst-case
/// `action_approved` line past the 16 KiB log limit (18,256 B), so upstream
/// refuses ML-DSA-65 keys in `add_agent` and `add_approver`. The refusal comes
/// after the owner check and before the core's guards (KeyAlreadyRegistered,
/// LogFull), panics with exactly `UNSUPPORTED_KEY_TYPE` and logs nothing; the
/// worst case can then not be set up with an ML-DSA-65 key on either side.
#[test]
fn f17_mldsa65_keys_are_refused() {
    quiet_expected_panics();
    let msg = approval_contract::UNSUPPORTED_KEY_TYPE;
    let pq = mldsa65(1);
    let a = accounts()[1].clone();
    let base = deploy(&owner());
    let refused = |ctx: &Ctx, st: Storage, op: &Op| -> String {
        let o = contract_step(ctx, st, op);
        assert!(o.logs.is_empty(), "refusal logged {:?}", o.logs);
        o.result.expect_err("ML-DSA-65 key accepted")
    };
    for op in [add_agent(&a, &pq), add_approver(&a, &pq)] {
        // Owner: refused with the exact message.
        assert_eq!(refused(&by_owner(1), base.clone(), &op), msg);
        // Non-owner: NotOwner still comes first.
        assert_eq!(
            refused(&signed(&a, &keys()[0], 1), base.clone(), &op),
            E::NotOwner.as_str()
        );
        // Before the core's guards: with the registration counter at
        // u64::MAX, any other key gets LogFull; an ML-DSA-65 key is still
        // refused as unsupported.
        let full = with_counters(&base, None, None, Some(u64::MAX));
        assert_eq!(
            contract_step(&by_owner(1), full.clone(), &add_agent(&a, &ed25519(9)))
                .result
                .unwrap_err(),
            E::LogFull.as_str()
        );
        assert_eq!(refused(&by_owner(1), full, &op), msg);
    }
    // The F-17 worst case cannot be set up with an ML-DSA-65 key on either side.
    for (ka, kb) in [
        (mldsa65(1), mldsa65(2)),
        (mldsa65(1), secp256k1(2)),
        (secp256k1(1), mldsa65(2)),
    ] {
        let e = worst_case_lines(&ka, &kb).expect_err("ML-DSA-65 key registered");
        assert_eq!(e, msg);
    }
}
