//! ST-4 and SH-2: the deployed store refines `MemStore` (strategy.md 5.6, 5.8).
//!
//! `ApprovalContract` (through its public methods, under near-sdk's mocked
//! runtime) and `MemStore<AccountId, PublicKey>` (through the core directly)
//! run the same random operation sequences. Before every step the contract is
//! persisted and reloaded (`state_write`, drop, `state_read`), so every step
//! reads Borsh from cold storage. After every step:
//!
//! - results are equal: the core's `Err(e)` is a panic with exactly
//!   `e.as_str()` and no log (SH-3), its `Ok` is the method's return value and
//!   exactly one event line with the expected data (SH-4, SH-5, SH-6);
//! - α(contract) = α(MemStore) (ST-4), and the raw storage holds exactly the
//!   keys α accounts for, `STATE` and `prefix ‖ borsh(key)` (ST-5): the call
//!   made one core transition and no other write (SH-2);
//! - every view equals the core's read on the `MemStore` (SH-7), on a
//!   contract reloaded again (views are pure, RD-6).
//!
//! Size: STORE_DIFF_SEQS sequences (default 10000) of STORE_DIFF_STEPS steps
//! (default 50), seeds STORE_DIFF_SEED.. (default 1). STORE_DIFF_VIEWS=0 skips
//! the per-step view comparison (it is then done at the end of each sequence).
//!
// PROP: ST-4 SH-2 ST-5 SH-3 SH-4 SH-5 SH-6 SH-7

use approval_core::{ApprovalError, MemStore, Role, Store};
use near_approval_near_tests::*;
use near_sdk::PublicKey;

const ACTIONS: &[&str] = &["x", "y", "pay 5", "", "\u{1}\u{2}\"\\", "\u{202e}abc"];

fn action(rng: &mut Rng) -> String {
    match rng.below(10) {
        0 => "a".repeat(2048),
        1 => "a".repeat(2049),
        2 => "é".repeat(1024), // 2048 bytes
        3 => "é".repeat(1025), // 2050 bytes
        _ => rng.pick(ACTIONS).to_string(),
    }
}

/// A random step biased toward successful calls, with every guard reachable.
fn gen_step(rng: &mut Rng, mem: &Mem, time: &mut (u64, u64), heavy: bool) -> (Ctx, Op) {
    let accts = accounts();
    let ks = keys();
    time.0 += rng.below(3);
    time.1 += rng.below(3) * 1_000_000_000 + rng.below(1000);
    let now = at(time.0, time.1);
    let key = rng.pick(&ks).clone();
    let acct = rng.pick(&accts).clone();
    let other = rng.pick(&accts).clone();
    let registered = |k: &PublicKey| mem.principal(k).map(|p| p.account_id);
    // Admin calls: the owner as predecessor most of the time, any signer.
    let admin = |rng: &mut Rng| {
        let pred = if rng.chance(85) {
            owner()
        } else {
            acct.clone()
        };
        Ctx::new(&pred, &other, &key, now)
    };
    // Signed calls: predecessor = signer mostly, the key's own account mostly.
    let signed = |rng: &mut Rng, k: &PublicKey| {
        let signer = match registered(k) {
            Some(a) if rng.chance(80) => a,
            _ => acct.clone(),
        };
        let pred = if rng.chance(92) {
            signer.clone()
        } else {
            other.clone()
        };
        Ctx::new(&pred, &signer, k, now)
    };
    let pick_id = |rng: &mut Rng| {
        let n = mem.request_count();
        if n > 0 && rng.chance(90) {
            // Prefer recent requests: more of them are still pending.
            n - 1 - rng.below(n.min(6))
        } else {
            rng.below(n + 2)
        }
    };
    // Request-heavy sequences fill one agent key up to the pending cap.
    if heavy && rng.chance(60) {
        if let Some((k, p)) = mem.principals.iter().find(|(_, p)| p.role == Role::Agent) {
            return (
                Ctx::signed(&p.account_id, k, now),
                Op::Request { action: "x".into() },
            );
        }
    }
    match rng.below(100) {
        0..=11 => (
            admin(rng),
            Op::AddAgent {
                account: acct.clone(),
                key,
            },
        ),
        12..=21 => (
            admin(rng),
            Op::AddApprover {
                account: acct.clone(),
                key,
            },
        ),
        22..=27 => (admin(rng), Op::Revoke { key }),
        28..=59 => {
            // Request with an agent key when there is one.
            let k = mem
                .principals
                .iter()
                .filter(|(_, p)| p.role == Role::Agent)
                .map(|(k, _)| k.clone())
                .collect::<Vec<_>>();
            let k = if !k.is_empty() && rng.chance(85) {
                rng.pick(&k).clone()
            } else {
                key
            };
            (
                signed(rng, &k),
                Op::Request {
                    action: action(rng),
                },
            )
        }
        _ => {
            let k = mem
                .principals
                .iter()
                .filter(|(_, p)| p.role == Role::Approver)
                .map(|(k, _)| k.clone())
                .collect::<Vec<_>>();
            let k = if !k.is_empty() && rng.chance(85) {
                rng.pick(&k).clone()
            } else {
                key
            };
            let ctx = signed(rng, &k);
            let id = pick_id(rng);
            if rng.chance(70) {
                let act = match mem.request(id) {
                    Some(r) if rng.chance(85) => r.action,
                    _ => action(rng),
                };
                (ctx, Op::Approve { id, action: act })
            } else {
                (ctx, Op::Reject { id })
            }
        }
    }
}

#[test]
fn store_refines_memstore_with_reload_every_step() {
    quiet_expected_panics();
    let seqs = env_u64("STORE_DIFF_SEQS", 10_000);
    let steps = env_u64("STORE_DIFF_STEPS", 50);
    let seed0 = env_u64("STORE_DIFF_SEED", 1);
    let views_every_step = env_u64("STORE_DIFF_VIEWS", 1) != 0;
    let started = std::time::Instant::now();
    let mut errors = std::collections::BTreeMap::<&'static str, u64>::new();
    let mut oks = std::collections::BTreeMap::<&'static str, u64>::new();
    let mut max_requests = 0;
    for s in 0..seqs {
        let seed = seed0 + s;
        let mut rng = Rng::new(seed);
        let mut storage = deploy(&owner());
        let mut mem: Mem = MemStore::new(owner());
        let mut time = (1, 1_000_000_000);
        let heavy = rng.chance(20);
        for t in 0..steps {
            let (c, op) = gen_step(&mut rng, &mem, &mut time, heavy);
            let what = format!("seed {seed} step {t}: {op:?} by {c:?}");
            let before = mem.clone();
            storage = step(storage, &mut mem, &c, &op, &what).storage;
            let kind = match &op {
                Op::AddAgent { .. } | Op::AddApprover { .. } => "add",
                Op::Revoke { .. } => "revoke",
                Op::Request { .. } => "request",
                Op::Approve { .. } => "approve",
                Op::Reject { .. } => "reject",
            };
            if mem == before {
                // Failed (TX-0 on the core side): count which guard.
                let e = core_step(&mut before.clone(), &c, &op).unwrap_err();
                *errors.entry(err_name(e)).or_default() += 1;
            } else {
                *oks.entry(kind).or_default() += 1;
            }
            if views_every_step {
                check_views(&storage, &mem, &mut rng, &what);
            }
        }
        if !views_every_step {
            check_views(&storage, &mem, &mut rng, &format!("seed {seed} end"));
        }
        max_requests = max_requests.max(mem.request_count());
    }
    eprintln!(
        "store_diff: {seqs} x {steps} steps in {:.1?}; ok {oks:?}; errors {errors:?}; max #R {max_requests}",
        started.elapsed()
    );
    // Non-vacuity: every operation succeeded and every reachable error occurred.
    if seqs * steps >= 20_000 {
        for k in ["add", "revoke", "request", "approve", "reject"] {
            assert!(oks.get(k).copied().unwrap_or(0) > 0, "no successful {k}");
        }
        for e in [
            "NotOwner",
            "IndirectCall",
            "UnknownKey",
            "WrongRole",
            "KeyAccountMismatch",
            "KeyAlreadyRegistered",
            "KeyNotRegistered",
            "EmptyAction",
            "ActionTooLong",
            "TooManyPending",
            "RequestNotFound",
            "AlreadyApproved",
            "AlreadyRejected",
            "AgentRevoked",
            "ActionMismatch",
            "SelfApproval",
        ] {
            assert!(errors.contains_key(e), "error {e} never produced");
        }
    }
}

fn err_name(e: ApprovalError) -> &'static str {
    match e {
        ApprovalError::NotOwner => "NotOwner",
        ApprovalError::IndirectCall => "IndirectCall",
        ApprovalError::UnknownKey => "UnknownKey",
        ApprovalError::WrongRole => "WrongRole",
        ApprovalError::KeyAccountMismatch => "KeyAccountMismatch",
        ApprovalError::KeyAlreadyRegistered => "KeyAlreadyRegistered",
        ApprovalError::KeyNotRegistered => "KeyNotRegistered",
        ApprovalError::EmptyAction => "EmptyAction",
        ApprovalError::ActionTooLong => "ActionTooLong",
        ApprovalError::TooManyPending => "TooManyPending",
        ApprovalError::RequestNotFound => "RequestNotFound",
        ApprovalError::AlreadyApproved => "AlreadyApproved",
        ApprovalError::AlreadyRejected => "AlreadyRejected",
        ApprovalError::AgentRevoked => "AgentRevoked",
        ApprovalError::ActionMismatch => "ActionMismatch",
        ApprovalError::SelfApproval => "SelfApproval",
        ApprovalError::LogFull => "LogFull",
    }
}
