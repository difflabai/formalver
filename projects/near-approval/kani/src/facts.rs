//! Generates `prolog/extracted/code_facts.pl` from the real core (strategy
//! §8, C-2, C-3, C-5). Plain mode only.
//!
//! The guard precedence is observed, not transcribed. For each operation,
//! `fails` lists every guard whose condition holds for a call, each judged
//! on its own (no order). Running the core on many random states and calls,
//! the error it returns must be one of them (and `Ok` only when none hold),
//! and comes before every other one: that gives `code_before/3` pairs. The
//! precedence list is their topological order; guards that never fail
//! together (WrongRole needs a registered key, UnknownKey an unregistered
//! one) are ordered by the error enum's declaration order, and C-2 accepts
//! any order of such pairs.
//!
//! `cargo test --release facts` fails if the checked-in file differs from
//! a fresh run; `FACTS_WRITE=1` rewrites it.

use crate::gen;
use crate::spec::{apply, live, p_get, r_get, Op, Out, S};
use crate::src::Rng;
use approval_core::{
    ApprovalError as E, Role, DEFAULT_PAGE_SIZE, MAX_ACTION_LEN, MAX_PAGE_SIZE, MAX_PENDING_PER_KEY,
};
use std::collections::{BTreeMap, BTreeSet};

/// Every variant, in declaration order (the tie-break).
const ERRORS: [E; 17] = [
    E::NotOwner,
    E::IndirectCall,
    E::UnknownKey,
    E::WrongRole,
    E::KeyAccountMismatch,
    E::KeyAlreadyRegistered,
    E::KeyNotRegistered,
    E::EmptyAction,
    E::ActionTooLong,
    E::TooManyPending,
    E::RequestNotFound,
    E::AlreadyApproved,
    E::AlreadyRejected,
    E::AgentRevoked,
    E::ActionMismatch,
    E::SelfApproval,
    E::LogFull,
];

fn name(e: E) -> String {
    format!("{e:?}")
}

fn op_name(op: &Op) -> &'static str {
    match op {
        Op::Add { .. } => "add_principal",
        Op::Revoke { .. } => "revoke_key",
        Op::Req { .. } => "request_action",
        Op::Appr { .. } => "approve",
        Op::Rej { .. } => "reject",
    }
}

/// The guards of each operation (its possible errors) and which hold.
fn fails(s: &S, op: &Op) -> (Vec<E>, Vec<E>) {
    let mut all = Vec::new();
    let mut hold = Vec::new();
    let mut g = |e: E, c: bool| {
        all.push(e);
        if c {
            hold.push(e);
        }
    };
    let auth = |g: &mut dyn FnMut(E, bool), c: &crate::spec::C, role: Role| {
        let p = p_get(s, &c.signer_key);
        g(E::IndirectCall, c.predecessor != c.signer);
        g(E::UnknownKey, p.is_none());
        g(E::WrongRole, p.as_ref().is_some_and(|p| p.role != role));
        g(
            E::KeyAccountMismatch,
            p.as_ref().is_some_and(|p| p.account_id != c.signer),
        );
    };
    let decide = |g: &mut dyn FnMut(E, bool), id: u64| {
        let r = r_get(s, id);
        g(E::RequestNotFound, r.is_none());
        g(E::AlreadyApproved, r.is_some_and(|r| r.approval.is_some()));
        g(E::AlreadyRejected, r.is_some_and(|r| r.rejection.is_some()));
        g(E::AgentRevoked, r.is_some_and(|r| !live(s, r)));
    };
    match op {
        Op::Add { caller, key, .. } => {
            g(E::NotOwner, *caller != s.owner);
            g(E::KeyAlreadyRegistered, p_get(s, key).is_some());
            g(E::LogFull, s.g() == u64::MAX);
        }
        Op::Revoke { caller, key, .. } => {
            g(E::NotOwner, *caller != s.owner);
            g(E::KeyNotRegistered, p_get(s, key).is_none());
        }
        Op::Req { c, action, .. } => {
            auth(&mut g, c, Role::Agent);
            g(E::EmptyAction, action.is_empty());
            g(E::ActionTooLong, action.len() > MAX_ACTION_LEN);
            g(
                E::TooManyPending,
                p_get(s, &c.signer_key).is_some_and(|p| p.pending >= MAX_PENDING_PER_KEY),
            );
            g(E::LogFull, s.nr() as u64 == u64::MAX);
        }
        Op::Appr { c, id, action, .. } => {
            auth(&mut g, c, Role::Approver);
            decide(&mut g, *id);
            let r = r_get(s, *id);
            g(E::ActionMismatch, r.is_some_and(|r| r.action != *action));
            g(
                E::SelfApproval,
                r.is_some_and(|r| r.agent_account_id == c.signer),
            );
            g(E::LogFull, s.nl() as u64 == u64::MAX);
        }
        Op::Rej { c, id, .. } => {
            auth(&mut g, c, Role::Approver);
            decide(&mut g, *id);
            let r = r_get(s, *id);
            g(
                E::SelfApproval,
                r.is_some_and(|r| r.agent_account_id == c.signer),
            );
        }
    }
    (all, hold)
}

fn err_of(out: &Out) -> Option<E> {
    out.err()
}

type Pairs = BTreeMap<&'static str, (Vec<E>, BTreeSet<(usize, usize)>)>;

fn idx(e: E) -> usize {
    ERRORS.iter().position(|x| *x == e).unwrap()
}

/// Observes the core on random calls and returns the guard pairs per op.
fn observe(samples: u32) -> Pairs {
    let mut pairs: Pairs = BTreeMap::new();
    let mut rng = Rng(0x5EED_FAC7);
    for n in 0..samples {
        let raw = n % 2 == 0;
        let s = if raw {
            gen::state(&mut rng, true)
        } else {
            let steps = (n % 30) as usize;
            gen::random_walk(&mut rng, steps).0
        };
        let h = crate::spec::Ghost::init();
        let op = match n % 5 {
            0 => gen::op_add(&mut rng, &s),
            1 => gen::op_revoke(&mut rng, &s, &h),
            2 => gen::op_req(&mut rng, &s, &h),
            3 => gen::op_appr(&mut rng, &s, &h),
            _ => gen::op_rej(&mut rng, &s, &h),
        };
        let (all, hold) = fails(&s, &op);
        let mut s2 = s.clone();
        let out = apply(&mut s2, &op);
        let e = pairs
            .entry(op_name(&op))
            .or_insert_with(|| (all.clone(), BTreeSet::new()));
        match err_of(&out) {
            None => assert!(
                hold.is_empty(),
                "{}: Ok although {:?} holds",
                op_name(&op),
                hold
            ),
            Some(got) => {
                assert!(
                    hold.contains(&got),
                    "{}: {:?} returned but only {:?} hold",
                    op_name(&op),
                    got,
                    hold
                );
                for other in &hold {
                    if *other != got {
                        e.1.insert((idx(got), idx(*other)));
                    }
                }
            }
        }
    }
    pairs
}

/// Topological order of `guards` under `before`, ties by declaration order.
fn order(guards: &[E], before: &BTreeSet<(usize, usize)>) -> Vec<E> {
    let mut left: Vec<usize> = guards.iter().map(|e| idx(*e)).collect();
    left.sort();
    left.dedup();
    let mut out = Vec::new();
    while !left.is_empty() {
        let pick = *left
            .iter()
            .find(|g| !left.iter().any(|h| before.contains(&(*h, **g))))
            .expect("observed precedence has a cycle");
        out.push(ERRORS[pick]);
        left.retain(|g| *g != pick);
    }
    out
}

fn render(pairs: &Pairs) -> String {
    let mut out = String::from(
        "%% GENERATED by `FACTS_WRITE=1 cargo test --release facts` in kani/ \
         (src/facts.rs) from the pinned core. Do not edit.\n",
    );
    for e in ERRORS {
        out += &format!("code_error('{}', \"{}\").\n", name(e), e.as_str());
    }
    for (n, v) in [
        ("max_action_len", MAX_ACTION_LEN as u64),
        ("max_pending_per_key", MAX_PENDING_PER_KEY as u64),
        ("default_page_size", DEFAULT_PAGE_SIZE),
        ("max_page_size", MAX_PAGE_SIZE),
    ] {
        out += &format!("code_constant({n}, {v}).\n");
    }
    for (op, (guards, before)) in pairs {
        let list: Vec<String> = order(guards, before)
            .iter()
            .map(|e| format!("'{}'", name(*e)))
            .collect();
        out += &format!("code_precedence({op}, [{}]).\n", list.join(", "));
    }
    for (op, (_, before)) in pairs {
        for (a, b) in before {
            out += &format!(
                "code_before({op}, '{}', '{}').\n",
                name(ERRORS[*a]),
                name(ERRORS[*b])
            );
        }
    }
    out
}

#[test]
fn facts() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../prolog/extracted/code_facts.pl"
    );
    let text = render(&observe(400_000));
    if std::env::var_os("FACTS_WRITE").is_some() {
        std::fs::create_dir_all(std::path::Path::new(path).parent().unwrap()).unwrap();
        std::fs::write(path, &text).unwrap();
    }
    let have = std::fs::read_to_string(path).unwrap_or_default();
    assert!(
        have == text,
        "{path} is stale: run FACTS_WRITE=1 cargo test --release facts"
    );
}
