//! CUT-1: the footprint premise of the cutoff argument (CUTOFF.md).
//!
//! Each operation runs over [`Track`], a store that forwards to `ArrStore`
//! and records which entries the core names: keys for principals, positions
//! for requests and log slots, registration ids for revocations. The
//! harnesses assert the per-operation footprint table of CUTOFF.md, from a
//! raw state (no `Inv`), so it holds whatever the store contains. Approve
//! and reject assume INV-1 only: with a stored id that differs from its
//! position, `replace_request` writes a second request.
//!
//! Size independence: the core's operations contain no loops (U-1's loop
//! table checks this on every harness's goto program), so each path makes a
//! fixed sequence of store calls, and every path is exercised here (covers
//! below). A bigger store changes the answers, not the number of calls.

use crate::gen;
use crate::ids::{Acct, Key};
use crate::spec::{apply, Op, Out, S};
use crate::src::Src;
use crate::store::ArrStore;
use approval_core::{
    add_principal, approve, reject, request_action, revoke_key, ActionRequest, BlockTime,
    Principal, RegistrationId, RequestId, Store,
};
use core::cell::RefCell;

/// More slots than any operation may use, so an overflow is caught by the
/// footprint assertion rather than by a panic here.
const SLOTS: usize = 4;

/// A set of at most `SLOTS` distinct values, counting how many were added.
#[derive(Clone, Copy)]
struct Set<T: Copy + PartialEq> {
    n: usize,
    v: [Option<T>; SLOTS],
}

impl<T: Copy + PartialEq> Set<T> {
    fn new() -> Self {
        Set {
            n: 0,
            v: [None; SLOTS],
        }
    }
    fn add(&mut self, x: T) {
        let mut i = 0;
        while i < SLOTS {
            if self.v[i] == Some(x) {
                return;
            }
            i += 1;
        }
        if self.n < SLOTS {
            self.v[self.n] = Some(x);
        }
        self.n += 1;
    }
}

/// What one operation named.
#[derive(Clone, Copy)]
pub struct Footprint {
    /// Distinct principal keys looked up, written or removed.
    keys: Set<u8>,
    /// Distinct existing request positions read or replaced.
    reqs: Set<RequestId>,
    /// Distinct existing log slots read.
    slots: Set<u64>,
    /// Distinct registration ids whose revocation was read.
    rev_reads: Set<RegistrationId>,
    pushed_requests: usize,
    pushed_approvals: usize,
    inserted_revocations: usize,
    /// Every store call, counters included.
    calls: usize,
}

impl Footprint {
    fn new() -> Self {
        Footprint {
            keys: Set::new(),
            reqs: Set::new(),
            slots: Set::new(),
            rev_reads: Set::new(),
            pushed_requests: 0,
            pushed_approvals: 0,
            inserted_revocations: 0,
            calls: 0,
        }
    }
}

/// `ArrStore` plus a record of the entries the core names.
pub struct Track<'a> {
    s: &'a mut ArrStore,
    f: RefCell<Footprint>,
}

impl<'a> Track<'a> {
    fn new(s: &'a mut ArrStore) -> Self {
        Track {
            s,
            f: RefCell::new(Footprint::new()),
        }
    }
    fn note(&self, g: impl FnOnce(&mut Footprint)) {
        let mut f = self.f.borrow_mut();
        f.calls += 1;
        g(&mut f);
    }
}

impl Store<Acct, Key> for Track<'_> {
    fn owner(&self) -> &Acct {
        self.note(|_| {});
        self.s.owner()
    }
    fn principal(&self, key: &Key) -> Option<Principal<Acct>> {
        self.note(|f| f.keys.add(key.0));
        self.s.principal(key)
    }
    fn insert_principal(&mut self, key: Key, principal: Principal<Acct>) {
        self.note(|f| f.keys.add(key.0));
        self.s.insert_principal(key, principal)
    }
    fn remove_principal(&mut self, key: &Key) -> Option<Principal<Acct>> {
        self.note(|f| f.keys.add(key.0));
        self.s.remove_principal(key)
    }
    fn request_count(&self) -> u64 {
        self.note(|_| {});
        self.s.request_count()
    }
    fn request(&self, id: RequestId) -> Option<ActionRequest<Acct, Key>> {
        self.note(|f| f.reqs.add(id));
        self.s.request(id)
    }
    fn push_request(&mut self, request: ActionRequest<Acct, Key>) {
        self.note(|f| f.pushed_requests += 1);
        self.s.push_request(request)
    }
    fn replace_request(&mut self, request: ActionRequest<Acct, Key>) {
        self.note(|f| f.reqs.add(request.id));
        self.s.replace_request(request)
    }
    fn approval_count(&self) -> u64 {
        self.note(|_| {});
        self.s.approval_count()
    }
    fn approved_request_id(&self, approval_index: u64) -> Option<RequestId> {
        self.note(|f| f.slots.add(approval_index));
        self.s.approved_request_id(approval_index)
    }
    fn push_approval(&mut self, request_id: RequestId) {
        self.note(|f| f.pushed_approvals += 1);
        self.s.push_approval(request_id)
    }
    fn registration_count(&self) -> u64 {
        self.note(|_| {});
        self.s.registration_count()
    }
    fn increment_registration_count(&mut self) {
        self.note(|_| {});
        self.s.increment_registration_count()
    }
    fn revocation(&self, registration_id: RegistrationId) -> Option<BlockTime> {
        self.note(|f| f.rev_reads.add(registration_id));
        self.s.revocation(registration_id)
    }
    fn insert_revocation(&mut self, registration_id: RegistrationId, revoked_at: BlockTime) {
        self.note(|f| f.inserted_revocations += 1);
        self.s.insert_revocation(registration_id, revoked_at)
    }
}

/// The CUTOFF.md footprint row of an operation.
struct Row {
    keys: usize,
    reqs: usize,
    pushed_requests: usize,
    pushed_approvals: usize,
    inserted_revocations: usize,
    calls: usize,
}

/// Runs `op` on `s` through [`Track`], checks the result equals a run on
/// the bare store, and asserts the footprint row.
fn check(s: &S, op: &Op, row: Row) -> Out {
    let mut bare = s.clone();
    let expect = apply(&mut bare, op);
    let mut copy = s.clone();
    let mut t = Track::new(&mut copy);
    let out = match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => Out::Add(add_principal(
            &mut t,
            caller,
            key.clone(),
            acct.clone(),
            *role,
        )),
        Op::Revoke { caller, key, t: at } => Out::Revoke(revoke_key(&mut t, caller, key, *at)),
        Op::Req { c, action, t: at } => Out::Req(request_action(&mut t, c, action.clone(), *at)),
        Op::Appr {
            c,
            id,
            action,
            t: at,
        } => Out::Appr(approve(&mut t, c, *id, action, *at)),
        Op::Rej { c, id, t: at } => Out::Rej(reject(&mut t, c, *id, *at)),
    };
    let f = *t.f.borrow();
    // PROP: CUT-1
    assert!(out == expect, "CUT-1 tracking is transparent");
    assert!(f.keys.n <= row.keys, "CUT-1 principals touched");
    assert!(f.reqs.n <= row.reqs, "CUT-1 requests touched");
    assert!(f.slots.n == 0, "CUT-1 no log slot read");
    assert!(f.rev_reads.n == 0, "CUT-1 no revocation read");
    assert!(
        f.pushed_requests <= row.pushed_requests,
        "CUT-1 requests appended"
    );
    assert!(
        f.pushed_approvals <= row.pushed_approvals,
        "CUT-1 log slots appended"
    );
    assert!(
        f.inserted_revocations <= row.inserted_revocations,
        "CUT-1 revocations appended"
    );
    assert!(f.calls <= row.calls, "CUT-1 store calls");
    out
}

/// A raw state; in plain mode often a reached one instead, so the `Ok`
/// covers fire (a random raw state almost never admits an approval).
fn start(src: &mut impl Src) -> S {
    match src.reach() {
        Some((s, _)) => s,
        None => gen::state(src, true),
    }
}

pub fn cut_add(src: &mut impl Src) {
    let s = start(src);
    let op = gen::op_add(src, &s);
    // owner, principal, registration_count, request_count,
    // increment_registration_count, insert_principal
    let out = check(
        &s,
        &op,
        Row {
            keys: 1,
            reqs: 0,
            pushed_requests: 0,
            pushed_approvals: 0,
            inserted_revocations: 0,
            calls: 6,
        },
    );
    cover!(out.is_ok(), "cut add: Ok");
}

pub fn cut_revoke(src: &mut impl Src) {
    let s = start(src);
    let op = gen::op_revoke(src, &s, &crate::spec::Ghost::init());
    // owner, remove_principal, insert_revocation
    let out = check(
        &s,
        &op,
        Row {
            keys: 1,
            reqs: 0,
            pushed_requests: 0,
            pushed_approvals: 0,
            inserted_revocations: 1,
            calls: 3,
        },
    );
    cover!(out.is_ok(), "cut revoke: Ok");
}

pub fn cut_request(src: &mut impl Src) {
    let s = start(src);
    let op = gen::op_req(src, &s, &crate::spec::Ghost::init());
    // principal, request_count, insert_principal, push_request
    let out = check(
        &s,
        &op,
        Row {
            keys: 1,
            reqs: 0,
            pushed_requests: 1,
            pushed_approvals: 0,
            inserted_revocations: 0,
            calls: 4,
        },
    );
    cover!(out.is_ok(), "cut request: Ok");
}

pub fn cut_approve(src: &mut impl Src) {
    let s = start(src);
    // `replace_request` writes at the stored id, so without INV-1 the write
    // can land on a second position (raw states touch 2 requests).
    assume!(crate::spec::inv1(&s));
    let op = gen::op_appr(src, &s, &crate::spec::Ghost::init());
    // principal (signer), request, principal (agent), approval_count,
    // insert_principal, replace_request, push_approval
    let out = check(
        &s,
        &op,
        Row {
            keys: 2,
            reqs: 1,
            pushed_requests: 0,
            pushed_approvals: 1,
            inserted_revocations: 0,
            calls: 7,
        },
    );
    cover!(out.is_ok(), "cut approve: Ok");
}

pub fn cut_reject(src: &mut impl Src) {
    let s = start(src);
    // `replace_request` writes at the stored id, so without INV-1 the write
    // can land on a second position (raw states touch 2 requests).
    assume!(crate::spec::inv1(&s));
    let op = gen::op_rej(src, &s, &crate::spec::Ghost::init());
    // principal (signer), request, principal (agent), insert_principal,
    // replace_request
    let out = check(
        &s,
        &op,
        Row {
            keys: 2,
            reqs: 1,
            pushed_requests: 0,
            pushed_approvals: 0,
            inserted_revocations: 0,
            calls: 5,
        },
    );
    cover!(out.is_ok(), "cut reject: Ok");
}
