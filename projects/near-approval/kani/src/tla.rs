//! The TLA+ model `tla/ApprovalCore.tla`, transcribed, and the abstraction
//! map `alpha` from a store to its state (strategy.md section 17).
//!
//! The `h_ref_*` harnesses prove that one step of the real core refines the
//! TLA+ spec, for every `Inv` state within the bounds and every operation:
//!
//! - REF-1 (A1, guard exactness): the core's error is the TLA+ error
//!   operator's (`AddErr`, `RevokeErr`, `RequestErr`, `ApproveErr`,
//!   `RejectErr`), and
//!   `Ok` exactly when the TLA+ action is enabled;
//! - REF-2 (A2, effect exactness): on `Ok`, `alpha(post)` is the TLA+
//!   action's post-state;
//! - REF-3 (A3, stutter): on `Err`, `alpha(post) = alpha(pre)`;
//! - REF-4 (A7, time): the TLA+ operators below never read the block time,
//!   so REF-1 and REF-2 also prove the error and `alpha(post)` independent
//!   of it.
//!
//! This file is checked against the `.tla` text by trace validation
//! (`trace.rs`, REF-5): random traces of the real core are written as a TLA+
//! module that TLC must accept as a behaviour of `Spec`.
//!
//! Field names follow the TLA+ records. Accounts and keys are their `u8`
//! values; payloads are action codes (`spec::act_code`), with `EMPTY` and
//! `TOO_LONG` for the two non-storable classes (A5). The revocation map is
//! abstracted to the set of its keys (block times are not modelled, A7),
//! held as a list compared as a set.

use crate::ids::{Key, NK};
use crate::spec::{act_code, Op, Snap, CR, S};
use approval_core::{ApprovalError as E, Role, MAX_ACTION_LEN, MAX_PENDING_PER_KEY};

/// `Empty`: the `""` action.
pub const EMPTY: u8 = 0;
/// `TooLong`: any action over `MAX_ACTION_LEN` bytes.
pub const TOO_LONG: u8 = 254;

/// Payload class of an action (A5).
pub fn class(a: &str) -> u8 {
    if a.len() > MAX_ACTION_LEN {
        TOO_LONG
    } else {
        act_code(a)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TP {
    pub reg: bool,
    pub acct: u8,
    pub role: Role,
    pub rid: u64,
    pub from: u64,
    pub pending: u32,
}

/// `NoPrincipal`.
pub const NO_P: TP = TP {
    reg: false,
    acct: 0,
    role: Role::Agent,
    rid: 0,
    from: 0,
    pending: 0,
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TR {
    pub acct: u8,
    pub key: u8,
    pub rid: u64,
    pub act: u8,
    pub appr: bool,
    pub aidx: u64,
    pub aacct: u8,
    pub akey: u8,
    pub arid: u64,
    pub rj: bool,
    pub racct: u8,
    pub rkey: u8,
    pub rrid: u64,
}

/// A TLA+ state (the store variables; the ghost is not part of `alpha`).
/// `principals` is total over the key universe `0..NK`.
/// Capacity `C` bounds `#R`, `#L` and `#V`: `CR + 1` in the harnesses (one
/// step from a snapshot), larger for trace validation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct T<const C: usize = { CR + 1 }> {
    pub principals: [TP; NK as usize],
    pub nr: usize,
    pub requests: [TR; C],
    pub nl: usize,
    pub log: [u64; C],
    pub regs: u64,
    pub nv: usize,
    pub revoked: [u64; C],
}

impl<const C: usize> T<C> {
    /// `Init`.
    pub fn init() -> Self {
        T {
            principals: [NO_P; NK as usize],
            nr: 0,
            requests: [BLANK_R; C],
            nl: 0,
            log: [0; C],
            regs: 0,
            nv: 0,
            revoked: [0; C],
        }
    }
}

pub const BLANK_R: TR = TR {
    acct: 0,
    key: 0,
    rid: 0,
    act: 0,
    appr: false,
    aidx: 0,
    aacct: 0,
    akey: 0,
    arid: 0,
    rj: false,
    racct: 0,
    rkey: 0,
    rrid: 0,
};

/// Approval fields: `(aidx, aacct, akey, arid)`.
pub type TAp = (u64, u8, u8, u64);
/// Rejection fields: `(racct, rkey, rrid)`.
pub type TRj = (u8, u8, u64);

/// A request record, with the unused decision fields as `RequestAction`
/// writes them (`aidx = arid = rrid = 0`, `aacct = racct = acct`,
/// `akey = rkey = key`).
pub fn tr(acct: u8, key: u8, rid: u64, act: u8, ap: Option<TAp>, rj: Option<TRj>) -> TR {
    let (appr, (aidx, aacct, akey, arid)) = match ap {
        Some(x) => (true, x),
        None => (false, (0, acct, key, 0)),
    };
    let (rjd, (racct, rkey, rrid)) = match rj {
        Some(x) => (true, x),
        None => (false, (acct, key, 0)),
    };
    TR {
        acct,
        key,
        rid,
        act,
        appr,
        aidx,
        aacct,
        akey,
        arid,
        rj: rjd,
        racct,
        rkey,
        rrid,
    }
}

/// `alpha` of a pre-state snapshot.
pub fn alpha_snap(s: &Snap) -> T {
    let mut t = T::init();
    t.nr = s.nr;
    t.nl = s.nl;
    t.regs = s.g;
    t.nv = s.nv;
    let mut k = 0;
    while k < NK {
        if let Some(p) = s.p_get(&Key(k)) {
            t.principals[k as usize] = TP {
                reg: true,
                acct: p.account_id.0,
                role: p.role,
                rid: p.registration_id,
                from: p.active_from,
                pending: p.pending,
            };
        }
        k += 1;
    }
    let mut i = 0;
    while i < s.nr {
        let q = s.req(i);
        t.requests[i] = tr(
            q.aa.0,
            q.ak.0,
            q.ag,
            q.act,
            q.ap.as_ref().map(t_ap),
            q.rj.as_ref().map(t_rj),
        );
        i += 1;
    }
    let mut j = 0;
    while j < s.nl {
        t.log[j] = s.l[j];
        j += 1;
    }
    let mut j = 0;
    while j < s.nv {
        t.revoked[j] = s.v[j].0;
        j += 1;
    }
    t
}

pub fn t_ap(x: &approval_core::Approval<crate::ids::Acct, Key>) -> TAp {
    (
        x.approval_index,
        x.approver_account_id.0,
        x.approver_key.0,
        x.approver_registration_id,
    )
}

pub fn t_rj(y: &approval_core::Rejection<crate::ids::Acct, Key>) -> TRj {
    (
        y.approver_account_id.0,
        y.approver_key.0,
        y.approver_registration_id,
    )
}

/// `alpha` of a store, through its snapshot.
pub fn alpha(s: &S) -> T {
    alpha_snap(&crate::spec::snap(s))
}

// ---------------------------------------------------------------------------
// Error operators. `None` is "Ok".
// ---------------------------------------------------------------------------

fn add_err<const C: usize>(t: &T<C>, c: u8, k: u8) -> Option<E> {
    if c != crate::ids::OWNER.0 {
        Some(E::NotOwner)
    } else if t.principals[k as usize].reg {
        Some(E::KeyAlreadyRegistered)
    } else {
        None
    }
}

fn revoke_err<const C: usize>(t: &T<C>, c: u8, k: u8) -> Option<E> {
    if c != crate::ids::OWNER.0 {
        Some(E::NotOwner)
    } else if !t.principals[k as usize].reg {
        Some(E::KeyNotRegistered)
    } else {
        None
    }
}

fn auth_err<const C: usize>(t: &T<C>, pred: u8, signer: u8, k: u8, role: Role) -> Option<E> {
    let p = &t.principals[k as usize];
    if pred != signer {
        Some(E::IndirectCall)
    } else if !p.reg {
        Some(E::UnknownKey)
    } else if p.role != role {
        Some(E::WrongRole)
    } else if p.acct != signer {
        Some(E::KeyAccountMismatch)
    } else {
        None
    }
}

fn request_err<const C: usize>(t: &T<C>, pred: u8, signer: u8, k: u8, x: u8) -> Option<E> {
    if let Some(e) = auth_err(t, pred, signer, k, Role::Agent) {
        Some(e)
    } else if x == EMPTY {
        Some(E::EmptyAction)
    } else if x == TOO_LONG {
        Some(E::ActionTooLong)
    } else if t.principals[k as usize].pending >= MAX_PENDING_PER_KEY {
        Some(E::TooManyPending)
    } else {
        None
    }
}

fn live<const C: usize>(t: &T<C>, i: usize) -> bool {
    let r = &t.requests[i];
    let p = &t.principals[r.key as usize];
    p.reg && p.role == Role::Agent && p.acct == r.acct && p.from <= i as u64
}

fn decide_err<const C: usize>(t: &T<C>, i: u64) -> Option<E> {
    if i >= t.nr as u64 {
        return Some(E::RequestNotFound);
    }
    let r = &t.requests[i as usize];
    if r.appr {
        Some(E::AlreadyApproved)
    } else if r.rj {
        Some(E::AlreadyRejected)
    } else if !live(t, i as usize) {
        Some(E::AgentRevoked)
    } else {
        None
    }
}

fn approve_err<const C: usize>(t: &T<C>, pred: u8, signer: u8, k: u8, i: u64, x: u8) -> Option<E> {
    if let Some(e) = auth_err(t, pred, signer, k, Role::Approver) {
        return Some(e);
    }
    if let Some(e) = decide_err(t, i) {
        return Some(e);
    }
    let r = &t.requests[i as usize];
    if r.act != x {
        Some(E::ActionMismatch)
    } else if signer == r.acct {
        Some(E::SelfApproval)
    } else {
        None
    }
}

fn reject_err<const C: usize>(t: &T<C>, pred: u8, signer: u8, k: u8, i: u64) -> Option<E> {
    if let Some(e) = auth_err(t, pred, signer, k, Role::Approver) {
        return Some(e);
    }
    if let Some(e) = decide_err(t, i) {
        return Some(e);
    }
    if signer == t.requests[i as usize].acct {
        Some(E::SelfApproval)
    } else {
        None
    }
}

/// The TLA+ error for `op` from `t`.
pub fn err<const C: usize>(t: &T<C>, op: &Op) -> Option<E> {
    match op {
        Op::Add { caller, key, .. } => add_err(t, caller.0, key.0),
        Op::Revoke { caller, key, .. } => revoke_err(t, caller.0, key.0),
        Op::Req { c, action, .. } => request_err(
            t,
            c.predecessor.0,
            c.signer.0,
            c.signer_key.0,
            class(action),
        ),
        Op::Appr { c, id, action, .. } => approve_err(
            t,
            c.predecessor.0,
            c.signer.0,
            c.signer_key.0,
            *id,
            class(action),
        ),
        Op::Rej { c, id, .. } => reject_err(t, c.predecessor.0, c.signer.0, c.signer_key.0, *id),
    }
}

/// The TLA+ action's post-state. Only meaningful when `err(t, op)` is `None`.
pub fn next<const C: usize>(t: &T<C>, op: &Op) -> T<C> {
    let mut u = *t;
    match op {
        Op::Add {
            key, acct, role, ..
        } => {
            u.principals[key.0 as usize] = TP {
                reg: true,
                acct: acct.0,
                role: *role,
                rid: t.regs,
                from: t.nr as u64,
                pending: 0,
            };
            u.regs += 1;
        }
        Op::Revoke { key, .. } => {
            u.principals[key.0 as usize] = NO_P;
            u.revoked[t.nv] = t.principals[key.0 as usize].rid;
            u.nv += 1;
        }
        Op::Req { c, action, .. } => {
            let k = c.signer_key.0 as usize;
            u.principals[k].pending += 1;
            u.requests[t.nr] = tr(
                c.signer.0,
                c.signer_key.0,
                t.principals[k].rid,
                class(action),
                None,
                None,
            );
            u.nr += 1;
        }
        Op::Appr { c, id, .. } => {
            let i = *id as usize;
            let r = &t.requests[i];
            let arid = t.principals[c.signer_key.0 as usize].rid;
            u.requests[i].appr = true;
            u.requests[i].aidx = t.nl as u64;
            u.requests[i].aacct = c.signer.0;
            u.requests[i].akey = c.signer_key.0;
            u.requests[i].arid = arid;
            decide(&mut u, r.key);
            u.log[t.nl] = *id;
            u.nl += 1;
        }
        Op::Rej { c, id, .. } => {
            let i = *id as usize;
            let r = &t.requests[i];
            let rrid = t.principals[c.signer_key.0 as usize].rid;
            u.requests[i].rj = true;
            u.requests[i].racct = c.signer.0;
            u.requests[i].rkey = c.signer_key.0;
            u.requests[i].rrid = rrid;
            decide(&mut u, r.key);
        }
    }
    u
}

/// `Decide`'s store effect: the agent key's pending count drops by one.
fn decide<const C: usize>(u: &mut T<C>, agent_key: u8) {
    let p = &mut u.principals[agent_key as usize];
    p.pending = if p.pending > 0 { p.pending - 1 } else { 0 };
}

/// `g` is in the first `n` entries of `v`.
fn holds<const C: usize>(v: &[u64; C], n: usize, g: u64) -> bool {
    let mut found = false;
    let mut j = 0;
    while j < C {
        found |= j < n && v[j] == g;
        j += 1;
    }
    found
}

/// `a = b` as TLA+ values: field by field, up to the counts. Not the derived
/// `PartialEq`, which compares the arrays with `memcmp` over all bytes (a
/// loop CBMC can't bound cheaply) and also compares unused slots.
pub fn same<const C: usize>(a: &T<C>, b: &T<C>) -> bool {
    let mut ok = a.nr == b.nr && a.nl == b.nl && a.regs == b.regs && a.nv == b.nv;
    let mut k = 0;
    while k < NK as usize {
        let (p, q) = (&a.principals[k], &b.principals[k]);
        ok &= p.reg == q.reg
            && p.acct == q.acct
            && p.role == q.role
            && p.rid == q.rid
            && p.from == q.from
            && p.pending == q.pending;
        k += 1;
    }
    let mut i = 0;
    while i < C {
        let (r, q) = (&a.requests[i], &b.requests[i]);
        ok &= i >= a.nr
            || (r.acct == q.acct
                && r.key == q.key
                && r.act == q.act
                && r.appr == q.appr
                && r.aidx == q.aidx
                && r.aacct == q.aacct
                && r.akey == q.akey
                && r.rid == q.rid
                && r.arid == q.arid
                && r.rj == q.rj
                && r.racct == q.racct
                && r.rkey == q.rkey
                && r.rrid == q.rrid);
        ok &= i >= a.nl || a.log[i] == b.log[i];
        // The revoked sets: equal counts, and each in the other.
        ok &= i >= a.nv || holds(&b.revoked, b.nv, a.revoked[i]);
        ok &= i >= b.nv || holds(&a.revoked, a.nv, b.revoked[i]);
        i += 1;
    }
    ok
}

/// REF-1..4 for one step: `pre` is the snapshot before, `post` the store
/// after, `core_err` the core's error.
pub fn assert_refines(pre: &Snap, post: &S, op: &Op, core_err: Option<E>) {
    let t = alpha_snap(pre);
    let want = err(&t, op);
    assert!(core_err == want, "REF-1 guard exactness"); // PROP: REF-1 REF-4
    let after = alpha(post);
    if want.is_none() {
        assert!(same(&after, &next(&t, op)), "REF-2 effect exactness"); // PROP: REF-2 REF-4
    } else {
        assert!(same(&after, &t), "REF-3 rejected call stutters"); // PROP: REF-3
    }
}
