//! The TLA+ model `tla/ApprovalCore.tla`, transcribed, and the abstraction
//! map `alpha` from a store to its state (strategy.md section 17).
//!
//! The `h_ref_*` harnesses prove that one step of the real core refines the
//! TLA+ spec, for every `Inv` state within the bounds and every operation:
//!
//! - REF-1 (A1, guard exactness): the core's error is the TLA+ error
//!   operator's (`AddErr`, `RevokeErr`, `RequestErr`, `ApproveErr`), and
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
//! `TOO_LONG` for the two non-storable classes (A5).

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
    pub from: u64,
    pub pending: u32,
}

/// `NoPrincipal`.
pub const NO_P: TP = TP {
    reg: false,
    acct: 0,
    role: Role::Agent,
    from: 0,
    pending: 0,
};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TR {
    pub acct: u8,
    pub key: u8,
    pub act: u8,
    pub appr: bool,
    pub aidx: u64,
    pub aacct: u8,
    pub akey: u8,
}

/// A TLA+ state (the store variables; the ghost is not part of `alpha`).
/// `principals` is total over the key universe `0..NK`.
/// Capacity `C` bounds `#R` and `#L`: `CR + 1` in the harnesses (one step
/// from a snapshot), larger for trace validation.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct T<const C: usize = { CR + 1 }> {
    pub principals: [TP; NK as usize],
    pub nr: usize,
    pub requests: [TR; C],
    pub nl: usize,
    pub log: [u64; C],
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
        }
    }
}

pub const BLANK_R: TR = TR {
    acct: 0,
    key: 0,
    act: 0,
    appr: false,
    aidx: 0,
    aacct: 0,
    akey: 0,
};

/// A request record, with the unused approval fields as `RequestAction`
/// writes them (`aidx = 0`, `aacct = acct`, `akey = key`).
pub fn tr(acct: u8, key: u8, act: u8, ap: Option<(u64, u8, u8)>) -> TR {
    match ap {
        Some((aidx, aacct, akey)) => TR {
            acct,
            key,
            act,
            appr: true,
            aidx,
            aacct,
            akey,
        },
        None => TR {
            acct,
            key,
            act,
            appr: false,
            aidx: 0,
            aacct: acct,
            akey: key,
        },
    }
}

/// `alpha` of a pre-state snapshot.
pub fn alpha_snap(s: &Snap) -> T {
    let mut t = T::init();
    t.nr = s.nr;
    t.nl = s.nl;
    let mut k = 0;
    while k < NK {
        if let Some(p) = s.p_get(&Key(k)) {
            t.principals[k as usize] = TP {
                reg: true,
                acct: p.account_id.0,
                role: p.role,
                from: p.active_from,
                pending: p.pending,
            };
        }
        k += 1;
    }
    let mut i = 0;
    while i < s.nr {
        let q = s.req(i);
        let ap =
            q.ap.as_ref()
                .map(|x| (x.approval_index, x.approver_account_id.0, x.approver_key.0));
        t.requests[i] = tr(q.aa.0, q.ak.0, q.act, ap);
        i += 1;
    }
    let mut j = 0;
    while j < s.nl {
        t.log[j] = s.l[j];
        j += 1;
    }
    t
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

fn approve_err<const C: usize>(t: &T<C>, pred: u8, signer: u8, k: u8, i: u64, x: u8) -> Option<E> {
    if let Some(e) = auth_err(t, pred, signer, k, Role::Approver) {
        return Some(e);
    }
    if i >= t.nr as u64 {
        return Some(E::RequestNotFound);
    }
    let r = &t.requests[i as usize];
    if r.appr {
        Some(E::AlreadyApproved)
    } else if !live(t, i as usize) {
        Some(E::AgentRevoked)
    } else if r.act != x {
        Some(E::ActionMismatch)
    } else if signer == r.acct {
        Some(E::SelfApproval)
    } else {
        None
    }
}

/// The TLA+ error for `op` from `t`.
pub fn err<const C: usize>(t: &T<C>, op: &Op) -> Option<E> {
    match op {
        Op::Add { caller, key, .. } => add_err(t, caller.0, key.0),
        Op::Revoke { caller, key } => revoke_err(t, caller.0, key.0),
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
                from: t.nr as u64,
                pending: 0,
            };
        }
        Op::Revoke { key, .. } => u.principals[key.0 as usize] = NO_P,
        Op::Req { c, action, .. } => {
            u.principals[c.signer_key.0 as usize].pending += 1;
            u.requests[t.nr] = tr(c.signer.0, c.signer_key.0, class(action), None);
            u.nr += 1;
        }
        Op::Appr { c, id, .. } => {
            let i = *id as usize;
            let ak = t.requests[i].key as usize;
            u.requests[i] = tr(
                t.requests[i].acct,
                t.requests[i].key,
                t.requests[i].act,
                Some((t.nl as u64, c.signer.0, c.signer_key.0)),
            );
            let p = &mut u.principals[ak];
            p.pending = if p.pending > 0 { p.pending - 1 } else { 0 };
            u.log[t.nl] = *id;
            u.nl += 1;
        }
    }
    u
}

/// REF-1..4 for one step: `pre` is the snapshot before, `post` the store
/// after, `core_err` the core's error.
pub fn assert_refines(pre: &Snap, post: &S, op: &Op, core_err: Option<E>) {
    let t = alpha_snap(pre);
    let want = err(&t, op);
    assert!(core_err == want, "REF-1 guard exactness"); // PROP: REF-1 REF-4
    let after = alpha(post);
    if want.is_none() {
        assert!(after == next(&t, op), "REF-2 effect exactness"); // PROP: REF-2 REF-4
    } else {
        assert!(after == t, "REF-3 rejected call stutters"); // PROP: REF-3
    }
}
