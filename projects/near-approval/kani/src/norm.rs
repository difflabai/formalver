//! LEAN-COVER's Rust half (strategy.md section 18.6.1): the class of a
//! footprint view, its representative, and the table carrying the
//! representative's calls back. A line-by-line transcription of
//! `lean/ApprovalLean/Ident.lean` (`cls`, `rep`, `sub`, `Sub.out`); keep the
//! two in step (ASM-NU).
//!
//! `h_link_t_*` (K-LINK-T) proves, for every footprint view `v` (any `u8`
//! identities, any counters, any times):
//!
//!   expect(v).err() = expect(d).err()  and
//!   protocol(v) = transport(sub(v), protocol(d)),   d = rep(cls(v)),
//!
//! and LINK (`link.rs`) runs exactly the views `rep(c)`, `c` in `all_cls()`.
//! Lean proves the same of `cstep` (`Ident.cover`), so `expect`/`protocol`
//! equal `cstep` on every view, not only on LINK's.
//!
//! Everything here is plain loops over fixed arrays (no `Vec` on the Kani
//! path), and every view is read through `Store`'s getters, so `cls` and
//! `sub` see only the footprint.

use crate::checks::LONG;
use crate::ghost::{Call, Rec, Sparse, CAP_CALLS};
use crate::ids::{Acct, Key, ACTIONS, ACTION_BYTES, OWNER};
use crate::spec::{Op, Req, C};
use approval_core::{
    Approval, BlockTime, Caller, Principal, Rejection, Role, Store, MAX_ACTION_LEN,
    MAX_PENDING_PER_KEY,
};

pub const MAXU: u64 = u64::MAX;

// Representative values: distinct, at least 2 apart and away from the
// constants 0, 15, 16, MAXU - 1 and MAXU (Ident.lean).
pub const G_REP: u64 = 1000;
pub const NR_REP: u64 = 2000;
pub const RID0: u64 = 3000;
pub const RID1: u64 = 3100;
pub const AF0: u64 = 4000;
pub const PEND_REP: u32 = 5000;
pub const AF_LE: u64 = 6000;
pub const ID_REP: u64 = 7000;
pub const AF_GT: u64 = 8000;
pub const RID_R: u64 = 9000;
pub const NL_REP: u64 = 10000;

/// The request time and the call time of a representative (Rust only:
/// the model has no times, A7).
pub const T_REQ: BlockTime = BlockTime {
    height: 1,
    timestamp_ns: 1,
};
pub const T_CALL: BlockTime = BlockTime {
    height: 2,
    timestamp_ns: 2,
};

const A_O: Acct = OWNER;
const A_1: Acct = Acct(1);
const A_2: Acct = Acct(2);
const K_0: Key = Key(0);
const K_1: Key = Key(1);
const K_3: Key = Key(3);

// ---------------------------------------------------------------------------
// Classes
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum XCls {
    Eq,
    Pay,
    Empty,
    TooLong,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct BCls {
    pub role: Role,
    pub acct_eq: bool,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct GCls {
    pub role: Role,
    pub acct_eq: bool,
    pub af_le: bool,
    pub pend0: bool,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RCls {
    pub appr: bool,
    pub rej: bool,
    pub acct_eq: bool,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PCls {
    pub role: Role,
    pub acct_eq: bool,
    pub full: bool,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cls {
    /// `a_rel`: 0 the owner, 1 the caller, 2 neither.
    Add {
        caller_owner: bool,
        a_rel: u8,
        role: Role,
        present: bool,
        regs_max: bool,
    },
    Revoke {
        caller_owner: bool,
        present: bool,
    },
    Request {
        pred_eq: bool,
        p: Option<PCls>,
        x: XCls,
        nr_max: bool,
    },
    Approve {
        pred_eq: bool,
        b: Option<BCls>,
        k_eq: bool,
        g: Option<GCls>,
        r: Option<RCls>,
        x: XCls,
        nl_max: bool,
    },
    Reject {
        pred_eq: bool,
        b: Option<BCls>,
        k_eq: bool,
        g: Option<GCls>,
        r: Option<RCls>,
    },
}

// ---------------------------------------------------------------------------
// Enumeration (Ident.allCls; plain mode only)
// ---------------------------------------------------------------------------

#[cfg(not(kani))]
const BOOLS: [bool; 2] = [false, true];
#[cfg(not(kani))]
const ROLES: [Role; 2] = [Role::Agent, Role::Approver];

#[cfg(not(kani))]
fn opts<T: Copy>(l: &[T]) -> Vec<Option<T>> {
    let mut v = vec![None];
    v.extend(l.iter().map(|x| Some(*x)));
    v
}

#[cfg(not(kani))]
fn all_b() -> Vec<BCls> {
    let mut v = vec![];
    for role in ROLES {
        for acct_eq in BOOLS {
            v.push(BCls { role, acct_eq });
        }
    }
    v
}

#[cfg(not(kani))]
fn all_g() -> Vec<GCls> {
    let mut v = vec![];
    for role in ROLES {
        for acct_eq in BOOLS {
            for af_le in BOOLS {
                for pend0 in BOOLS {
                    v.push(GCls {
                        role,
                        acct_eq,
                        af_le,
                        pend0,
                    });
                }
            }
        }
    }
    v
}

#[cfg(not(kani))]
fn all_r() -> Vec<RCls> {
    let mut v = vec![];
    for appr in BOOLS {
        for rej in BOOLS {
            for acct_eq in BOOLS {
                v.push(RCls { appr, rej, acct_eq });
            }
        }
    }
    v
}

#[cfg(not(kani))]
fn all_p() -> Vec<PCls> {
    let mut v = vec![];
    for role in ROLES {
        for acct_eq in BOOLS {
            for full in BOOLS {
                v.push(PCls {
                    role,
                    acct_eq,
                    full,
                });
            }
        }
    }
    v
}

/// Every class, in `Ident.allCls`'s order.
#[cfg(not(kani))]
pub fn all_cls() -> Vec<Cls> {
    let mut v = vec![];
    for caller_owner in BOOLS {
        for a_rel in 0..3 {
            for role in ROLES {
                for present in BOOLS {
                    for regs_max in BOOLS {
                        v.push(Cls::Add {
                            caller_owner,
                            a_rel,
                            role,
                            present,
                            regs_max,
                        });
                    }
                }
            }
        }
    }
    for caller_owner in BOOLS {
        for present in BOOLS {
            v.push(Cls::Revoke {
                caller_owner,
                present,
            });
        }
    }
    for pred_eq in BOOLS {
        for p in opts(&all_p()) {
            for x in [XCls::Empty, XCls::TooLong, XCls::Pay] {
                for nr_max in BOOLS {
                    v.push(Cls::Request {
                        pred_eq,
                        p,
                        x,
                        nr_max,
                    });
                }
            }
        }
    }
    let decs = |approve: bool, v: &mut Vec<Cls>| {
        for pred_eq in BOOLS {
            for b in opts(&all_b()) {
                for k_eq in BOOLS {
                    let gs = if k_eq { vec![None] } else { opts(&all_g()) };
                    for g in gs {
                        for r in opts(&all_r()) {
                            if !approve {
                                v.push(Cls::Reject {
                                    pred_eq,
                                    b,
                                    k_eq,
                                    g,
                                    r,
                                });
                                continue;
                            }
                            let xs: &[XCls] = if r.is_some() {
                                &[XCls::Eq, XCls::Pay, XCls::Empty, XCls::TooLong]
                            } else {
                                &[XCls::Pay, XCls::Empty, XCls::TooLong]
                            };
                            for &x in xs {
                                for nl_max in BOOLS {
                                    v.push(Cls::Approve {
                                        pred_eq,
                                        b,
                                        k_eq,
                                        g,
                                        r,
                                        x,
                                        nl_max,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    };
    decs(true, &mut v);
    decs(false, &mut v);
    v
}

// ---------------------------------------------------------------------------
// The class of a view (Ident.cls)
// ---------------------------------------------------------------------------

/// The kind of an action argument (`TooLong` above `MAX_ACTION_LEN`, as
/// `request_action` checks it).
fn kind(x: &str) -> XCls {
    if x.is_empty() {
        XCls::Empty
    } else if x.len() > MAX_ACTION_LEN {
        XCls::TooLong
    } else {
        XCls::Pay
    }
}

/// `Ident.xcls`: `Eq` when `x` is the request's action.
fn xcls(x: &str, r: &Option<Req>) -> XCls {
    match r {
        Some(r) if r.action == *x => XCls::Eq,
        _ => kind(x),
    }
}

fn bcls(signer: &Acct, b: &Principal<Acct>) -> BCls {
    BCls {
        role: b.role,
        acct_eq: b.account_id == *signer,
    }
}

fn gcls(r: &Req, g: &Principal<Acct>) -> GCls {
    GCls {
        role: g.role,
        acct_eq: g.account_id == r.agent_account_id,
        af_le: g.active_from <= r.id,
        pend0: g.pending == 0,
    }
}

fn rcls(signer: &Acct, r: &Req) -> RCls {
    RCls {
        appr: r.approval.is_some(),
        rej: r.rejection.is_some(),
        acct_eq: r.agent_account_id == *signer,
    }
}

/// The request's agent principal, read only when its key is not the call
/// key (`Ident.gOf`).
fn g_of<T: Store<Acct, Key>>(s: &T, k: &Key, r: &Option<Req>) -> Option<Principal<Acct>> {
    match r {
        Some(r) if r.agent_key != *k => s.principal(&r.agent_key),
        _ => None,
    }
}

pub fn cls<T: Store<Acct, Key>>(s: &T, op: &Op) -> Cls {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => Cls::Add {
            caller_owner: caller == s.owner(),
            a_rel: if acct == s.owner() {
                0
            } else if acct == caller {
                1
            } else {
                2
            },
            role: *role,
            present: s.principal(key).is_some(),
            regs_max: s.registration_count() == MAXU,
        },
        Op::Revoke { caller, key, .. } => Cls::Revoke {
            caller_owner: caller == s.owner(),
            present: s.principal(key).is_some(),
        },
        Op::Req { c, action, .. } => Cls::Request {
            pred_eq: c.predecessor == c.signer,
            p: s.principal(&c.signer_key).map(|p| PCls {
                role: p.role,
                acct_eq: p.account_id == c.signer,
                full: p.pending >= MAX_PENDING_PER_KEY,
            }),
            x: kind(action),
            nr_max: s.request_count() == MAXU,
        },
        Op::Appr { c, id, action, .. } => {
            let r = s.request(*id);
            Cls::Approve {
                pred_eq: c.predecessor == c.signer,
                b: s.principal(&c.signer_key).map(|b| bcls(&c.signer, &b)),
                k_eq: matches!(&r, Some(r) if r.agent_key == c.signer_key),
                g: match &r {
                    Some(rr) => g_of(s, &c.signer_key, &r).map(|g| gcls(rr, &g)),
                    None => None,
                },
                r: r.as_ref().map(|r| rcls(&c.signer, r)),
                x: xcls(action, &r),
                nl_max: s.approval_count() == MAXU,
            }
        }
        Op::Rej { c, id, .. } => {
            let r = s.request(*id);
            Cls::Reject {
                pred_eq: c.predecessor == c.signer,
                b: s.principal(&c.signer_key).map(|b| bcls(&c.signer, &b)),
                k_eq: matches!(&r, Some(r) if r.agent_key == c.signer_key),
                g: match &r {
                    Some(rr) => g_of(s, &c.signer_key, &r).map(|g| gcls(rr, &g)),
                    None => None,
                },
                r: r.as_ref().map(|r| rcls(&c.signer, r)),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The representative of a class (Ident.rep)
// ---------------------------------------------------------------------------

/// Principals a view stores: the call key's and the request key's.
pub const VP: usize = 2;

/// One footprint view: the stored principals in order, the one request
/// the call can read, and the counters. The owner is `o`.
#[derive(Clone, Debug)]
pub struct View {
    pub prins: [Option<(Key, Principal<Acct>)>; VP],
    pub req: Option<Req>,
    pub nr: u64,
    pub nl: u64,
    pub regs: u64,
}

impl View {
    pub fn store(&self) -> Sparse {
        let mut s = Sparse::new(OWNER);
        let mut i = 0;
        while i < VP {
            if let Some((k, p)) = &self.prins[i] {
                s.principals.insert(k.clone(), p.clone());
            }
            i += 1;
        }
        if let Some(r) = &self.req {
            s.requests.insert(r.id, r.clone());
        }
        s.request_count = self.nr;
        s.approval_count = self.nl;
        s.registration_count = self.regs;
        s
    }
}

fn acct_of(b: bool) -> Acct {
    if b {
        A_1
    } else {
        A_2
    }
}

fn x_rep(x: XCls) -> String {
    match x {
        XCls::Eq => ACTIONS[0].to_string(),
        XCls::Pay => ACTIONS[1].to_string(),
        XCls::Empty => String::new(),
        XCls::TooLong => LONG.to_string(),
    }
}

fn p_fix() -> Principal<Acct> {
    Principal {
        account_id: A_2,
        role: Role::Agent,
        registration_id: RID0,
        active_from: AF0,
        pending: 0,
    }
}

fn b_rep(b: &BCls) -> Principal<Acct> {
    Principal {
        account_id: acct_of(b.acct_eq),
        role: b.role,
        registration_id: RID0,
        active_from: AF0,
        pending: 0,
    }
}

fn g_rep(racct: &Acct, g: &GCls) -> Principal<Acct> {
    Principal {
        account_id: if g.acct_eq { racct.clone() } else { A_O },
        role: g.role,
        registration_id: RID1,
        active_from: if g.af_le { AF_LE } else { AF_GT },
        pending: if g.pend0 { 0 } else { PEND_REP },
    }
}

fn r_rep(k_eq: bool, r: &RCls) -> Req {
    Req {
        id: ID_REP,
        agent_account_id: acct_of(r.acct_eq),
        agent_key: if k_eq { K_0 } else { K_1 },
        agent_registration_id: RID_R,
        action: ACTIONS[0].to_string(),
        requested_at: T_REQ,
        approval: r.appr.then(|| Approval {
            approval_index: 4,
            approver_account_id: A_2,
            approver_key: K_3,
            approver_registration_id: 13,
            approved_at: T_REQ,
        }),
        rejection: r.rej.then(|| Rejection {
            approver_account_id: A_2,
            approver_key: K_3,
            approver_registration_id: 13,
            rejected_at: T_REQ,
        }),
    }
}

fn dec_view(b: &Option<BCls>, k_eq: bool, g: &Option<GCls>, r: &Option<RCls>, nl: u64) -> View {
    let racct = r.map_or(A_2, |r| acct_of(r.acct_eq));
    View {
        prins: [
            b.as_ref().map(|b| (K_0, b_rep(b))),
            if k_eq {
                None
            } else {
                g.as_ref().map(|g| (K_1, g_rep(&racct, g)))
            },
        ],
        req: r.as_ref().map(|r| r_rep(k_eq, r)),
        nr: ID_REP + 1,
        nl,
        regs: G_REP,
    }
}

fn caller(pred_eq: bool) -> C {
    Caller {
        predecessor: acct_of(pred_eq),
        signer: A_1,
        signer_key: K_0,
    }
}

pub fn rep(c: &Cls) -> (View, Op) {
    match *c {
        Cls::Add {
            caller_owner,
            a_rel,
            role,
            present,
            regs_max,
        } => (
            View {
                prins: [present.then(|| (K_0, p_fix())), None],
                req: None,
                nr: NR_REP,
                nl: NL_REP,
                regs: if regs_max { MAXU } else { G_REP },
            },
            Op::Add {
                caller: if caller_owner { A_O } else { A_1 },
                key: K_0,
                acct: match a_rel {
                    0 => A_O,
                    1 => A_1,
                    _ => A_2,
                },
                role,
            },
        ),
        Cls::Revoke {
            caller_owner,
            present,
        } => (
            View {
                prins: [present.then(|| (K_0, p_fix())), None],
                req: None,
                nr: NR_REP,
                nl: NL_REP,
                regs: G_REP,
            },
            Op::Revoke {
                caller: if caller_owner { A_O } else { A_1 },
                key: K_0,
                t: T_CALL,
            },
        ),
        Cls::Request {
            pred_eq,
            p,
            x,
            nr_max,
        } => (
            View {
                prins: [
                    p.map(|p| {
                        (
                            K_0,
                            Principal {
                                account_id: acct_of(p.acct_eq),
                                role: p.role,
                                registration_id: RID0,
                                active_from: AF0,
                                pending: if p.full { 16 } else { 15 },
                            },
                        )
                    }),
                    None,
                ],
                req: None,
                nr: if nr_max { MAXU } else { NR_REP },
                nl: NL_REP,
                regs: G_REP,
            },
            Op::Req {
                c: caller(pred_eq),
                action: x_rep(x),
                t: T_CALL,
            },
        ),
        Cls::Approve {
            pred_eq,
            b,
            k_eq,
            g,
            r,
            x,
            nl_max,
        } => (
            dec_view(&b, k_eq, &g, &r, if nl_max { MAXU } else { NL_REP }),
            Op::Appr {
                c: caller(pred_eq),
                id: ID_REP,
                action: x_rep(x),
                t: T_CALL,
            },
        ),
        Cls::Reject {
            pred_eq,
            b,
            k_eq,
            g,
            r,
        } => (
            dec_view(&b, k_eq, &g, &r, NL_REP),
            Op::Rej {
                c: caller(pred_eq),
                id: ID_REP,
                t: T_CALL,
            },
        ),
    }
}

// ---------------------------------------------------------------------------
// Transport back to the view (Ident.sub, Ident.Sub.out)
// ---------------------------------------------------------------------------

/// A first-match table of at most `N` rows. Rows are only ever read at
/// a concrete index below the table's constant size (U-1). Every path
/// through `sub` fills the same slots, an absent row as `None`, so `n`
/// stays concrete under Kani and no write lands at a symbolic index.
#[derive(Clone, Debug)]
pub struct Tab<T, U, const N: usize> {
    n: usize,
    e: [Option<(T, U)>; N],
}

impl<T: Clone, U: Clone, const N: usize> Tab<T, U, N> {
    fn push(&mut self, d: T, v: U) {
        self.slot(Some((d, v)));
    }

    /// The next slot: a row, or `None` where the row is absent.
    fn slot(&mut self, row: Option<(T, U)>) {
        assert!(self.n < N, "table overflow");
        self.e[self.n] = row;
        self.n += 1;
    }
}

/// Table sizes: the most rows `sub` pushes (approve: 5 accounts, 2 keys,
/// 8 counters, 2 payloads, 2 times).
pub const TA: usize = 5;
pub const TK: usize = 2;
pub const TN: usize = 8;
pub const TP: usize = 2;
pub const TT: usize = 2;

/// `x + 1`, saturating (`Ident.inc`).
fn inc(x: u64) -> u64 {
    x.saturating_add(1)
}

pub struct Sub {
    acct: Tab<Acct, Acct, TA>,
    key: Tab<Key, Key, TK>,
    num: Tab<u64, u64, TN>,
    /// Rows keyed by the representative payload's index in `ACTIONS`.
    pay: Tab<usize, String, TP>,
    time: Tab<BlockTime, BlockTime, TT>,
    d_a: Acct,
    d_k: Key,
}

impl Sub {
    fn new(d_a: Acct, d_k: Key) -> Self {
        Sub {
            acct: Tab {
                n: 0,
                e: [None, None, None, None, None],
            },
            key: Tab {
                n: 0,
                e: [None, None],
            },
            num: Tab {
                n: 0,
                e: [None, None, None, None, None, None, None, None],
            },
            pay: Tab {
                n: 0,
                e: [None, None],
            },
            time: Tab {
                n: 0,
                e: [None, None],
            },
            d_a,
            d_k,
        }
    }

    pub fn a(&self, x: &Acct) -> Acct {
        let mut i = 0;
        while i < TA {
            if let Some((d, v)) = &self.acct.e[i] {
                if d == x {
                    return v.clone();
                }
            }
            i += 1;
        }
        self.d_a.clone()
    }

    pub fn k(&self, x: &Key) -> Key {
        let mut i = 0;
        while i < TK {
            if let Some((d, v)) = &self.key.e[i] {
                if d == x {
                    return v.clone();
                }
            }
            i += 1;
        }
        self.d_k.clone()
    }

    /// `Ident.num`: `d` stands for `v`, `d + 1` for `v + 1`, `d - 1` for
    /// `v - 1` (both saturating); anything else is itself.
    pub fn n(&self, x: u64) -> u64 {
        let mut i = 0;
        while i < TN {
            if let Some((d, v)) = self.num.e[i] {
                if x == d {
                    return v;
                } else if x == inc(d) {
                    return inc(v);
                } else if x == d.saturating_sub(1) {
                    return v.saturating_sub(1);
                }
            }
            i += 1;
        }
        x
    }

    fn pend(&self, x: u32) -> u32 {
        self.n(x as u64) as u32
    }

    fn t(&self, x: &BlockTime) -> BlockTime {
        let mut i = 0;
        while i < TT {
            if let Some((d, v)) = &self.time.e[i] {
                if d == x {
                    return *v;
                }
            }
            i += 1;
        }
        *x
    }

    /// `Sub.act`: the representative payloads `ACTIONS[0]`, `ACTIONS[1]`
    /// (`t1`, `t2`) by their row; `""` and too-long strings are kinds and
    /// stay as they are; a payload without a row becomes `""` (`.empty`).
    fn act(&self, x: &str) -> String {
        if x.is_empty() || x.len() > MAX_ACTION_LEN {
            return x.to_string();
        }
        let b = x.as_bytes();
        let mut i = 0;
        while i < TP {
            if let Some((j, v)) = &self.pay.e[i] {
                if b.len() == 2 && b[0] == ACTION_BYTES[*j][0] && b[1] == ACTION_BYTES[*j][1] {
                    return v.clone();
                }
            }
            i += 1;
        }
        String::new()
    }

    fn prin(&self, p: &Principal<Acct>) -> Principal<Acct> {
        Principal {
            account_id: self.a(&p.account_id),
            role: p.role,
            registration_id: self.n(p.registration_id),
            active_from: self.n(p.active_from),
            pending: self.pend(p.pending),
        }
    }

    fn req(&self, r: &Req) -> Req {
        Req {
            id: self.n(r.id),
            agent_account_id: self.a(&r.agent_account_id),
            agent_key: self.k(&r.agent_key),
            agent_registration_id: self.n(r.agent_registration_id),
            action: self.act(&r.action),
            requested_at: self.t(&r.requested_at),
            approval: r.approval.as_ref().map(|d| Approval {
                approval_index: self.n(d.approval_index),
                approver_account_id: self.a(&d.approver_account_id),
                approver_key: self.k(&d.approver_key),
                approver_registration_id: self.n(d.approver_registration_id),
                approved_at: self.t(&d.approved_at),
            }),
            rejection: r.rejection.as_ref().map(|d| Rejection {
                approver_account_id: self.a(&d.approver_account_id),
                approver_key: self.k(&d.approver_key),
                approver_registration_id: self.n(d.approver_registration_id),
                rejected_at: self.t(&d.rejected_at),
            }),
        }
    }

    fn call(&self, c: &Call) -> Call {
        match c {
            Call::IncrementRegistrationCount => Call::IncrementRegistrationCount,
            Call::InsertPrincipal(k, p) => Call::InsertPrincipal(self.k(k), self.prin(p)),
            Call::RemovePrincipal(k) => Call::RemovePrincipal(self.k(k)),
            Call::PushRequest(r) => Call::PushRequest(self.req(r)),
            Call::ReplaceRequest(r) => Call::ReplaceRequest(self.req(r)),
            Call::PushApproval(i) => Call::PushApproval(self.n(*i)),
            Call::InsertRevocation(g, t) => Call::InsertRevocation(self.n(*g), self.t(t)),
        }
    }

    /// `Sub.out` on the calls (the error carries over unchanged).
    pub fn out(&self, rec: &Rec) -> Rec {
        let mut o = rec.clone();
        let mut i = 0;
        while i < CAP_CALLS {
            o.c[i] = rec.c[i].as_ref().map(|c| self.call(c));
            i += 1;
        }
        o
    }

    /// `x == self.out(rec)`, field by field and without building `out`:
    /// under Kani the transported copy (fresh strings and records for
    /// every call kind of every slot) cost several times the rest of
    /// K-LINK-T. Plain mode checks the two agree on every case.
    pub fn same(&self, x: &Rec, rec: &Rec) -> bool {
        if x.n != rec.n {
            return false;
        }
        let mut i = 0;
        while i < CAP_CALLS {
            if !self.same_slot(x, rec, i, F_ALL) {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Slot `i` of `x` is slot `i` of `self.out(rec)`, on the request
    /// fields `f` selects.
    pub fn same_slot(&self, x: &Rec, rec: &Rec, i: usize, f: u8) -> bool {
        match (&x.c[i], &rec.c[i]) {
            (None, None) => true,
            (Some(a), Some(b)) => self.same_call(a, b, f),
            _ => false,
        }
    }

    /// `a == self.call(b)`.
    fn same_call(&self, a: &Call, b: &Call, f: u8) -> bool {
        match (a, b) {
            (Call::IncrementRegistrationCount, Call::IncrementRegistrationCount) => true,
            (Call::InsertPrincipal(ka, pa), Call::InsertPrincipal(kb, pb)) => {
                *ka == self.k(kb) && *pa == self.prin(pb)
            }
            (Call::RemovePrincipal(ka), Call::RemovePrincipal(kb)) => *ka == self.k(kb),
            (Call::PushRequest(ra), Call::PushRequest(rb))
            | (Call::ReplaceRequest(ra), Call::ReplaceRequest(rb)) => self.same_req(ra, rb, f),
            (Call::PushApproval(ia), Call::PushApproval(ib)) => *ia == self.n(*ib),
            (Call::InsertRevocation(ga, ta), Call::InsertRevocation(gb, tb)) => {
                *ga == self.n(*gb) && *ta == self.t(tb)
            }
            _ => false,
        }
    }

    /// `a == self.req(b)` on the fields `f` selects.
    fn same_req(&self, a: &Req, b: &Req, f: u8) -> bool {
        (f & F_IDS == 0
            || a.id == self.n(b.id)
                && a.agent_account_id == self.a(&b.agent_account_id)
                && a.agent_key == self.k(&b.agent_key)
                && a.agent_registration_id == self.n(b.agent_registration_id)
                && a.requested_at == self.t(&b.requested_at))
            && (f & F_ACT == 0 || self.same_act(&a.action, &b.action))
            && (f & F_APPR == 0
                || match (&a.approval, &b.approval) {
                (None, None) => true,
                (Some(x), Some(d)) => {
                    x.approval_index == self.n(d.approval_index)
                        && x.approver_account_id == self.a(&d.approver_account_id)
                        && x.approver_key == self.k(&d.approver_key)
                        && x.approver_registration_id == self.n(d.approver_registration_id)
                        && x.approved_at == self.t(&d.approved_at)
                }
                    _ => false,
                })
            && (f & F_REJ == 0
                || match (&a.rejection, &b.rejection) {
                (None, None) => true,
                (Some(x), Some(d)) => {
                    x.approver_account_id == self.a(&d.approver_account_id)
                        && x.approver_key == self.k(&d.approver_key)
                        && x.approver_registration_id == self.n(d.approver_registration_id)
                        && x.rejected_at == self.t(&d.rejected_at)
                }
                    _ => false,
                })
    }

    /// `a == self.act(x)`.
    fn same_act(&self, a: &str, x: &str) -> bool {
        if x.is_empty() || x.len() > MAX_ACTION_LEN {
            return eq_str(a, x);
        }
        let b = x.as_bytes();
        let mut i = 0;
        while i < TP {
            if let Some((j, v)) = &self.pay.e[i] {
                if b.len() == 2 && b[0] == ACTION_BYTES[*j][0] && b[1] == ACTION_BYTES[*j][1] {
                    return eq_str(a, v);
                }
            }
            i += 1;
        }
        a.is_empty()
    }
}

/// `F_ACT_D` on every representative: each operation of every class of
/// `all_cls`, on its representative view, keeps the stored action.
#[cfg(not(kani))]
pub fn keeps_action_all() -> usize {
    let mut n = 0;
    for c in all_cls() {
        let (dv, dop) = rep(&c);
        let d = dv.store();
        let ed = expect(&d, &dop);
        let pd = protocol(&d, &dop, &ed);
        let mut i = 0;
        while i < CAP_CALLS {
            assert!(keeps_action(&pd, i, &d, &dop), "F_ACT_D on {c:?}");
            i += 1;
        }
        n += 1;
    }
    n
}

/// A request call in slot `i` carries the action stored at its id.
fn keeps_action<T: Store<Acct, Key>>(rec: &Rec, i: usize, s: &T, op: &Op) -> bool {
    match (&rec.c[i], op) {
        (Some(Call::ReplaceRequest(x)), Op::Appr { id, .. }) => match s.request(*id) {
            Some(r) => eq_str(&x.action, &r.action),
            None => false,
        },
        _ => true,
    }
}

/// `a == b`, byte by byte up to the alphabet's two bytes (as
/// `spec::act_code`): `str` equality's `memcmp` alone ran K-LINK-T approve
/// out of memory. Longer strings fall back to `==`.
fn eq_str(a: &str, b: &str) -> bool {
    let (x, y) = (a.as_bytes(), b.as_bytes());
    if x.len() != y.len() {
        false
    } else if x.len() == 0 {
        true
    } else if x.len() == 1 {
        x[0] == y[0]
    } else if x.len() == 2 {
        x[0] == y[0] && x[1] == y[1]
    } else {
        a == b
    }
}

/// `Ident.pRows`, for a principal that may be absent.
fn p_rows(t: &mut Tab<u64, u64, TN>, rid: u64, af: u64, pend: u64, p: Option<&Principal<Acct>>) {
    t.slot(p.map(|p| (rid, p.registration_id)));
    t.slot(p.map(|p| (af, p.active_from)));
    t.slot(p.map(|p| (pend, p.pending as u64)));
}

/// `Ident.payRows`: a row for a payload action.
fn pay_row(t: &mut Tab<usize, String, TP>, j: usize, x: Option<&str>) {
    t.slot(x.filter(|x| kind(x) == XCls::Pay).map(|x| (j, x.to_string())));
}

/// `Ident.sub.decAccts`, `decKeys`, `decNums` and the shared rows of
/// approve and reject.
fn sub_dec<T: Store<Acct, Key>>(s: &T, c: &C, id: u64, t: &BlockTime) -> Sub {
    let (signer, pred, k) = (&c.signer, &c.predecessor, &c.signer_key);
    let r = s.request(id);
    let b = s.principal(k);
    let g = g_of(s, k, &r);
    let mut o = Sub::new(signer.clone(), k.clone());
    o.acct.push(A_1, signer.clone());
    o.acct.slot(r.as_ref().map(|r| (A_2, r.agent_account_id.clone())));
    o.acct.slot(g.as_ref().map(|g| (A_O, g.account_id.clone())));
    o.acct.push(A_2, pred.clone());
    o.acct.slot(b.as_ref().map(|b| (A_2, b.account_id.clone())));
    o.key.push(K_0, k.clone());
    o.key.slot(r.as_ref().map(|r| (K_1, r.agent_key.clone())));
    o.num.slot(b.as_ref().map(|b| (RID0, b.registration_id)));
    // g is only ever present with r (g_of reads r's key).
    let (af, pd) = match (&r, &g) {
        (Some(r), Some(g)) => (
            if g.active_from <= r.id { AF_LE } else { AF_GT },
            if g.pending == 0 { 0 } else { PEND_REP as u64 },
        ),
        _ => (0, 0),
    };
    p_rows(&mut o.num, RID1, af, pd, r.as_ref().and(g.as_ref()));
    o.num.push(ID_REP, id);
    o.num.slot(r.as_ref().map(|r| (RID_R, r.agent_registration_id)));
    pay_row(&mut o.pay, 0, r.as_ref().map(|r| r.action.as_str()));
    o.time.slot(r.as_ref().map(|r| (T_REQ, r.requested_at)));
    o.time.push(T_CALL, *t);
    o
}

pub fn sub<T: Store<Acct, Key>>(s: &T, op: &Op) -> Sub {
    match op {
        Op::Add {
            caller, key, acct, ..
        } => {
            let mut o = Sub::new(acct.clone(), key.clone());
            o.acct.push(A_O, s.owner().clone());
            o.acct.push(A_1, caller.clone());
            o.acct.push(A_2, acct.clone());
            o.key.push(K_0, key.clone());
            let g = s.registration_count();
            o.num.push(if g == MAXU { MAXU } else { G_REP }, g);
            o.num.push(NR_REP, s.request_count());
            o
        }
        Op::Revoke { caller, key, t } => {
            let mut o = Sub::new(caller.clone(), key.clone());
            o.acct.push(A_O, s.owner().clone());
            o.acct.push(A_1, caller.clone());
            o.key.push(K_0, key.clone());
            o.num.slot(s.principal(key).map(|p| (RID0, p.registration_id)));
            o.time.push(T_CALL, *t);
            o
        }
        Op::Req { c, action, t } => {
            let mut o = Sub::new(c.signer.clone(), c.signer_key.clone());
            o.acct.push(A_1, c.signer.clone());
            o.acct.push(A_2, c.predecessor.clone());
            let p = s.principal(&c.signer_key);
            o.acct.slot(p.as_ref().map(|p| (A_2, p.account_id.clone())));
            o.key.push(K_0, c.signer_key.clone());
            let pd = match &p {
                Some(p) if p.pending >= MAX_PENDING_PER_KEY => 16,
                _ => 15,
            };
            p_rows(&mut o.num, RID0, AF0, pd, p.as_ref());
            let nr = s.request_count();
            o.num.push(if nr == MAXU { MAXU } else { NR_REP }, nr);
            pay_row(&mut o.pay, 1, Some(action));
            o.time.push(T_CALL, *t);
            o
        }
        Op::Appr { c, id, action, t } => {
            let mut o = sub_dec(s, c, *id, t);
            let nl = s.approval_count();
            o.num.push(if nl == MAXU { MAXU } else { NL_REP }, nl);
            pay_row(&mut o.pay, 1, Some(action));
            o
        }
        Op::Rej { c, id, t } => sub_dec(s, c, *id, t),
    }
}

// The representatives' pending values are 15 and 16 (Ident.lean).
const _: () = assert!(MAX_PENDING_PER_KEY == 16);

// ---------------------------------------------------------------------------
// h_link_t_* (K-LINK-T)
// ---------------------------------------------------------------------------

use crate::ghost::{expect, protocol};
use crate::src::Src;

/// Any `u8` identity under Kani; plain mode leans to three values so
/// equalities occur.
fn ident(src: &mut impl Src) -> u8 {
    if src.hint(70) {
        src.below(3)
    } else {
        src.below(255)
    }
}

fn any_role(src: &mut impl Src) -> Role {
    if src.bool() {
        Role::Agent
    } else {
        Role::Approver
    }
}

fn any_time(src: &mut impl Src) -> BlockTime {
    BlockTime {
        height: src.u64(),
        timestamp_ns: src.u64(),
    }
}

fn any_prin(src: &mut impl Src, acct: Acct) -> Principal<Acct> {
    Principal {
        account_id: acct,
        role: any_role(src),
        registration_id: src.u64(),
        active_from: src.u64(),
        pending: src.u32(),
    }
}

/// A payload from the harness alphabet (stored actions are payloads: INV-2).
fn payload(src: &mut impl Src) -> String {
    ACTIONS[src.below(ACTIONS.len() as u8) as usize].to_string()
}

/// The call's action: from the alphabet (`xk` 0), `""` (1) or too long
/// (2). Fixed per Kani harness so string lengths stay concrete.
fn action(src: &mut impl Src, xk: u8) -> String {
    match xk {
        0 => payload(src),
        1 => String::new(),
        _ => LONG.to_string(),
    }
}

/// What a K-LINK-T harness asserts: `CHK_ERR` the error and the number
/// of calls, `chk_slot(i)` call slot `i`. Approve checks one at a time in
/// separate harnesses: the whole comparison does not fit in memory, while
/// each part's cone does. The parts of a family together assert
/// `ev.err() == ed.err()` and `sub.same(pv, pd)`.
pub const CHK_ERR: u8 = 1;
pub const CHK_ALL: u8 = u8::MAX;

pub const fn chk_slot(i: usize) -> u8 {
    2 << i
}

/// Which fields of a request call a slot check compares (`F_ALL` every
/// one). Approve's `ReplaceRequest` slot is checked a group at a time.
pub const F_IDS: u8 = 1;
pub const F_ACT: u8 = 2;
pub const F_APPR: u8 = 4;
pub const F_REJ: u8 = 8;
pub const F_ALL: u8 = u8::MAX;

/// Approve's stored action alone still does not fit: both views' strings
/// flow through two runs of the core. `F_ACT` is checked in three parts
/// that each follow one side, and together give `same_act` on the slot:
/// `F_ACT_V` the view's call carries its stored action, `F_ACT_D` the
/// representative's carries its own, `F_ACT_S` the two stored actions
/// correspond under `sub`. `F_ACT_D` is about the representatives alone,
/// a finite set, so `keeps_action_all` checks it on every one in plain
/// mode rather than in a Kani harness (which also ran out of memory).
pub const F_ACT_V: u8 = 16;
pub const F_ACT_D: u8 = 32;
pub const F_ACT_S: u8 = 64;

/// One footprint view of any identities, counters and times, and one
/// operation of kind `kind` (0 add .. 4 reject) on it: `expect`/`protocol`
/// on the view equal those on its representative, carried back by `sub`.
// PROP: K-LINK-T
pub fn link_t(src: &mut impl Src, kind: u8, xk: u8, chk: u8, f: u8) {
    let owner = Acct(ident(src));
    let signer = Acct(ident(src));
    let k = Key(ident(src));
    let mut s = Sparse::new(owner.clone());
    if src.bool() {
        let a = if src.hint(60) {
            signer.clone()
        } else {
            Acct(ident(src))
        };
        s.principals.insert(k.clone(), any_prin(src, a));
    }
    let id = src.u64();
    let mut stored = None;
    if kind >= 3 && src.bool() {
        let rk = if src.hint(40) { k.clone() } else { Key(ident(src)) };
        let ra = Acct(ident(src));
        let r = Req {
            id,
            agent_account_id: ra.clone(),
            agent_key: rk.clone(),
            agent_registration_id: src.u64(),
            action: payload(src),
            requested_at: any_time(src),
            approval: if src.bool() && !src.hint(70) {
                Some(Approval {
                    approval_index: src.u64(),
                    approver_account_id: Acct(ident(src)),
                    approver_key: Key(ident(src)),
                    approver_registration_id: src.u64(),
                    approved_at: any_time(src),
                })
            } else {
                None
            },
            rejection: if src.bool() && !src.hint(70) {
                Some(Rejection {
                    approver_account_id: Acct(ident(src)),
                    approver_key: Key(ident(src)),
                    approver_registration_id: src.u64(),
                    rejected_at: any_time(src),
                })
            } else {
                None
            },
        };
        if rk != k && src.bool() {
            let a = if src.hint(70) {
                ra.clone()
            } else {
                Acct(ident(src))
            };
            let mut g = any_prin(src, a);
            if src.hint(70) {
                g.role = Role::Agent;
                g.active_from = 0;
            }
            s.principals.insert(rk, g);
        }
        stored = Some(r.action.clone());
        s.requests.insert(id, r);
    }
    s.request_count = src.u64();
    s.approval_count = src.u64();
    s.registration_count = src.u64();
    let pred = if src.hint(80) {
        signer.clone()
    } else {
        Acct(ident(src))
    };
    let c = Caller {
        predecessor: pred,
        signer: signer.clone(),
        signer_key: k.clone(),
    };
    let t = any_time(src);
    let op = match kind {
        0 => Op::Add {
            caller: if src.hint(70) { owner } else { Acct(ident(src)) },
            key: k,
            acct: Acct(ident(src)),
            role: any_role(src),
        },
        1 => Op::Revoke {
            caller: if src.hint(70) { owner } else { Acct(ident(src)) },
            key: k,
            t,
        },
        2 => Op::Req {
            c,
            action: action(src, xk),
            t,
        },
        3 => {
            let mut x = action(src, xk);
            if let Some(a) = stored {
                if xk == 0 && src.hint(70) {
                    x = a;
                }
            }
            Op::Appr { c, id, action: x, t }
        }
        _ => Op::Rej { c, id, t },
    };

    let cl = cls(&s, &op);
    let (dv, dop) = rep(&cl);
    let d = dv.store();
    let ev = expect(&s, &op);
    let pv = protocol(&s, &op, &ev);
    let ed = expect(&d, &dop);
    let pd = protocol(&d, &dop, &ed);
    if xk == 0 {
        cover!(ev.is_ok(), "link_t: Ok");
    }
    cover!(!ev.is_ok(), "link_t: an error");
    let tr = sub(&s, &op);
    if chk & CHK_ERR != 0 {
        assert!(ev.err() == ed.err(), "K-LINK-T: the representative's error");
        assert!(pv.n == pd.n, "K-LINK-T: the representative's number of calls");
    }
    // An empty or too-long action fails request and approve (it is never
    // a stored payload) and makes no call, on both views: so every slot
    // is `None` on both sides and the slot checks below hold.
    if xk != 0 {
        assert!(!ev.is_ok(), "K-LINK-T: a non-payload action fails");
        assert!(pv == Rec::new() && pd == Rec::new(), "K-LINK-T: no calls on failure");
        return;
    }
    let mut i = 0;
    while i < CAP_CALLS {
        if chk & chk_slot(i) != 0 {
            assert!(tr.same_slot(&pv, &pd, i, f), "K-LINK-T: the representative's call, carried back");
            if f & F_ACT_V != 0 {
                assert!(keeps_action(&pv, i, &s, &op), "K-LINK-T: the view's request keeps its action");
            }
            if f & F_ACT_D != 0 {
                assert!(keeps_action(&pd, i, &d, &dop), "K-LINK-T: the representative's request keeps its action");
            }
        }
        i += 1;
    }
    if f & F_ACT_S != 0 {
        if let (Op::Appr { id, .. }, Op::Appr { id: did, .. }) = (&op, &dop) {
            if let (Some(r), Some(dr)) = (s.request(*id), d.request(*did)) {
                assert!(tr.same_act(&r.action, &dr.action), "K-LINK-T: the stored actions correspond");
            }
        }
    }
    #[cfg(not(kani))]
    assert_eq!(tr.same(&pv, &pd), pv == tr.out(&pd), "Sub::same is out, then ==");
}
