//! Executable specification of `approval-core` (strategy.md sections 5 and 6.1).
//!
//! Upstream: difflabai/trust-framework `contracts/approval/core/src/lib.rs`
//! Pin:      3426c9246cee98dbfaa3ff7980bd85ff839d60d6
//! sha256:   f5d72cc7bedd0866dfb7891246999315338410f06be00210e3ffd21452ea0d0c
//! Covers:   add_principal, revoke_key, authenticate (through its callers),
//!           live_agent_registration and decidable_request (through approve,
//!           reject and request_status), request_action, approve, reject,
//!           request_status, status_of, proof_revocations, approval,
//!           approvals, ActionRequest::proof; run over `store::ArrStore`.
//!
//! Everything here is written from the catalogue, not from the core: the
//! guard order, the exact `Ok` values and post-states, and the invariants.
//! The core is only ever *called* (in `apply`) and compared against it.
//!
//! Simplifications:
//! - `P` is read as "first matching entry", which is the store's semantics
//!   and a function under INV-0. Only the `h_raw_*` harnesses see
//!   duplicate keys.
//! - `Live` compares `active_from` with `R[i].id` (what the code stores)
//!   rather than with the position `i`. They coincide under INV-1, and this
//!   keeps `expected` meaningful on raw (non-`Inv`) states, which ROB-1 needs.
//! - `#L = MAXU` and `#R = MAXU` cannot occur in a bounded store, so both
//!   `LogFull` cases are left to the M2 ghost-store harnesses (ROB-2).
//!   `G = MAXU` can (the counter is a plain field), so `add_principal`'s
//!   `LogFull` is checked here, from raw states.
//! - `V` (revocations) is read as "first matching entry", like `P`. Under
//!   INV-12 its ids are distinct, so it is a map.

use crate::ids::{Acct, Key, ACTIONS, ACTION_BYTES, NK, OWNER};
use crate::store::{CAP_P, CAP_R, CAP_V};
use approval_core::{
    add_principal, approval, approve, reject, request_action, revoke_key, ActionRequest, Approval,
    ApprovalError as E, ApprovalProof, BlockTime, Caller, Principal, Rejection, Role,
    MAX_ACTION_LEN, MAX_PENDING_PER_KEY,
};

pub type S = crate::store::ArrStore;
pub type C = Caller<Acct, Key>;
pub type Req = ActionRequest<Acct, Key>;
pub type Proof = ApprovalProof<Acct, Key>;

pub const MAXP: u32 = MAX_PENDING_PER_KEY;
pub const N: usize = MAX_ACTION_LEN;

// ---------------------------------------------------------------------------
// Operations
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    Add {
        caller: Acct,
        key: Key,
        acct: Acct,
        role: Role,
    },
    Revoke {
        caller: Acct,
        key: Key,
        t: BlockTime,
    },
    Req {
        c: C,
        action: String,
        t: BlockTime,
    },
    Appr {
        c: C,
        id: u64,
        action: String,
        t: BlockTime,
    },
    Rej {
        c: C,
        id: u64,
        t: BlockTime,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Out {
    Add(Result<Principal<Acct>, E>),
    Revoke(Result<Principal<Acct>, E>),
    Req(Result<Req, E>),
    Appr(Result<Proof, E>),
    Rej(Result<Req, E>),
}

impl Out {
    pub fn is_ok(&self) -> bool {
        self.err().is_none()
    }
    pub fn err(&self) -> Option<E> {
        match self {
            Out::Add(r) => r.as_ref().err().copied(),
            Out::Revoke(r) => r.as_ref().err().copied(),
            Out::Req(r) => r.as_ref().err().copied(),
            Out::Appr(r) => r.as_ref().err().copied(),
            Out::Rej(r) => r.as_ref().err().copied(),
        }
    }
}

/// `op` with its time argument (if it has one) replaced by `t`.
pub fn with_time(op: Op, t: BlockTime) -> Op {
    match op {
        Op::Revoke { caller, key, .. } => Op::Revoke { caller, key, t },
        Op::Req { c, action, .. } => Op::Req { c, action, t },
        Op::Appr { c, id, action, .. } => Op::Appr { c, id, action, t },
        Op::Rej { c, id, .. } => Op::Rej { c, id, t },
        op => op,
    }
}

/// Runs `op` through the real core.
pub fn apply(s: &mut S, op: &Op) -> Out {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => Out::Add(add_principal(s, caller, key.clone(), acct.clone(), *role)),
        Op::Revoke { caller, key, t } => Out::Revoke(revoke_key(s, caller, key, *t)),
        Op::Req { c, action, t } => Out::Req(request_action(s, c, action.clone(), *t)),
        Op::Appr { c, id, action, t } => Out::Appr(approve(s, c, *id, action, *t)),
        Op::Rej { c, id, t } => Out::Rej(reject(s, c, *id, *t)),
    }
}

// ---------------------------------------------------------------------------
// Notation (section 5.0)
// ---------------------------------------------------------------------------

/// `P(k)`.
pub fn p_get(s: &S, k: &Key) -> Option<Principal<Acct>> {
    let mut found: Option<usize> = None;
    for i in 0..CAP_P {
        if found.is_none() && i < s.np() && s.prin(i).0 == *k {
            found = Some(i);
        }
    }
    found.map(|i| s.prin(i).1.clone())
}

pub fn n_r(s: &S) -> u64 {
    s.nr() as u64
}

pub fn n_l(s: &S) -> u64 {
    s.nl() as u64
}

/// `V(g)`: when registration `g` was revoked.
pub fn v_get(s: &S, g: u64) -> Option<BlockTime> {
    let mut found: Option<usize> = None;
    for j in 0..CAP_V {
        if found.is_none() && j < s.nv() && s.rev(j).0 == g {
            found = Some(j);
        }
    }
    found.map(|j| s.rev(j).1)
}

/// `R[i]` by position.
pub fn r_get(s: &S, i: u64) -> Option<&Req> {
    if i < n_r(s) {
        Some(&s.req(i as usize))
    } else {
        None
    }
}

/// `Holds(s,c,ρ)` as the first failing authentication guard (TX-3 order).
pub fn auth_err(s: &S, c: &C, role: Role) -> Option<E> {
    if c.predecessor != c.signer {
        return Some(E::IndirectCall);
    }
    let Some(p) = p_get(s, &c.signer_key) else {
        return Some(E::UnknownKey);
    };
    if p.role != role {
        return Some(E::WrongRole);
    }
    if p.account_id != c.signer {
        return Some(E::KeyAccountMismatch);
    }
    None
}

/// `Live(s,i)`: the agent registration request `r` was made under is in force.
pub fn live(s: &S, r: &Req) -> bool {
    match p_get(s, &r.agent_key) {
        Some(p) => {
            p.account_id == r.agent_account_id && p.role == Role::Agent && p.active_from <= r.id
        }
        None => false,
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum St {
    Pending,
    Approved,
    Rejected,
    Void,
}

/// `Status(s,i)` for `i < #R`.
pub fn status(s: &S, r: &Req) -> St {
    if r.approval.is_some() {
        St::Approved
    } else if r.rejection.is_some() {
        St::Rejected
    } else if live(s, r) {
        St::Pending
    } else {
        St::Void
    }
}

/// `proof(R[i])`, field by field from the catalogue.
pub fn spec_proof(r: &Req) -> Option<Proof> {
    let x = r.approval.as_ref()?;
    Some(ApprovalProof {
        approval_index: x.approval_index,
        request_id: r.id,
        action: r.action.clone(),
        agent_account_id: r.agent_account_id.clone(),
        agent_key: r.agent_key.clone(),
        agent_registration_id: r.agent_registration_id,
        requested_at: r.requested_at,
        approver_account_id: x.approver_account_id.clone(),
        approver_key: x.approver_key.clone(),
        approver_registration_id: x.approver_registration_id,
        approved_at: x.approved_at,
    })
}

pub fn time_le(a: &BlockTime, b: &BlockTime) -> bool {
    a.height <= b.height && a.timestamp_ns <= b.timestamp_ns
}

// ---------------------------------------------------------------------------
// `expected(s, op)`: the exact result, first failing guard wins. Needs no Inv.
// PROP: TX-1 TX-2 TX-3 TX-4 TX-5 TX-7
// ---------------------------------------------------------------------------

/// The request an approver may decide on, or the first failing
/// `decidable_request` guard (TX-5 and TX-7 share them).
pub fn decidable(s: &S, id: u64) -> Result<&Req, E> {
    match r_get(s, id) {
        None => Err(E::RequestNotFound),
        Some(r) if r.approval.is_some() => Err(E::AlreadyApproved),
        Some(r) if r.rejection.is_some() => Err(E::AlreadyRejected),
        Some(r) if !live(s, r) => Err(E::AgentRevoked),
        Some(r) => Ok(r),
    }
}

pub fn expected(s: &S, op: &Op) -> Out {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => Out::Add(if *caller != s.owner {
            Err(E::NotOwner)
        } else if p_get(s, key).is_some() {
            Err(E::KeyAlreadyRegistered)
        } else if s.g() == u64::MAX {
            Err(E::LogFull)
        } else {
            Ok(Principal {
                account_id: acct.clone(),
                role: *role,
                registration_id: s.g(),
                active_from: n_r(s),
                pending: 0,
            })
        }),
        Op::Revoke { caller, key, .. } => Out::Revoke(if *caller != s.owner {
            Err(E::NotOwner)
        } else {
            p_get(s, key).ok_or(E::KeyNotRegistered)
        }),
        Op::Req { c, action, t } => Out::Req(if let Some(e) = auth_err(s, c, Role::Agent) {
            Err(e)
        } else if action.is_empty() {
            Err(E::EmptyAction)
        } else if action.len() > N {
            Err(E::ActionTooLong)
        } else if p_get(s, &c.signer_key).unwrap().pending >= MAXP {
            Err(E::TooManyPending)
        } else {
            Ok(ActionRequest {
                id: n_r(s),
                agent_account_id: c.signer.clone(),
                agent_key: c.signer_key.clone(),
                agent_registration_id: p_get(s, &c.signer_key).unwrap().registration_id,
                action: action.clone(),
                requested_at: *t,
                approval: None,
                rejection: None,
            })
        }),
        Op::Appr { c, id, action, t } => {
            Out::Appr(if let Some(e) = auth_err(s, c, Role::Approver) {
                Err(e)
            } else {
                match decidable(s, *id) {
                    Err(e) => Err(e),
                    Ok(r) if r.action != *action => Err(E::ActionMismatch),
                    Ok(r) if c.signer == r.agent_account_id => Err(E::SelfApproval),
                    // `proof(R'[i])`: the stored id, which INV-1 makes `i`.
                    Ok(r) => Ok(ApprovalProof {
                        approval_index: n_l(s),
                        request_id: r.id,
                        action: r.action.clone(),
                        agent_account_id: r.agent_account_id.clone(),
                        agent_key: r.agent_key.clone(),
                        agent_registration_id: r.agent_registration_id,
                        requested_at: r.requested_at,
                        approver_account_id: c.signer.clone(),
                        approver_key: c.signer_key.clone(),
                        approver_registration_id: p_get(s, &c.signer_key).unwrap().registration_id,
                        approved_at: *t,
                    }),
                }
            })
        }
        Op::Rej { c, id, t } => Out::Rej(if let Some(e) = auth_err(s, c, Role::Approver) {
            Err(e)
        } else {
            match decidable(s, *id) {
                Err(e) => Err(e),
                Ok(r) if c.signer == r.agent_account_id => Err(E::SelfApproval),
                Ok(r) => {
                    let mut out = r.clone();
                    out.rejection = Some(rejection_of(s, c, *t));
                    Ok(out)
                }
            }
        }),
    }
}

/// The rejection record `reject` must write for caller `c` at `t`.
pub fn rejection_of(s: &S, c: &C, t: BlockTime) -> Rejection<Acct, Key> {
    Rejection {
        approver_account_id: c.signer.clone(),
        approver_key: c.signer_key.clone(),
        approver_registration_id: p_get(s, &c.signer_key).unwrap().registration_id,
        rejected_at: t,
    }
}

// ---------------------------------------------------------------------------
// Pre-state snapshots
//
// CBMC blows up (13.5 GB at #P = 3) on `Vec::clone` of a symbolic-length
// vector of non-`Copy` structs, so harnesses never clone a store. They
// snapshot the pre-state into fixed-size arrays (reads only), let the core
// mutate the one store, and compare the result with the snapshot.
// ---------------------------------------------------------------------------

/// Snapshot capacity for requests and the log: `#R ≤ 3` plus one step in
/// the step harnesses, up to `BMC_DEPTH` in `h_bmc_from_init`.
pub const CR: usize = 4;
/// Snapshot capacity for registry entries.
pub const CP: usize = 5;
/// Snapshot capacity for revocations.
pub const CV: usize = 4;

/// Code of an action from the closed universe `{"", ACTIONS..}`.
pub fn act_code(a: &str) -> u8 {
    if a.is_empty() {
        return 0;
    }
    // Byte by byte rather than `a == ACTIONS[i]`: every action is two bytes,
    // and `str` equality's `memcmp` unwinds to the harness bound at each of
    // the dozens of call sites (it ran the MemStore law harnesses out of
    // memory).
    let b = a.as_bytes();
    let mut i = 0;
    while i < ACTION_BYTES.len() {
        if b.len() == 2 && b[0] == ACTION_BYTES[i][0] && b[1] == ACTION_BYTES[i][1] {
            return i as u8 + 1;
        }
        i += 1;
    }
    panic!("action outside the harness universe");
}

pub fn act_str(code: u8) -> &'static str {
    if code == 0 {
        ""
    } else {
        ACTIONS[code as usize - 1]
    }
}

#[derive(Clone, Debug)]
pub struct SnapReq {
    pub id: u64,
    pub aa: Acct,
    pub ak: Key,
    pub ag: u64,
    pub act: u8,
    pub rt: BlockTime,
    pub ap: Option<Approval<Acct, Key>>,
    pub rj: Option<Rejection<Acct, Key>>,
}

impl SnapReq {
    pub fn same_content(&self, r: &Req) -> bool {
        r.id == self.id
            && r.agent_account_id == self.aa
            && r.agent_key == self.ak
            && r.agent_registration_id == self.ag
            && r.action == act_str(self.act)
            && r.requested_at == self.rt
    }
    pub fn same(&self, r: &Req) -> bool {
        self.same_content(r) && r.approval == self.ap && r.rejection == self.rj
    }
}

/// The pre-state, as fixed-size arrays.
#[derive(Clone, Debug)]
pub struct Snap {
    pub owner: Acct,
    pub np: usize,
    pub p: [Option<(Key, Principal<Acct>)>; CP],
    pub nr: usize,
    pub r: [Option<SnapReq>; CR],
    pub nl: usize,
    pub l: [u64; CR],
    pub g: u64,
    pub nv: usize,
    pub v: [(u64, BlockTime); CV],
}

pub fn snap(s: &S) -> Snap {
    assert!(s.np() <= CP && s.nr() <= CR && s.nl() <= CR && s.nv() <= CV);
    let mut out = Snap {
        owner: s.owner.clone(),
        np: s.np(),
        p: [const { None }; CP],
        nr: s.nr(),
        r: [const { None }; CR],
        nl: s.nl(),
        l: [0; CR],
        g: s.g(),
        nv: s.nv(),
        v: [(0, crate::store::T0); CV],
    };
    let mut i = 0;
    while i < out.np {
        out.p[i] = Some(s.prin(i).clone());
        i += 1;
    }
    let mut i = 0;
    while i < out.nr {
        let r = &s.req(i);
        out.r[i] = Some(SnapReq {
            id: r.id,
            aa: r.agent_account_id.clone(),
            ak: r.agent_key.clone(),
            ag: r.agent_registration_id,
            act: act_code(&r.action),
            rt: r.requested_at,
            ap: r.approval.clone(),
            rj: r.rejection.clone(),
        });
        i += 1;
    }
    let mut i = 0;
    while i < out.nl {
        out.l[i] = s.log(i);
        i += 1;
    }
    let mut j = 0;
    while j < out.nv {
        out.v[j] = s.rev(j);
        j += 1;
    }
    out
}

impl Snap {
    /// `P(k)` in the pre-state (first matching entry, like `p_get`).
    pub fn p_get(&self, k: &Key) -> Option<Principal<Acct>> {
        let mut i = 0;
        while i < self.np {
            if let Some((k2, p)) = &self.p[i] {
                if k2 == k {
                    return Some(p.clone());
                }
            }
            i += 1;
        }
        None
    }
    pub fn req(&self, i: usize) -> &SnapReq {
        self.r[i].as_ref().unwrap()
    }
    /// `V(g)` in the pre-state (first matching entry, like `v_get`).
    pub fn v_get(&self, g: u64) -> Option<BlockTime> {
        let mut j = 0;
        while j < self.nv {
            if self.v[j].0 == g {
                return Some(self.v[j].1);
            }
            j += 1;
        }
        None
    }
}

/// `s` equals the snapshot (TX-0).
pub fn same_as(s: &S, pre: &Snap) -> bool {
    if s.owner != pre.owner
        || s.np() != pre.np
        || s.nr() != pre.nr
        || s.nl() != pre.nl
        || s.g() != pre.g
        || s.nv() != pre.nv
    {
        return false;
    }
    let mut j = 0;
    while j < pre.nv {
        if s.rev(j) != pre.v[j] {
            return false;
        }
        j += 1;
    }
    let mut i = 0;
    while i < pre.np {
        if Some(s.prin(i)) != pre.p[i].as_ref() {
            return false;
        }
        i += 1;
    }
    let mut i = 0;
    while i < pre.nr {
        if !pre.req(i).same(&s.req(i)) {
            return false;
        }
        i += 1;
    }
    let mut i = 0;
    while i < pre.nl {
        if s.log(i) != pre.l[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// `next(s, op)` as the catalogue states it, compared field by field with
/// the post-state `s` (Inv states, `out = expected(pre, op)`).
// PROP: TX-1 TX-2 TX-4 TX-5 TX-7
pub fn post_ok(pre: &Snap, s: &S, op: &Op, out: &Out) -> bool {
    if !out.is_ok() {
        return same_as(s, pre);
    }
    if s.owner != pre.owner {
        return false;
    }
    // Registry, as a function over the key universe.
    let mut k = 0;
    while k < NK {
        let key = Key(k);
        let mut want = pre.p_get(&key);
        match op {
            Op::Add {
                key: k2,
                acct,
                role,
                ..
            } if *k2 == key => {
                want = Some(Principal {
                    account_id: acct.clone(),
                    role: *role,
                    registration_id: pre.g,
                    active_from: pre.nr as u64,
                    pending: 0,
                })
            }
            Op::Revoke { key: k2, .. } if *k2 == key => want = None,
            Op::Req { c, .. } if c.signer_key == key => want.as_mut().unwrap().pending += 1,
            Op::Appr { id, .. } | Op::Rej { id, .. } if pre.req(*id as usize).ak == key => {
                want.as_mut().unwrap().pending -= 1
            }
            _ => {}
        }
        if p_get(s, &key) != want {
            return false;
        }
        k += 1;
    }
    // Registration counter and revocations.
    let add_ok = matches!(out, Out::Add(Ok(_)));
    if s.g() != pre.g + add_ok as u64 {
        return false;
    }
    let revoked = match (op, out) {
        (Op::Revoke { t, .. }, Out::Revoke(Ok(p))) => Some((p.registration_id, *t)),
        _ => None,
    };
    if s.nv() != pre.nv + revoked.is_some() as usize {
        return false;
    }
    let mut j = 0;
    while j < pre.nv {
        if s.rev(j) != pre.v[j] {
            return false;
        }
        j += 1;
    }
    if let Some(e) = revoked {
        if s.rev(pre.nv) != e {
            return false;
        }
    }
    // Requests.
    let req_ok = matches!(out, Out::Req(Ok(_)));
    let appr_ok = matches!(out, Out::Appr(Ok(_)));
    if s.nr() != pre.nr + req_ok as usize {
        return false;
    }
    let mut i = 0;
    while i < pre.nr {
        let q = pre.req(i);
        let r = &s.req(i);
        if !q.same_content(r) {
            return false;
        }
        let want_ap = match op {
            Op::Appr { c, id, t, .. } if *id as usize == i => Some(Approval {
                approval_index: pre.nl as u64,
                approver_account_id: c.signer.clone(),
                approver_key: c.signer_key.clone(),
                approver_registration_id: pre.p_get(&c.signer_key).unwrap().registration_id,
                approved_at: *t,
            }),
            _ => q.ap.clone(),
        };
        if r.approval != want_ap {
            return false;
        }
        let want_rj = match op {
            Op::Rej { c, id, t } if *id as usize == i => Some(Rejection {
                approver_account_id: c.signer.clone(),
                approver_key: c.signer_key.clone(),
                approver_registration_id: pre.p_get(&c.signer_key).unwrap().registration_id,
                rejected_at: *t,
            }),
            _ => q.rj.clone(),
        };
        if r.rejection != want_rj {
            return false;
        }
        i += 1;
    }
    if let Out::Req(Ok(r)) = out {
        if s.req(pre.nr) != r {
            return false;
        }
    }
    if let (Op::Rej { id, .. }, Out::Rej(Ok(r))) = (op, out) {
        if s.req(*id as usize) != r {
            return false;
        }
    }
    // Log.
    if s.nl() != pre.nl + appr_ok as usize {
        return false;
    }
    let mut j = 0;
    while j < pre.nl {
        if s.log(j) != pre.l[j] {
            return false;
        }
        j += 1;
    }
    if let Op::Appr { id, .. } = op {
        if appr_ok && s.log(pre.nl) != *id {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// State invariants (section 5.2)
// ---------------------------------------------------------------------------

/// INV-0: one registration per key.
pub fn inv0(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_P {
        for j in 0..CAP_P {
            ok &= !(i < j && j < s.np()) || s.prin(i).0 != s.prin(j).0;
        }
    }
    ok
}

/// INV-1: dense ids.
pub fn inv1(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        ok &= i >= s.nr() || s.req(i).id == i as u64;
    }
    ok
}

/// INV-2: 1 ≤ len(act) ≤ N.
pub fn inv2(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        let a = &s.req(i).action;
        ok &= i >= s.nr() || (!a.is_empty() && a.len() <= N);
    }
    ok
}

/// INV-3: log → request.
pub fn inv3(s: &S) -> bool {
    let mut ok = true;
    for j in 0..CAP_R {
        if j < s.nl() {
            let i = s.log(j);
            ok &= i < n_r(s)
                && matches!(&s.req(i as usize).approval, Some(x) if x.approval_index == j as u64);
        }
    }
    ok
}

/// INV-4: request → log.
pub fn inv4(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        if i < s.nr() {
            if let Some(x) = &s.req(i).approval {
                ok &= x.approval_index < n_l(s) && s.log(x.approval_index as usize) == i as u64;
            }
        }
    }
    ok
}

/// INV-5: separation of duties, for approvals and rejections.
pub fn inv5(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        let r = s.req(i);
        if let Some(x) = &r.approval {
            ok &= i >= s.nr() || x.approver_account_id != r.agent_account_id;
        }
        if let Some(y) = &r.rejection {
            ok &= i >= s.nr() || y.approver_account_id != r.agent_account_id;
        }
    }
    ok
}

/// INV-6: distinct keys, for approvals and rejections.
pub fn inv6(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        let r = s.req(i);
        if let Some(x) = &r.approval {
            ok &= i >= s.nr() || x.approver_key != r.agent_key;
        }
        if let Some(y) = &r.rejection {
            ok &= i >= s.nr() || y.approver_key != r.agent_key;
        }
    }
    ok
}

/// INV-7: registration bound.
pub fn inv7(s: &S) -> bool {
    let mut ok = true;
    for k in 0..CAP_P {
        ok &= k >= s.np() || s.prin(k).1.active_from <= n_r(s);
    }
    ok
}

/// INV-8: registration provenance, including the registration id.
pub fn inv8(s: &S) -> bool {
    let mut ok = true;
    for k in 0..CAP_P {
        let (key, p) = s.prin(k);
        for i in 0..CAP_R {
            let r = s.req(i);
            let applies =
                k < s.np() && i < s.nr() && r.agent_key == *key && i as u64 >= p.active_from;
            ok &= !applies
                || (r.agent_account_id == p.account_id
                    && p.role == Role::Agent
                    && r.agent_registration_id == p.registration_id);
        }
    }
    ok
}

/// `Pend(s,k)`: undecided requests made under `k`'s registration.
pub fn pend(s: &S, k: &Key, from: u64) -> u64 {
    let mut n = 0;
    for i in 0..CAP_R {
        let r = s.req(i);
        if i < s.nr()
            && i as u64 >= from
            && r.agent_key == *k
            && r.approval.is_none()
            && r.rejection.is_none()
        {
            n += 1;
        }
    }
    n
}

/// INV-9: pending count.
pub fn inv9(s: &S) -> bool {
    let mut ok = true;
    for k in 0..CAP_P {
        let (key, p) = s.prin(k);
        ok &= k >= s.np() || (p.pending as u64 == pend(s, key, p.active_from) && p.pending <= MAXP);
    }
    ok
}

/// INV-10: time order within a request.
pub fn inv10(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        let r = s.req(i);
        if let Some(x) = &r.approval {
            ok &= i >= s.nr() || time_le(&r.requested_at, &x.approved_at);
        }
        if let Some(y) = &r.rejection {
            ok &= i >= s.nr() || time_le(&r.requested_at, &y.rejected_at);
        }
    }
    ok
}

/// INV-11: live registration ids are issued (`< G`), distinct, and not
/// revoked.
pub fn inv11(s: &S) -> bool {
    let mut ok = true;
    for k in 0..CAP_P {
        if k < s.np() {
            let g = s.prin(k).1.registration_id;
            ok &= g < s.g() && v_get(s, g).is_none();
            for k2 in 0..CAP_P {
                ok &= !(k < k2 && k2 < s.np()) || s.prin(k2).1.registration_id != g;
            }
        }
    }
    ok
}

/// INV-12: revoked ids are issued and each is revoked once.
pub fn inv12(s: &S) -> bool {
    let mut ok = true;
    for j in 0..CAP_V {
        if j < s.nv() {
            ok &= s.rev(j).0 < s.g();
            for j2 in 0..CAP_V {
                ok &= !(j < j2 && j2 < s.nv()) || s.rev(j2).0 != s.rev(j).0;
            }
        }
    }
    ok
}

/// INV-13: at most one decision per request.
pub fn inv13(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        let r = s.req(i);
        ok &= i >= s.nr() || r.approval.is_none() || r.rejection.is_none();
    }
    ok
}

/// INV-14: recorded registration ids were issued.
pub fn inv14(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        if i < s.nr() {
            let r = s.req(i);
            ok &= r.agent_registration_id < s.g();
            if let Some(x) = &r.approval {
                ok &= x.approver_registration_id < s.g();
            }
            if let Some(y) = &r.rejection {
                ok &= y.approver_registration_id < s.g();
            }
        }
    }
    ok
}

/// INV-15: registration accounting. Every issued id is live or revoked;
/// with INV-11 and INV-12, exactly one of the two.
pub fn inv15(s: &S) -> bool {
    s.np() as u64 + s.nv() as u64 == s.g()
}

/// INV-16: registration binding. A recorded registration id that is live
/// belongs to the key, account and role it was recorded with.
pub fn inv16(s: &S) -> bool {
    let mut ok = true;
    for k in 0..CAP_P {
        let (key, p) = s.prin(k);
        let g = p.registration_id;
        for i in 0..CAP_R {
            if k < s.np() && i < s.nr() {
                let r = s.req(i);
                if r.agent_registration_id == g {
                    ok &= r.agent_key == *key
                        && r.agent_account_id == p.account_id
                        && p.role == Role::Agent;
                }
                if let Some(x) = &r.approval {
                    if x.approver_registration_id == g {
                        ok &= x.approver_key == *key
                            && x.approver_account_id == p.account_id
                            && p.role == Role::Approver;
                    }
                }
                if let Some(y) = &r.rejection {
                    if y.approver_registration_id == g {
                        ok &= y.approver_key == *key
                            && y.approver_account_id == p.account_id
                            && p.role == Role::Approver;
                    }
                }
            }
        }
    }
    ok
}

/// LEM-1: the log has no duplicates.
pub fn lem1(s: &S) -> bool {
    let mut ok = true;
    for i in 0..CAP_R {
        for j in 0..CAP_R {
            ok &= !(i < j && j < s.nl()) || s.log(i) != s.log(j);
        }
    }
    ok
}

/// LEM-2: `#L = #approved ≤ #R`.
pub fn lem2(s: &S) -> bool {
    let mut approved = 0u64;
    for i in 0..CAP_R {
        if i < s.nr() && s.req(i).approval.is_some() {
            approved += 1;
        }
    }
    n_l(s) == approved && n_l(s) <= n_r(s)
}

/// LEM-3: an unapproved request exists ⇒ `#L < #R`.
pub fn lem3(s: &S) -> bool {
    let mut pending = false;
    for i in 0..CAP_R {
        pending |= i < s.nr() && s.req(i).approval.is_none();
    }
    !pending || n_l(s) < n_r(s)
}

/// TR-4 as a state invariant: approval times are non-decreasing along the log.
pub fn tr4(s: &S) -> bool {
    let mut ok = true;
    for j in 1..CAP_R {
        if j < s.nl() {
            let (a, b) = (s.log(j - 1), s.log(j));
            ok &= a < n_r(s) && b < n_r(s);
            if ok {
                match (&s.req(a as usize).approval, &s.req(b as usize).approval) {
                    (Some(xa), Some(xb)) => ok &= time_le(&xa.approved_at, &xb.approved_at),
                    _ => ok = false,
                }
            }
        }
    }
    ok
}

/// `Inv`: the conjunction, for `assume`. `checks::assert_inv` asserts each.
pub fn inv(s: &S) -> bool {
    s.owner == OWNER
        && inv0(s)
        && inv1(s)
        && inv2(s)
        && inv3(s)
        && inv4(s)
        && inv5(s)
        && inv6(s)
        && inv7(s)
        && inv8(s)
        && inv9(s)
        && inv10(s)
        && inv11(s)
        && inv12(s)
        && inv13(s)
        && inv14(s)
        && inv15(s)
        && inv16(s)
        && lem1(s)
        && lem2(s)
        && lem3(s)
        && tr4(s)
}

/// TR-6 potential `Φ(s) = Σ_{k agent} (MAXP − pend_k)`.
pub fn phi(s: &S) -> i64 {
    let mut sum = 0i64;
    let mut k = 0;
    while k < NK {
        if let Some(p) = p_get(s, &Key(k)) {
            if p.role == Role::Agent {
                sum += MAXP as i64 - p.pending as i64;
            }
        }
        k += 1;
    }
    sum
}

// ---------------------------------------------------------------------------
// Ghost history `H` and its invariant `GH` (TR-1)
// ---------------------------------------------------------------------------

/// A recorded runtime caller, as raw identity values (keeps the ghost
/// `Copy`, which CBMC handles far more cheaply than nested clones).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CallRec {
    pub pred: u8,
    pub sig: u8,
    pub key: u8,
}

impl CallRec {
    pub fn of(c: &C) -> Self {
        CallRec {
            pred: c.predecessor.0,
            sig: c.signer.0,
            key: c.signer_key.0,
        }
    }
}

/// What the successful `Req` that created a request saw.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ReqRec {
    pub c: CallRec,
    pub act: u8,
    pub t: BlockTime,
    /// Registration id of `c.signer_key` at the time.
    pub reg: u8,
    /// `P(c.signer_key)` at the time.
    pub acct: u8,
    pub role: Role,
}

/// What the successful `Appr` or `Rej` of a request saw.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct DecRec {
    pub c: CallRec,
    /// The action argument (`Appr` only; 0 for `Rej`).
    pub act: u8,
    pub t: BlockTime,
    /// `P(c.signer_key)` at the time.
    pub acct: u8,
    pub role: Role,
    /// Registration id of `c.signer_key` at the time.
    pub reg: Option<u8>,
    /// Registration id of the request's agent key at the time.
    pub agent_reg: Option<u8>,
    /// `#L` at the time (`Appr` only; 0 for `Rej`).
    pub log_len: u64,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Ghost {
    /// Latest time seen; step inputs are assumed not to precede it (ASM-TIME).
    pub now: BlockTime,
    /// Next fresh registration id. Every successful `Add` takes one, so two
    /// registrations of the same key are told apart. `GH` requires the core's
    /// own registration ids to agree.
    pub next_reg: u8,
    /// Current registration id per key.
    pub reg: [Option<u8>; NK as usize],
    /// Successful `Revoke`s in order: the registration revoked, and when.
    pub nrev: usize,
    pub rev: [Option<(u8, BlockTime)>; CV],
    /// Number of requests recorded.
    pub n: usize,
    pub req: [Option<ReqRec>; CR],
    pub appr: [Option<DecRec>; CR],
    pub rej: [Option<DecRec>; CR],
}

impl Ghost {
    pub fn init() -> Self {
        Ghost {
            now: crate::store::T0,
            next_reg: 0,
            reg: [None; NK as usize],
            nrev: 0,
            rev: [None; CV],
            n: 0,
            req: [None; CR],
            appr: [None; CR],
            rej: [None; CR],
        }
    }
}

/// What `ghost_step` reads from the pre-state: the caller key's
/// registration, the agent key of the decided request, and `#L`. Taken
/// before the step, without snapshotting the whole store.
#[derive(Clone, Debug)]
pub struct GPre {
    pub signer: Option<Principal<Acct>>,
    pub ak: Option<Key>,
    pub nl: u64,
}

impl GPre {
    pub fn of_state(s: &S, op: &Op) -> Self {
        let (signer, ak) = match op {
            Op::Req { c, .. } => (p_get(s, &c.signer_key), None),
            Op::Appr { c, id, .. } | Op::Rej { c, id, .. } => (
                p_get(s, &c.signer_key),
                r_get(s, *id).map(|r| r.agent_key.clone()),
            ),
            _ => (None, None),
        };
        GPre {
            signer,
            ak,
            nl: n_l(s),
        }
    }
    pub fn of_snap(pre: &Snap, op: &Op) -> Self {
        let (signer, ak) = match op {
            Op::Req { c, .. } => (pre.p_get(&c.signer_key), None),
            Op::Appr { c, id, .. } | Op::Rej { c, id, .. } => (
                pre.p_get(&c.signer_key),
                if (*id as usize) < pre.nr {
                    Some(pre.req(*id as usize).ak.clone())
                } else {
                    None
                },
            ),
            _ => (None, None),
        };
        GPre {
            signer,
            ak,
            nl: pre.nl as u64,
        }
    }
}

/// `H'` after `op` ran on a pre-state (seen through `pre`) with result `out`.
pub fn ghost_step(h: &Ghost, pre: &GPre, op: &Op, out: &Out) -> Ghost {
    let mut h = *h;
    match op {
        Op::Revoke { t, .. } | Op::Req { t, .. } | Op::Appr { t, .. } | Op::Rej { t, .. } => {
            h.now = *t
        }
        _ => {}
    }
    if !out.is_ok() {
        return h;
    }
    match op {
        Op::Add { key, .. } => {
            h.reg[key.0 as usize] = Some(h.next_reg);
            h.next_reg += 1;
        }
        Op::Revoke { key, t, .. } => {
            h.rev[h.nrev] = Some((h.reg[key.0 as usize].unwrap(), *t));
            h.nrev += 1;
            h.reg[key.0 as usize] = None;
        }
        Op::Req { c, action, t } => {
            let p = pre.signer.as_ref().unwrap();
            h.req[h.n] = Some(ReqRec {
                c: CallRec::of(c),
                act: act_code(action),
                t: *t,
                reg: h.reg[c.signer_key.0 as usize].unwrap(),
                acct: p.account_id.0,
                role: p.role,
            });
            h.appr[h.n] = None;
            h.rej[h.n] = None;
            h.n += 1;
        }
        Op::Appr { c, id, action, t } => {
            h.appr[*id as usize] = Some(dec_rec(&h, pre, c, act_code(action), *t));
        }
        Op::Rej { c, id, t } => {
            let mut d = dec_rec(&h, pre, c, 0, *t);
            d.log_len = 0;
            h.rej[*id as usize] = Some(d);
        }
    }
    h
}

fn dec_rec(h: &Ghost, pre: &GPre, c: &C, act: u8, t: BlockTime) -> DecRec {
    let p = pre.signer.as_ref().unwrap();
    let ak = pre.ak.as_ref().unwrap();
    DecRec {
        c: CallRec::of(c),
        act,
        t,
        acct: p.account_id.0,
        role: p.role,
        reg: h.reg[c.signer_key.0 as usize],
        agent_reg: h.reg[ak.0 as usize],
        log_len: pre.nl,
    }
}

/// The decision clause shared by approvals and rejections: the deciding
/// call, by a registered approver key of a different account, under the
/// registration recorded in the decision, while the agent registration
/// the request was made under was still in force.
fn dec_ok(
    d: &DecRec,
    q: &ReqRec,
    r: &Req,
    acct: &Acct,
    key: &Key,
    reg: u64,
    t: &BlockTime,
    now: &BlockTime,
) -> bool {
    time_le(t, now)
        && d.c.pred == d.c.sig
        && d.c.sig == acct.0
        && d.c.key == key.0
        && d.acct == acct.0
        && d.role == Role::Approver
        && *acct != r.agent_account_id
        && d.t == *t
        && d.reg.map(|g| g as u64) == Some(reg)
        && d.agent_reg == Some(q.reg)
}

/// `GH(s,H)`. Its approved-request clause is TR-1 (a)-(d), its revocation
/// clause TR-7; the rest makes it inductive.
// PROP: TR-1 TR-7
pub fn gh(s: &S, h: &Ghost) -> bool {
    if h.n != s.nr() || h.n > CR {
        return false;
    }
    // The core issues the ghost's registration ids.
    if s.g() != h.next_reg as u64 {
        return false;
    }
    // Registration ids mirror the registry, are fresh-allocated and distinct.
    let mut k = 0;
    while k < NK as usize {
        let p = p_get(s, &Key(k as u8));
        match h.reg[k] {
            Some(id) => {
                match &p {
                    Some(p) if p.registration_id == id as u64 => {}
                    _ => return false,
                }
                if id >= h.next_reg {
                    return false;
                }
                let mut k2 = k + 1;
                while k2 < NK as usize {
                    if h.reg[k2] == Some(id) {
                        return false;
                    }
                    k2 += 1;
                }
            }
            None => {
                if p.is_some() {
                    return false;
                }
            }
        }
        k += 1;
    }
    // TR-7: the core's revocations are exactly the successful `Revoke`s,
    // with the registration each removed and its time.
    if s.nv() != h.nrev || h.nrev > CV {
        return false;
    }
    let mut j = 0;
    while j < CV {
        if j >= h.nrev {
            break;
        }
        let Some((g, t)) = h.rev[j] else { return false };
        if s.rev(j) != (g as u64, t) || !time_le(&t, &h.now) {
            return false;
        }
        j += 1;
    }
    let mut i = 0;
    while i < CR {
        if i >= h.n {
            break;
        }
        let r = &s.req(i);
        let Some(q) = &h.req[i] else { return false };
        // Times never exceed the clock.
        if !time_le(&r.requested_at, &h.now) {
            return false;
        }
        // TR-1 (a): the creating request, by a registered agent key, under
        // the registration the request records.
        if !(q.c.pred == q.c.sig
            && q.c.sig == r.agent_account_id.0
            && q.c.key == r.agent_key.0
            && q.acct == r.agent_account_id.0
            && q.role == Role::Agent
            && act_str(q.act) == r.action
            && q.t == r.requested_at
            && q.reg as u64 == r.agent_registration_id)
        {
            return false;
        }
        // A live request still runs under the registration it was made under.
        if live(s, r) && h.reg[r.agent_key.0 as usize] != Some(q.reg) {
            return false;
        }
        match (&r.approval, &h.appr[i]) {
            (None, None) => {}
            (Some(x), Some(a)) => {
                // TR-1 (b)-(d): the approving call (b) at log position #L,
                // with the agent registration continuous (c) and both
                // registration ids those in force (d).
                if !(dec_ok(
                    a,
                    q,
                    r,
                    &x.approver_account_id,
                    &x.approver_key,
                    x.approver_registration_id,
                    &x.approved_at,
                    &h.now,
                ) && a.act == q.act
                    && a.log_len == x.approval_index)
                {
                    return false;
                }
            }
            _ => return false,
        }
        match (&r.rejection, &h.rej[i]) {
            (None, None) => {}
            (Some(y), Some(d)) => {
                if !dec_ok(
                    d,
                    q,
                    r,
                    &y.approver_account_id,
                    &y.approver_key,
                    y.approver_registration_id,
                    &y.rejected_at,
                    &h.now,
                ) {
                    return false;
                }
            }
            _ => return false,
        }
        i += 1;
    }
    true
}

/// `approval(s, i)` through the real core, for HIST-5.
pub fn core_approval(s: &S, i: u64) -> Option<Proof> {
    approval(s, i)
}
