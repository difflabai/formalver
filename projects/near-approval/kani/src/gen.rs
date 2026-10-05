//! Bounded state and operation builders (strategy.md sections 6.1 and 6.3).
//!
//! Bounds: `#P, #R, #L ≤ 3`; accounts and keys from 4 values each; actions
//! from [`ACTIONS`] (plus `""` in operations); ids, counters, `active_from`,
//! `pending` and times free.

use crate::ids::{Acct, ACTION_BYTES, OWNER};
use crate::spec::{act_code, apply, ghost_step, snap, ApprRec, CallRec, Ghost, Op, ReqRec, C, S};
use crate::src::Src;
use crate::store::ArrStore;
use approval_core::{ActionRequest, Approval, BlockTime, Caller, Principal, Role};

pub const MAX_P: u8 = 3;
pub const MAX_R: u8 = 3;

pub fn role(src: &mut impl Src) -> Role {
    if src.bool() {
        Role::Agent
    } else {
        Role::Approver
    }
}

pub fn time(src: &mut impl Src) -> BlockTime {
    BlockTime {
        height: src.u64(),
        timestamp_ns: src.u64(),
    }
}

/// One of [`ACTIONS`], built from its bytes so its length is concrete.
pub fn alphabet_action(src: &mut impl Src) -> String {
    let b = ACTION_BYTES[src.below(ACTION_BYTES.len() as u8) as usize];
    String::from_utf8(b.to_vec()).unwrap()
}

/// The action stored in a request: one of [`ACTIONS`], or also `""` in raw
/// plain-mode states (the core never inspects a stored action's length).
pub fn stored_action(src: &mut impl Src, raw: bool) -> String {
    if raw && src.hint(20) {
        return String::new();
    }
    alphabet_action(src)
}

/// An operation argument: `""` if `src.empty_action()`, else one of [`ACTIONS`].
pub fn op_action(src: &mut impl Src) -> String {
    if src.empty_action() {
        return String::new();
    }
    alphabet_action(src)
}

/// An arbitrary store within the bounds.
///
/// With `raw = false` the result is meant to be filtered by `assume(inv)`,
/// so request ids and approval indices that INV-1/INV-3/INV-4 pin down are
/// fixed instead of drawn (no loss of generality under the assumption).
/// With `raw = true` every field is free and duplicate keys are possible.
pub fn state(src: &mut impl Src, raw: bool) -> S {
    let mut s: S = ArrStore::new(if raw { src.acct() } else { OWNER });
    let shape = src.shape();
    let np = shape.np;
    let mut i = 0;
    while i < np {
        let key = src.key();
        s.push_principal_entry(
            key,
            Principal {
                account_id: src.acct(),
                role: role(src),
                active_from: src.u64(),
                pending: src.u32(),
            },
        );
        i += 1;
    }
    let nr = shape.nr;
    let nl = shape.nl;
    let mut i = 0;
    while i < nr {
        let approval = if src.bool() {
            Some(Approval {
                approval_index: src.u64(),
                approver_account_id: src.acct(),
                approver_key: src.key(),
                approved_at: time(src),
            })
        } else {
            None
        };
        s.push_request_raw(ActionRequest {
            id: if raw { src.u64() } else { i as u64 },
            agent_account_id: src.acct(),
            agent_key: src.key(),
            action: stored_action(src, raw),
            requested_at: time(src),
            approval,
        });
        i += 1;
    }
    let mut j = 0;
    while j < nl {
        s.push_log_raw(src.u64());
        j += 1;
    }
    s
}

/// A ghost history for `s`, to be filtered by `assume(gh(s, h))`.
///
/// `GH` determines every recorded caller, action, time, account, role and
/// log position from `s` itself, so those are copied rather than drawn; only
/// the registration ids and the clock are free.
pub fn ghost(src: &mut impl Src, s: &S) -> Ghost {
    let mut h = Ghost::init();
    h.now = time(src);
    h.next_reg = src.below(16);
    let mut k = 0;
    while k < h.reg.len() {
        h.reg[k] = if src.bool() {
            Some(src.below(16))
        } else {
            None
        };
        k += 1;
    }
    h.n = s.nr();
    let mut i = 0;
    while i < h.n {
        let r = &s.req(i);
        let reg = src.below(16);
        let act = act_code(&r.action);
        h.req[i] = Some(ReqRec {
            c: CallRec {
                pred: r.agent_account_id.0,
                sig: r.agent_account_id.0,
                key: r.agent_key.0,
            },
            act,
            t: r.requested_at,
            reg,
            acct: r.agent_account_id.0,
            role: Role::Agent,
        });
        h.appr[i] = r.approval.as_ref().map(|x| ApprRec {
            c: CallRec {
                pred: x.approver_account_id.0,
                sig: x.approver_account_id.0,
                key: x.approver_key.0,
            },
            act,
            t: x.approved_at,
            acct: x.approver_account_id.0,
            role: Role::Approver,
            agent_reg: Some(reg),
            log_len: x.approval_index,
        });
        i += 1;
    }
    h
}

/// The caller account of an owner-only operation.
pub fn admin(src: &mut impl Src) -> Acct {
    if src.hint(80) {
        OWNER
    } else {
        src.acct()
    }
}

/// A runtime caller. Plain mode leans toward direct calls with a key the
/// signer actually holds, so authentication passes often enough.
pub fn caller(src: &mut impl Src, s: &S) -> C {
    let signer = src.acct();
    let predecessor = if src.hint(90) {
        signer.clone()
    } else {
        src.acct()
    };
    let mut signer_key = src.key();
    if src.hint(75) {
        for (k, p) in s.principals().iter() {
            if p.account_id == signer && src.hint(70) {
                signer_key = k.clone();
            }
        }
    }
    Caller {
        predecessor,
        signer,
        signer_key,
    }
}

/// An operation time. Plain mode keeps time non-decreasing from `h.now`;
/// symbolic mode draws it freely and the harness assumes ASM-TIME.
pub fn op_time(src: &mut impl Src, h: &Ghost) -> BlockTime {
    if src.hint(100) {
        BlockTime {
            height: h.now.height + src.below(3) as u64,
            timestamp_ns: h.now.timestamp_ns + src.below(3) as u64,
        }
    } else {
        time(src)
    }
}

pub fn op_add(src: &mut impl Src, s: &S) -> Op {
    let caller = admin(src);
    // Plain mode: sometimes re-register a revoked agent key to the account
    // it used before, the TR-3 revival attempt.
    if src.hint(30) {
        for r in s.requests().iter() {
            let free = s.principals().iter().all(|(k, _)| *k != r.agent_key);
            if free && src.hint(60) {
                return Op::Add {
                    caller,
                    key: r.agent_key.clone(),
                    acct: r.agent_account_id.clone(),
                    role: Role::Agent,
                };
            }
        }
    }
    Op::Add {
        caller,
        key: src.key(),
        acct: src.acct(),
        role: role(src),
    }
}

pub fn op_revoke(src: &mut impl Src, s: &S) -> Op {
    let caller = admin(src);
    let mut key = src.key();
    if src.hint(70) {
        for (k, _) in s.principals().iter() {
            if src.hint(50) {
                key = k.clone();
            }
        }
    }
    Op::Revoke { caller, key }
}

pub fn op_req(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    Op::Req {
        c: caller(src, s),
        action: op_action(src),
        t: op_time(src, h),
    }
}

pub fn op_appr(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    let c = caller(src, s);
    let id = if src.hint(90) {
        src.below(s.nr() as u8 + 1) as u64
    } else {
        src.u64()
    };
    let action = if id < s.nr() as u64 && src.hint(85) {
        s.req(id as usize).action.clone()
    } else {
        op_action(src)
    };
    Op::Appr {
        c,
        id,
        action,
        t: op_time(src, h),
    }
}

/// Any of the four operations.
pub fn op(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    match src.below(4) {
        0 => op_add(src, s),
        1 => op_revoke(src, s),
        2 => op_req(src, s, h),
        _ => op_appr(src, s, h),
    }
}

/// Plain mode: a reachable state and its ghost history, by a random walk
/// from `Init`. Keeps `#P, #R ≤ 3` like the symbolic bounds.
#[cfg(not(kani))]
pub fn random_walk(src: &mut impl Src, steps: usize) -> (S, Ghost) {
    let mut s: S = ArrStore::new(OWNER);
    let mut h = Ghost::init();
    for _ in 0..steps {
        let o = op(src, &s, &h);
        let mut next = s.clone();
        let out = apply(&mut next, &o);
        if next.np() > MAX_P as usize || next.nr() > MAX_R as usize {
            continue;
        }
        h = ghost_step(&h, &snap(&s), &o, &out);
        s = next;
    }
    (s, h)
}
