//! Bounded state and operation builders (strategy.md sections 6.1 and 6.3).
//!
//! Bounds: `#P, #R, #L, #V ≤ 3`; accounts and keys from 4 values each;
//! actions from [`ACTIONS`] (plus `""` in operations); ids, counters,
//! `active_from`, `pending` and times free. Registration ids are free in raw
//! states and drawn from `0..8` in `Inv` states, where INV-15 forces
//! `G = #P + #V ≤ 6` and INV-11/12/14 put every id below `G`.

use crate::ids::{Acct, ACTION_BYTES, OWNER};
#[cfg(not(kani))]
use crate::spec::{apply, ghost_step, GPre};
use crate::spec::{Ghost, Op, C, S};
use crate::src::Src;
use crate::store::ArrStore;
use approval_core::{ActionRequest, Approval, BlockTime, Caller, Principal, Rejection, Role};

pub const MAX_P: u8 = 3;
pub const MAX_R: u8 = 3;
pub const MAX_V: u8 = 3;

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

/// A time stored in a generated state: free in raw states; in `Inv`
/// states each component is drawn from `0..16`. Times are only copied and
/// compared (`==`, component-wise `≤`), and a state plus one step holds at
/// most 10 of them, so any assignment is order-isomorphic to one in range.
pub fn state_time(src: &mut impl Src, raw: bool) -> BlockTime {
    if raw {
        time(src)
    } else {
        BlockTime {
            height: src.below(16) as u64,
            timestamp_ns: src.below(16) as u64,
        }
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

/// A registration id: free in raw states, `0..8` in `Inv` states.
pub fn reg_id(src: &mut impl Src, raw: bool) -> u64 {
    if raw {
        src.u64()
    } else {
        src.below(8) as u64
    }
}

/// An arbitrary store within the bounds.
///
/// With `raw = false` the result is meant to be filtered by `assume(inv)`,
/// so values that INV-1/INV-3/INV-4/INV-13/INV-15 pin down (request ids,
/// at most one decision per request, `G`) are fixed instead of drawn (no
/// loss of generality under the assumption). With `raw = true` every field
/// is free and duplicate keys are possible.
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
                registration_id: reg_id(src, raw),
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
        // Raw: approval and rejection independently; Inv: at most one.
        let (ap, rj) = if raw {
            (src.bool(), src.bool())
        } else {
            match src.below(3) {
                0 => (false, false),
                1 => (true, false),
                _ => (false, true),
            }
        };
        let approval = if ap {
            Some(Approval {
                approval_index: src.u64(),
                approver_account_id: src.acct(),
                approver_key: src.key(),
                approver_registration_id: reg_id(src, raw),
                approved_at: state_time(src, raw),
            })
        } else {
            None
        };
        let rejection = if rj {
            Some(Rejection {
                approver_account_id: src.acct(),
                approver_key: src.key(),
                approver_registration_id: reg_id(src, raw),
                rejected_at: state_time(src, raw),
            })
        } else {
            None
        };
        s.push_request_raw(ActionRequest {
            id: if raw { src.u64() } else { i as u64 },
            agent_account_id: src.acct(),
            agent_key: src.key(),
            agent_registration_id: reg_id(src, raw),
            action: stored_action(src, raw),
            requested_at: state_time(src, raw),
            approval,
            rejection,
        });
        i += 1;
    }
    let mut j = 0;
    while j < nl {
        s.push_log_raw(src.u64());
        j += 1;
    }
    let nv = shape.nv;
    let mut j = 0;
    while j < nv {
        let g = reg_id(src, raw);
        s.push_rev_raw(g, state_time(src, raw));
        j += 1;
    }
    s.set_g(if raw {
        src.u64()
    } else {
        np as u64 + nv as u64
    });
    s
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

pub fn op_revoke(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    let caller = admin(src);
    let mut key = src.key();
    if src.hint(70) {
        for (k, _) in s.principals().iter() {
            if src.hint(50) {
                key = k.clone();
            }
        }
    }
    Op::Revoke {
        caller,
        key,
        t: op_time(src, h),
    }
}

pub fn op_req(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    Op::Req {
        c: caller(src, s),
        action: op_action(src),
        t: op_time(src, h),
    }
}

/// A request id: mostly an existing one in plain mode, any `u64` under Kani.
fn req_id(src: &mut impl Src, s: &S) -> u64 {
    if src.hint(90) {
        src.below(s.nr() as u8 + 1) as u64
    } else {
        src.u64()
    }
}

pub fn op_appr(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    let c = caller(src, s);
    let id = req_id(src, s);
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

pub fn op_rej(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    Op::Rej {
        c: caller(src, s),
        id: req_id(src, s),
        t: op_time(src, h),
    }
}

/// Any of the five operations.
pub fn op(src: &mut impl Src, s: &S, h: &Ghost) -> Op {
    // Plain mode leans toward the request and decision operations, which
    // need several registry steps before they can succeed.
    let pick = if src.hint(40) {
        2 + src.below(3)
    } else {
        src.below(5)
    };
    match pick {
        0 => op_add(src, s),
        1 => op_revoke(src, s, h),
        2 => op_req(src, s, h),
        3 => op_appr(src, s, h),
        _ => op_rej(src, s, h),
    }
}

/// Plain mode: a reachable state and its ghost history, by a random walk
/// from `Init`. Keeps `#P, #R, #V ≤ 3` like the symbolic bounds.
#[cfg(not(kani))]
pub fn random_walk(src: &mut impl Src, steps: usize) -> (S, Ghost) {
    let mut s: S = ArrStore::new(OWNER);
    let mut h = Ghost::init();
    for _ in 0..steps {
        let o = op(src, &s, &h);
        let mut next = s.clone();
        let out = apply(&mut next, &o);
        if next.np() > MAX_P as usize || next.nr() > MAX_R as usize || next.nv() > MAX_V as usize {
            continue;
        }
        h = ghost_step(&h, &GPre::of_state(&s, &o), &o, &out);
        s = next;
    }
    (s, h)
}
