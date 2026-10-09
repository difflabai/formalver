//! Harness bodies, generic over [`Src`] (strategy.md section 6.2).
//!
//! Each body is the proof under Kani (`proofs.rs`) and a random test in plain
//! mode (`plain.rs`). Property IDs are tagged `PROP:` where they are checked.

use crate::gen;
use crate::ids::{Key, NK, OWNER};
use crate::spec::*;
use crate::src::{assume, Src};
use approval_core::{approvals, request_status, ApprovalError as E, RequestStatus, Role};
use approval_core::{MAX_PAGE_SIZE, MAX_PENDING_PER_KEY};

// ---------------------------------------------------------------------------
// Shared checks
// ---------------------------------------------------------------------------

/// Every state invariant, asserted one by one so Kani reports each.
pub fn assert_inv(s: &S) {
    assert!(s.owner == OWNER, "TX-6 owner fixed"); // PROP: TX-6
    assert!(inv0(s), "INV-0"); // PROP: INV-0
    assert!(inv1(s), "INV-1"); // PROP: INV-1
    assert!(inv2(s), "INV-2"); // PROP: INV-2
    assert!(inv3(s), "INV-3"); // PROP: INV-3
    assert!(inv4(s), "INV-4"); // PROP: INV-4
    assert!(inv5(s), "INV-5"); // PROP: INV-5
    assert!(inv6(s), "INV-6"); // PROP: INV-6
    assert!(inv7(s), "INV-7"); // PROP: INV-7
    assert!(inv8(s), "INV-8"); // PROP: INV-8
    assert!(inv9(s), "INV-9"); // PROP: INV-9
    assert!(inv10(s), "INV-10"); // PROP: INV-10
    assert!(lem1(s), "LEM-1"); // PROP: LEM-1
    assert!(lem2(s), "LEM-2"); // PROP: LEM-2
    assert!(lem3(s), "LEM-3"); // PROP: LEM-3
    assert!(tr4(s), "TR-4"); // PROP: TR-4
}

/// An `Inv` state within the bounds, with its ghost history in plain mode.
///
/// Under Kani there is no ghost: assuming `GH` over an arbitrary state made
/// CBMC exhaust 15 GB even at one request. The step harnesses instead prove
/// the pieces TR-1 is assembled from (TX-4, TX-5, HIST-1, HIST-8, see
/// RESULTS.md), and `h_bmc_from_init` checks `GH` itself along every trace
/// from `Init`, where the ghost starts concrete and needs no assumption.
pub fn inv_state(src: &mut impl Src) -> Option<(S, Option<Ghost>)> {
    if let Some((s, h)) = src.reach() {
        return Some((s, Some(h)));
    }
    let s = gen::state(src, false);
    if !assume(inv(&s)) {
        return None;
    }
    Some((s, None))
}

/// The ghost for generating operations: the real one, or a clock at zero.
fn clock(h: &Option<Ghost>) -> Ghost {
    h.unwrap_or_else(Ghost::init)
}

/// ASM-TIME: a step's time is not before any time already recorded.
fn time_ok(s: &S, h: &Option<Ghost>, op: &Op) -> bool {
    let t = match op {
        Op::Req { t, .. } | Op::Appr { t, .. } => t,
        _ => return true,
    };
    if let Some(h) = h {
        if !time_le(&h.now, t) {
            return false;
        }
    }
    let mut i = 0;
    while i < s.nr() {
        let r = &s.req(i);
        if !time_le(&r.requested_at, t) {
            return false;
        }
        if let Some(x) = &r.approval {
            if !time_le(&x.approved_at, t) {
                return false;
            }
        }
        i += 1;
    }
    true
}

/// What the history checks need from the pre-state besides the snapshot.
pub struct PreViews {
    pub status: [St; CR],
    pub proof: [Option<Proof>; CR],
    pub phi: i64,
}

pub fn pre_views(s: &S) -> PreViews {
    let mut v = PreViews {
        status: [St::Void; CR],
        proof: [const { None }; CR],
        phi: phi(s),
    };
    let mut i = 0;
    while i < s.nr() {
        v.status[i] = status(s, &s.req(i));
        v.proof[i] = core_approval(s, i as u64);
        i += 1;
    }
    v
}

/// History properties of one step `pre → post` (section 5.3).
fn assert_hist(pre: &Snap, v: &PreViews, post: &S, op: &Op, out: &Out) {
    // PROP: HIST-1
    assert!(post.nr() >= pre.nr, "HIST-1 never removed");
    let mut i = 0;
    while i < pre.nr {
        let q = pre.req(i);
        let r2 = &post.req(i);
        assert!(q.same_content(r2), "HIST-1 content immutable");
        // PROP: HIST-2
        if q.ap.is_some() {
            assert!(r2.approval == q.ap, "HIST-2 approval immutable");
        }
        // PROP: HIST-5
        if v.proof[i].is_some() {
            assert!(
                core_approval(post, i as u64) == v.proof[i],
                "HIST-5 proof stable"
            );
        }
        // PROP: HIST-8
        if v.status[i] == St::Void {
            assert!(status(post, r2) == St::Void, "HIST-8 void terminal");
        }
        i += 1;
    }
    // PROP: HIST-3
    assert!(post.nl() >= pre.nl, "HIST-3 log never shrinks");
    let mut j = 0;
    while j < pre.nl {
        assert!(post.log(j) == pre.l[j], "HIST-3 log append-only");
        j += 1;
    }
    // PROP: HIST-4
    let req_ok = matches!(out, Out::Req(Ok(_)));
    let appr_ok = matches!(out, Out::Appr(Ok(_)));
    assert!(
        post.nr() == pre.nr + req_ok as usize,
        "HIST-4 request counter delta"
    );
    assert!(
        post.nl() == pre.nl + appr_ok as usize,
        "HIST-4 log counter delta"
    );
    // PROP: HIST-6 TX-6
    assert!(post.owner == pre.owner, "HIST-6 owner fixed");
    let mut k = 0;
    while k < NK {
        let key = Key(k);
        let (a, b) = (pre.p_get(&key), p_get(post, &key));
        if a != b {
            let allowed = match (op, out.is_ok()) {
                (
                    Op::Add {
                        caller, key: k2, ..
                    },
                    true,
                )
                | (Op::Revoke { caller, key: k2 }, true) => *caller == pre.owner && *k2 == key,
                (Op::Req { c, .. }, true) => c.signer_key == key && same_but_pending(&a, &b),
                (Op::Appr { id, .. }, true) => {
                    pre.req(*id as usize).ak == key && same_but_pending(&a, &b)
                }
                _ => false,
            };
            assert!(allowed, "HIST-6 registry discipline");
        }
        k += 1;
    }
}

fn same_but_pending(
    a: &Option<approval_core::Principal<crate::ids::Acct>>,
    b: &Option<approval_core::Principal<crate::ids::Acct>>,
) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => {
            a.account_id == b.account_id && a.role == b.role && a.active_from == b.active_from
        }
        _ => false,
    }
}

/// TR-6: the potential moves only as the catalogue allows.
// PROP: TR-6
fn assert_phi(p0: i64, post: &S, op: &Op, out: &Out) {
    let p1 = phi(post);
    assert!(p1 >= 0, "TR-6 potential non-negative");
    if matches!(out, Out::Req(Ok(_))) {
        assert!(p1 == p0 - 1, "TR-6 request costs exactly 1");
    }
    if p1 > p0 {
        let agent_add = matches!(
            op,
            Op::Add {
                role: Role::Agent,
                ..
            }
        ) && out.is_ok();
        let appr = matches!(out, Out::Appr(Ok(_)));
        assert!(
            (appr && p1 == p0 + 1) || (agent_add && p1 == p0 + MAX_PENDING_PER_KEY as i64),
            "TR-6 potential rises only on approve or agent add"
        );
    }
}

/// Step check groups. Each is a separate Kani harness (section 6.3 ladder,
/// step 1: split further); plain mode runs all three in one.
pub const PART_TX: u8 = 1;
pub const PART_HIST: u8 = 2;
pub const PART_INV: u8 = 4;
pub const PART_ALL: u8 = PART_TX | PART_HIST | PART_INV;
/// Refinement of the TLA+ spec (REF-1..4, `tla.rs`). Its own harnesses
/// (`h_ref_*`), so the existing step harnesses keep their cost.
pub const PART_REF: u8 = 8;

/// One inductive step from an `Inv` state `s`, in place. `PART_TX`: exact
/// result, exact post-state, atomic failure. `PART_HIST`: history and `Φ`.
/// `PART_INV`: every invariant afterwards, and `GH` when a ghost is given.
pub fn check_step(s: &mut S, h: &Option<Ghost>, op: &Op, part: u8) -> (Option<Ghost>, Out) {
    let exp = if part & PART_TX != 0 {
        Some(expected(s, op))
    } else {
        None
    };
    let pre = if part & PART_ALL != PART_INV || h.is_some() {
        Some(snap(s))
    } else {
        None
    };
    let v = if part & PART_HIST != 0 {
        Some(pre_views(s))
    } else {
        None
    };
    let out = apply(s, op);
    if let (Some(exp), Some(pre)) = (&exp, &pre) {
        assert!(out == *exp, "TX exact result"); // PROP: TX-1 TX-2 TX-3 TX-4 TX-5
        if !out.is_ok() {
            assert!(same_as(s, pre), "TX-0 atomic failure"); // PROP: TX-0
        }
        assert!(post_ok(pre, s, op, &out), "TX exact post-state"); // PROP: TX-1 TX-2 TX-4 TX-5
    }
    if let (true, Some(pre)) = (part & PART_REF != 0, &pre) {
        crate::tla::assert_refines(pre, s, op, out.err());
    }
    if let (Some(v), Some(pre)) = (&v, &pre) {
        assert_hist(pre, v, s, op, &out);
        assert_phi(v.phi, s, op, &out);
    }
    if part & PART_INV != 0 {
        assert_inv(s);
    }
    let h2 = match (h, &pre) {
        (Some(h), Some(pre)) => Some(ghost_step(h, pre, op, &out)),
        _ => None,
    };
    if let Some(h2) = &h2 {
        assert!(gh(s, h2), "TR-1 ghost history GH"); // PROP: TR-1
    }
    (h2, out)
}

// ---------------------------------------------------------------------------
// h_init
// ---------------------------------------------------------------------------

pub fn init(_src: &mut impl Src) {
    let s: S = crate::store::ArrStore::new(OWNER);
    assert_inv(&s);
    assert!(gh(&s, &Ghost::init()), "TR-1 GH at init");
}

// ---------------------------------------------------------------------------
// h_step_*
// ---------------------------------------------------------------------------

pub fn step_add(src: &mut impl Src) {
    let Some((mut s, h)) = inv_state(src) else {
        return;
    };
    let op = gen::op_add(src, &s);
    let (_, out) = check_step(&mut s, &h, &op, src.part());
    cover!(out.is_ok(), "add: Ok");
    cover!(out.err() == Some(E::NotOwner), "add: NotOwner");
    cover!(
        out.err() == Some(E::KeyAlreadyRegistered),
        "add: KeyAlreadyRegistered"
    );
}

pub fn step_revoke(src: &mut impl Src) {
    let Some((mut s, h)) = inv_state(src) else {
        return;
    };
    let op = gen::op_revoke(src, &s);
    let before = pre_views(&s);
    let (_, out) = check_step(&mut s, &h, &op, src.part());
    cover!(out.is_ok(), "revoke: Ok");
    cover!(out.err() == Some(E::NotOwner), "revoke: NotOwner");
    cover!(
        out.err() == Some(E::KeyNotRegistered),
        "revoke: KeyNotRegistered"
    );
    let mut voided = false;
    let mut i = 0;
    while i < s.nr() {
        voided |= before.status[i] == St::Pending && status(&s, &s.req(i)) == St::Void;
        i += 1;
    }
    cover!(voided, "revoke: a pending request becomes void");
}

pub fn step_request(src: &mut impl Src) {
    let Some((mut s, h)) = inv_state(src) else {
        return;
    };
    let op = gen::op_req(src, &s, &clock(&h));
    assume!(time_ok(&s, &h, &op));
    let (_, out) = check_step(&mut s, &h, &op, src.part());
    cover!(out.is_ok(), "request: Ok");
    cover!(out.err() == Some(E::IndirectCall), "request: IndirectCall");
    cover!(out.err() == Some(E::UnknownKey), "request: UnknownKey");
    cover!(out.err() == Some(E::WrongRole), "request: WrongRole");
    cover!(
        out.err() == Some(E::KeyAccountMismatch),
        "request: KeyAccountMismatch"
    );
    cover!(out.err() == Some(E::EmptyAction), "request: EmptyAction");
}

pub fn step_approve(src: &mut impl Src) {
    let Some((mut s, h)) = inv_state(src) else {
        return;
    };
    let op = gen::op_appr(src, &s, &clock(&h));
    assume!(time_ok(&s, &h, &op));
    let (_, out) = check_step(&mut s, &h, &op, src.part());
    cover!(out.is_ok(), "approve: Ok");
    cover!(out.err() == Some(E::IndirectCall), "approve: IndirectCall");
    cover!(out.err() == Some(E::UnknownKey), "approve: UnknownKey");
    cover!(out.err() == Some(E::WrongRole), "approve: WrongRole");
    cover!(
        out.err() == Some(E::KeyAccountMismatch),
        "approve: KeyAccountMismatch"
    );
    cover!(
        out.err() == Some(E::RequestNotFound),
        "approve: RequestNotFound"
    );
    cover!(
        out.err() == Some(E::AlreadyApproved),
        "approve: AlreadyApproved"
    );
    cover!(out.err() == Some(E::AgentRevoked), "approve: AgentRevoked");
    cover!(
        out.err() == Some(E::ActionMismatch),
        "approve: ActionMismatch"
    );
    cover!(out.err() == Some(E::SelfApproval), "approve: SelfApproval");
}

// ---------------------------------------------------------------------------
// h_raw_*: arbitrary store state, no assume(inv)
// ---------------------------------------------------------------------------

/// Exact result and atomic failure from any state; the core must not panic
/// on the way (ROB-1).
fn check_raw(s: &mut S, op: &Op) -> (Snap, Out) {
    let exp = expected(s, op);
    let pre = snap(s);
    let out = apply(s, op); // PROP: ROB-1
    assert!(out == exp, "TX exact result (raw)"); // PROP: TX-1 TX-2 TX-3 TX-4 TX-5
    if !out.is_ok() {
        assert!(same_as(s, &pre), "TX-0 atomic failure (raw)"); // PROP: TX-0
    }
    (pre, out)
}

/// HIST-7: `R` and `L` equal the snapshot's.
fn same_r_l(s: &S, pre: &Snap) -> bool {
    if s.nr() != pre.nr || s.nl() != pre.nl {
        return false;
    }
    let mut i = 0;
    while i < pre.nr {
        if !pre.req(i).same(&s.req(i)) {
            return false;
        }
        i += 1;
    }
    let mut j = 0;
    while j < pre.nl {
        if s.log(j) != pre.l[j] {
            return false;
        }
        j += 1;
    }
    true
}

pub fn raw_add(src: &mut impl Src) {
    let mut s = gen::state(src, true);
    let op = gen::op_add(src, &s);
    let (pre, out) = check_raw(&mut s, &op);
    // PROP: HIST-7
    assert!(same_r_l(&s, &pre), "HIST-7 add leaves R, L unchanged");
    cover!(out.is_ok(), "raw add: Ok");
}

pub fn raw_revoke(src: &mut impl Src) {
    let mut s = gen::state(src, true);
    let op = gen::op_revoke(src, &s);
    let (pre, out) = check_raw(&mut s, &op);
    // PROP: HIST-7
    assert!(same_r_l(&s, &pre), "HIST-7 revoke leaves R, L unchanged");
    cover!(out.is_ok(), "raw revoke: Ok");
}

pub fn raw_request(src: &mut impl Src) {
    let mut s = gen::state(src, true);
    let h = Ghost::init();
    let op = gen::op_req(src, &s, &h);
    let Op::Req { c, .. } = &op else {
        unreachable!()
    };
    let before = p_get(&s, &c.signer_key).map(|p| p.pending);
    let (_, out) = check_raw(&mut s, &op);
    let post = &s;
    // PROP: INV-9 TX-4 TR-6
    if out.is_ok() {
        let b = before.unwrap();
        assert!(
            b < MAX_PENDING_PER_KEY,
            "INV-9 bound step: Ok => pend < MAXP"
        );
        assert!(
            p_get(post, &c.signer_key).unwrap().pending == b + 1,
            "INV-9 bound step: pend' = pend + 1"
        );
    }
    cover!(out.is_ok(), "raw request: Ok");
    cover!(
        out.is_ok() && before == Some(MAX_PENDING_PER_KEY - 1),
        "raw request: Ok at pend = MAXP - 1"
    );
    cover!(
        out.err() == Some(E::TooManyPending) && before == Some(MAX_PENDING_PER_KEY),
        "raw request: TooManyPending at pend = MAXP"
    );
}

pub fn raw_approve(src: &mut impl Src) {
    let mut s = gen::state(src, true);
    let h = Ghost::init();
    let op = gen::op_appr(src, &s, &h);
    let (_, out) = check_raw(&mut s, &op);
    cover!(out.is_ok(), "raw approve: Ok");
}

// ---------------------------------------------------------------------------
// h_read
// ---------------------------------------------------------------------------

/// `h_read` checks the point queries, `h_read_page` the page contents and
/// `h_read_find` that paged proofs are findable (cost fallback 1: split
/// further). Plain mode runs all three.
pub const READ_POINT: u8 = 1;
pub const READ_PAGE: u8 = 2;
pub const READ_FIND: u8 = 4;

pub fn read(src: &mut impl Src) {
    let Some((s, _)) = inv_state(src) else { return };
    let part = src.part();
    if part & READ_POINT != 0 {
        read_point(src, &s);
    }
    if part & (READ_PAGE | READ_FIND) != 0 {
        read_page(src, &s, part);
    }
}

fn read_point(src: &mut impl Src, s: &S) {
    let id = if src.hint(80) {
        src.below(5) as u64
    } else {
        src.u64()
    };

    // PROP: RD-1
    let got = core_approval(s, id);
    let want = r_get(s, id).and_then(spec_proof);
    assert!(got == want, "RD-1 approval = proof(R[i]) iff approved");
    if let Some(p) = &got {
        assert!(
            s.log(p.approval_index as usize) == id,
            "RD-1 L[approval_index] = i"
        );
    }

    // PROP: RD-7
    let st = request_status(s, id);
    let want_st = r_get(s, id).map(|r| match status(s, r) {
        St::Pending => RequestStatus::Pending,
        St::Approved => RequestStatus::Approved,
        St::Void => RequestStatus::Void,
    });
    assert!(st == want_st, "RD-7 request_status");

    // PROP: RD-5
    if let Some(p) = got {
        let one = approvals(s, p.approval_index, 1);
        assert!(
            one.len() == 1 && one[0] == p,
            "RD-5 proof findable by approval_index"
        );
    }

    // PROP: LEM-4
    let mut i = 0;
    while i < s.nr() {
        let r = &s.req(i);
        let reduced = match p_get(s, &r.agent_key) {
            Some(p) => p.active_from <= i as u64,
            None => false,
        };
        assert!(live(s, r) == reduced, "LEM-4 liveness is active_from <= i");
        i += 1;
    }

    cover!(st == Some(RequestStatus::Void), "read: void status");
}

fn read_page(src: &mut impl Src, s: &S, part: u8) {
    let from = if src.hint(80) {
        src.below(5) as u64
    } else {
        src.u64()
    };
    let limit = if src.hint(80) {
        src.below(5) as u64
    } else {
        src.u64()
    };

    let page = approvals(s, from, limit);
    if part & READ_PAGE != 0 {
        page_exact(s, from, limit, &page);
    }
    if part & READ_FIND != 0 {
        page_findable(s, &page);
    }
    cover!(!page.is_empty(), "read: non-empty page");
}

fn page_exact(s: &S, from: u64, limit: u64, page: &[Proof]) {
    // PROP: RD-2
    let end = from.saturating_add(limit.min(MAX_PAGE_SIZE)).min(n_l(s));
    assert!(
        page.len() as u64 == end.saturating_sub(from),
        "RD-2 page length e - f"
    );
    let mut j = from;
    let mut n = 0;
    while j < end {
        let i = s.log(j as usize);
        assert!(
            proof_of(&page[n], s, i),
            "RD-2 page entry = proof(R[L[j]])"
        );
        j += 1;
        n += 1;
    }

}

fn page_findable(s: &S, page: &[Proof]) {
    // PROP: RD-5
    let mut n = 0;
    while n < page.len() {
        let p = &page[n];
        assert!(
            core_approval(s, p.request_id).as_ref() == Some(p),
            "RD-5 paged proof findable by request_id"
        );
        n += 1;
    }
}

/// `p == proof(R[i])`, field by field over concrete slots: no clone, and no
/// `String` read through a symbolic index.
fn proof_of(p: &Proof, s: &S, i: u64) -> bool {
    let mut k = 0;
    while k < crate::store::CAP_R {
        if k < s.nr() && i == k as u64 {
            let r = s.req(k);
            return match &r.approval {
                Some(x) => {
                    p.approval_index == x.approval_index
                        && p.request_id == r.id
                        && p.action == r.action
                        && p.agent_account_id == r.agent_account_id
                        && p.agent_key == r.agent_key
                        && p.requested_at == r.requested_at
                        && p.approver_account_id == x.approver_account_id
                        && p.approver_key == x.approver_key
                        && p.approved_at == x.approved_at
                }
                None => false,
            };
        }
        k += 1;
    }
    false
}

// ---------------------------------------------------------------------------
// h_bmc_from_init
// ---------------------------------------------------------------------------

pub const BMC_DEPTH: usize = 6;
/// Requests along a BMC trace (section 6.3 fallback 3: requests and log
/// bounded at 2). One request suffices for every TR witness; the second
/// keeps two ids in play for TR-2.
pub const BMC_MAX_R: usize = 2;

pub fn bmc_from_init(src: &mut impl Src) {
    let mut s: S = crate::store::ArrStore::new(OWNER);
    let mut h = Some(Ghost::init());
    let mut approved_once = [0u8; BMC_DEPTH];
    let mut revoked_then_readded = false;
    let mut d = 0;
    while d < BMC_DEPTH {
        // Plain mode sometimes follows the TR-3 witness shape; under Kani
        // every step is any operation.
        const SCRIPT: [u8; BMC_DEPTH] = [0, 0, 2, 1, 0, 3];
        let op = if src.hint(50) {
            match SCRIPT[d] {
                0 => gen::op_add(src, &s),
                1 => gen::op_revoke(src, &s),
                2 => gen::op_req(src, &s, &clock(&h)),
                _ => gen::op_appr(src, &s, &clock(&h)),
            }
        } else {
            gen::op(src, &s, &clock(&h))
        };
        assume!(time_ok(&s, &h, &op));
        // Harness bound: at most BMC_MAX_R requests along a trace.
        assume!(!matches!(op, Op::Req { .. }) || s.nr() < BMC_MAX_R);
        let ak = match &op {
            Op::Appr { id, .. } if *id < s.nr() as u64 => {
                Some(s.req(*id as usize).agent_key.clone())
            }
            _ => None,
        };
        let (h2, out) = check_step(&mut s, &h, &op, src.part());
        // PROP: TR-2
        if let (Op::Appr { id, .. }, true) = (&op, out.is_ok()) {
            approved_once[*id as usize] += 1;
            assert!(
                approved_once[*id as usize] == 1,
                "TR-2 approved at most once"
            );
        }
        // PROP: TR-3
        if let (Op::Appr { id, .. }, Some(E::AgentRevoked)) = (&op, out.err()) {
            let _ = id;
            revoked_then_readded |= p_get(&s, ak.as_ref().unwrap()).is_some();
        }
        h = h2;
        d += 1;
    }
    // PROP: TR-5
    cover!(n_l(&s) > 0, "bmc: approved");
    cover!(
        revoked_then_readded,
        "bmc: revoke, re-add, approve old id fails with AgentRevoked"
    );
}

// ---------------------------------------------------------------------------
// h_canary
// ---------------------------------------------------------------------------

/// Asserts something false about reachable states. Must FAIL under Kani; if
/// it passes, the harness setup is vacuous.
pub fn canary(src: &mut impl Src) {
    let Some((s, _)) = inv_state(src) else { return };
    assert!(n_l(&s) == 0, "canary: no approval is ever recorded");
}

// ---------------------------------------------------------------------------
// h_ref_toolong: the TooLong payload class (A5, REF-1..3)
// ---------------------------------------------------------------------------

/// An action one byte over `MAX_ACTION_LEN`, built at compile time so its
/// length stays concrete under Kani.
pub const LONG: &str = match core::str::from_utf8(&[b'x'; approval_core::MAX_ACTION_LEN + 1]) {
    Ok(s) => s,
    Err(_) => panic!(),
};

/// The step harnesses draw actions from the 2-byte alphabet and `""`; this
/// covers the third class the TLA+ spec has, `TooLong`, for both entry
/// points that take an action.
pub fn ref_toolong(src: &mut impl Src) {
    let Some((mut s, h)) = inv_state(src) else {
        return;
    };
    let c = gen::caller(src, &s);
    let t = gen::op_time(src, &clock(&h));
    let op = if src.bool() {
        Op::Req {
            c,
            action: LONG.to_string(),
            t,
        }
    } else {
        let id = src.below(s.nr() as u8 + 1) as u64;
        Op::Appr {
            c,
            id,
            action: LONG.to_string(),
            t,
        }
    };
    assume!(time_ok(&s, &h, &op));
    let (_, out) = check_step(&mut s, &h, &op, PART_TX | PART_REF);
    assert!(!out.is_ok(), "REF TooLong is never accepted");
    cover!(out.err() == Some(E::ActionTooLong), "toolong: ActionTooLong");
    cover!(out.err() == Some(E::ActionMismatch), "toolong: ActionMismatch");
}
