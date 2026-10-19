//! Step properties (strategy.md §5.3): what one operation may change, at
//! every store size. `hist(s, op, exec(s, op))` holds from every `full_inv`
//! state; HIST-7 holds from any state at all.

use crate::*;
use vstd::prelude::*;

verus! {

/// Request content: everything but the decision fields.
pub open spec fn same_content<A, K>(r: ActionRequest<A, K>, r2: ActionRequest<A, K>) -> bool {
    &&& r2.id == r.id
    &&& r2.agent_account_id == r.agent_account_id
    &&& r2.agent_key == r.agent_key
    &&& r2.agent_registration_id == r.agent_registration_id
    &&& r2.action == r.action
    &&& r2.requested_at == r.requested_at
}

/// A registration entry changed at most in its pending count.
pub open spec fn same_reg<A>(p: Principal<A>, p2: Principal<A>) -> bool {
    &&& p2.account_id == p.account_id
    &&& p2.role == p.role
    &&& p2.registration_id == p.registration_id
    &&& p2.active_from == p.active_from
}

/// What survives any number of steps (the transitive part of `hist`).
pub open spec fn grows<A, K>(s: AbsStore<A, K>, s2: AbsStore<A, K>) -> bool {
    // HIST-1
    &&& s.requests.len() <= s2.requests.len()
    &&& forall|i: int| 0 <= i < s.requests.len() ==> same_content(s.requests[i], #[trigger] s2.requests[i])
    // HIST-2
    &&& forall|i: int| 0 <= i < s.requests.len() && (#[trigger] s.requests[i]).approval is Some
        ==> s2.requests[i].approval == s.requests[i].approval
    &&& forall|i: int| 0 <= i < s.requests.len() && (#[trigger] s.requests[i]).rejection is Some
        ==> s2.requests[i].rejection == s.requests[i].rejection
    // HIST-3
    &&& s.log.len() <= s2.log.len()
    &&& forall|j: int| 0 <= j < s.log.len() ==> #[trigger] s2.log[j] == s.log[j]
    // HIST-6 (owner), HIST-10 (G grows, revocations never change)
    &&& s2.owner == s.owner
    &&& s.reg_count <= s2.reg_count
    &&& forall|g: RegistrationId| #[trigger] s.revocations.dom().contains(g)
        ==> s2.revocations.dom().contains(g) && s2.revocations[g] == s.revocations[g]
}

pub proof fn lemma_grows_refl<A, K>(s: AbsStore<A, K>)
    ensures
        grows(s, s),
{
}

pub proof fn lemma_grows_trans<A, K>(s1: AbsStore<A, K>, s2: AbsStore<A, K>, s3: AbsStore<A, K>)
    requires
        grows(s1, s2),
        grows(s2, s3),
    ensures
        grows(s1, s3),
{
    assert forall|i: int| 0 <= i < s1.requests.len() implies same_content(s1.requests[i], #[trigger] s3.requests[i]) by {
        assert(same_content(s1.requests[i], s2.requests[i]));
        assert(same_content(s2.requests[i], s3.requests[i]));
    }
    assert forall|i: int| 0 <= i < s1.requests.len() && (#[trigger] s1.requests[i]).approval is Some
        implies s3.requests[i].approval == s1.requests[i].approval by {
        assert(s2.requests[i].approval == s1.requests[i].approval);
    }
    assert forall|i: int| 0 <= i < s1.requests.len() && (#[trigger] s1.requests[i]).rejection is Some
        implies s3.requests[i].rejection == s1.requests[i].rejection by {
        assert(s2.requests[i].rejection == s1.requests[i].rejection);
    }
    assert forall|j: int| 0 <= j < s1.log.len() implies #[trigger] s3.log[j] == s1.log[j] by {
        assert(s2.log[j] == s1.log[j]);
    }
}

pub open spec fn op_is_request<A, K>(op: Op<A, K>) -> bool {
    op is Request
}

pub open spec fn op_is_approve<A, K>(op: Op<A, K>) -> bool {
    op is Approve
}

/// The step properties of one operation.
pub open spec fn hist<A, K>(s: AbsStore<A, K>, op: Op<A, K>, s2: AbsStore<A, K>) -> bool {
    let ok = ok(s, op);
    // PROP: HIST-1 HIST-2 HIST-3
    &&& grows(s, s2)
    // PROP: HIST-4
    &&& s2.requests.len() == s.requests.len() + if ok && op is Request { 1int } else { 0int }
    &&& s2.log.len() == s.log.len() + if ok && op is Approve { 1int } else { 0int }
    // PROP: HIST-5
    &&& forall|id: RequestId| (#[trigger] approval_spec(s, id)) is Some ==> approval_spec(s2, id) == approval_spec(s, id)
    // PROP: HIST-6
    &&& !ok ==> s2 == s
    &&& match op {
        Op::Add { caller, .. } => ok ==> caller == s.owner,
        Op::Revoke { caller, .. } => ok ==> caller == s.owner,
        _ => {
            &&& s2.principals.dom() == s.principals.dom()
            &&& forall|k: K| #[trigger] s.principals.dom().contains(k) ==> same_reg(s.principals[k], s2.principals[k])
        },
    }
    // PROP: HIST-8 HIST-9
    &&& forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Void
        ==> status_spec(s2, s2.requests[i]) == RequestStatus::Void
    &&& forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Rejected
        ==> status_spec(s2, s2.requests[i]) == RequestStatus::Rejected
    // PROP: HIST-10
    &&& s2.reg_count == s.reg_count + if ok && op is Add { 1int } else { 0int }
    &&& match op {
        Op::Revoke { key, .. } => ok ==> {
            &&& !s.revocations.dom().contains(s.principals[key].registration_id)
            &&& s2.revocations.dom() == s.revocations.dom().insert(s.principals[key].registration_id)
        },
        _ => s2.revocations == s.revocations,
    }
}

/// Every operation from an invariant state satisfies the step properties.
pub proof fn lemma_hist<A, K>(s: AbsStore<A, K>, op: Op<A, K>)
    requires
        full_inv(s),
    ensures
        hist(s, op, exec(s, op)),
{
    let s2 = exec(s, op);
    if !ok(s, op) {
        return;
    }
    // Decided requests keep their decisions; the only request a step
    // rewrites is an undecided one.
    match op {
        Op::Add { caller, key, acct, role } => {
            assert forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Void
                implies status_spec(s2, s2.requests[i]) == RequestStatus::Void by {
                assert(s.requests[i].id == i);
            }
            assert forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Rejected
                implies status_spec(s2, s2.requests[i]) == RequestStatus::Rejected by {
            }
        },
        Op::Revoke { caller, key, now } => {
            assert(s.principals.dom().contains(key));
        },
        Op::Request { c, action, now } => {
            let n = s.requests.len();
            assert(s.principals.dom().contains(c.signer_key));
            assert(s2.principals.dom() =~= s.principals.dom());
            assert forall|i: int| 0 <= i < s.requests.len() implies same_content(s.requests[i], #[trigger] s2.requests[i]) by {
                assert(s2.requests[i] == s.requests.push(s2.requests[n as int])[i]);
            }
            assert(s2.requests =~= s.requests.push(s2.requests[n as int]));
            assert forall|id: RequestId| (#[trigger] approval_spec(s, id)) is Some implies approval_spec(s2, id) == approval_spec(s, id) by {
            }
            assert forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Void
                implies status_spec(s2, s2.requests[i]) == RequestStatus::Void by {
            }
        },
        Op::Approve { c, id, act, now } => {
            let r = s.requests[id as int];
            assert(s.principals.dom().contains(r.agent_key));
            assert(s2.principals.dom() =~= s.principals.dom());
            assert forall|x: RequestId| (#[trigger] approval_spec(s, x)) is Some implies approval_spec(s2, x) == approval_spec(s, x) by {
            }
            assert forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Void
                implies status_spec(s2, s2.requests[i]) == RequestStatus::Void by {
                assert(s.requests[i].id == i);
            }
        },
        Op::Reject { c, id, now } => {
            let r = s.requests[id as int];
            assert(s.principals.dom().contains(r.agent_key));
            assert(s2.principals.dom() =~= s.principals.dom());
            assert forall|x: RequestId| (#[trigger] approval_spec(s, x)) is Some implies approval_spec(s2, x) == approval_spec(s, x) by {
            }
            assert forall|i: int| 0 <= i < s.requests.len() && status_spec(s, #[trigger] s.requests[i]) == RequestStatus::Void
                implies status_spec(s2, s2.requests[i]) == RequestStatus::Void by {
                assert(s.requests[i].id == i);
            }
        },
    }
}

/// HIST-7: owner operations never change requests or the log, and reject
/// never changes the log, from any state (no invariant). PROP: HIST-7
pub proof fn lemma_hist7<A, K>(s: AbsStore<A, K>, op: Op<A, K>)
    ensures
        (op is Add || op is Revoke) ==> exec(s, op).requests == s.requests && exec(s, op).log == s.log,
        op is Reject ==> exec(s, op).log == s.log,
{
}

// ---------------------------------------------------------------------------
// Time (ASM-TIME: block times passed to successive calls never decrease)
// ---------------------------------------------------------------------------

/// Component-wise order on block times.
pub open spec fn tle(a: BlockTime, b: BlockTime) -> bool {
    a.height <= b.height && a.timestamp_ns <= b.timestamp_ns
}

/// The time an operation is called at; `Add` takes none, so it keeps `t`.
pub open spec fn op_now<A, K>(op: Op<A, K>, t: BlockTime) -> BlockTime {
    match op {
        Op::Add { .. } => t,
        Op::Revoke { now, .. } => now,
        Op::Request { now, .. } => now,
        Op::Approve { now, .. } => now,
        Op::Reject { now, .. } => now,
    }
}

/// Every time recorded in `s` is at most `t`.
pub open spec fn clock<A, K>(s: AbsStore<A, K>, t: BlockTime) -> bool {
    forall|i: int| 0 <= i < s.requests.len() ==> {
        let r = #[trigger] s.requests[i];
        &&& tle(r.requested_at, t)
        &&& (r.approval matches Some(x) ==> tle(x.approved_at, t))
        &&& (r.rejection matches Some(y) ==> tle(y.rejected_at, t))
    }
}

/// INV-10: decisions are no earlier than their request. PROP: INV-10
pub open spec fn inv10<A, K>(s: AbsStore<A, K>) -> bool {
    forall|i: int| 0 <= i < s.requests.len() ==> {
        let r = #[trigger] s.requests[i];
        &&& (r.approval matches Some(x) ==> tle(r.requested_at, x.approved_at))
        &&& (r.rejection matches Some(y) ==> tle(r.requested_at, y.rejected_at))
    }
}

pub open spec fn approved_at<A, K>(s: AbsStore<A, K>, j: int) -> BlockTime {
    s.requests[s.log[j] as int].approval->Some_0.approved_at
}

/// TR-4: approval times are non-decreasing along the log. PROP: TR-4
pub open spec fn tr4<A, K>(s: AbsStore<A, K>) -> bool {
    forall|j1: int, j2: int| 0 <= j1 <= j2 < s.log.len() ==> tle(#[trigger] approved_at(s, j1), #[trigger] approved_at(s, j2))
}

pub open spec fn timed<A, K>(s: AbsStore<A, K>, t: BlockTime) -> bool {
    clock(s, t) && inv10(s) && tr4(s)
}

pub proof fn lemma_timed<A, K>(s: AbsStore<A, K>, op: Op<A, K>, t: BlockTime)
    requires
        full_inv(s),
        timed(s, t),
        tle(t, op_now(op, t)),
    ensures
        timed(exec(s, op), op_now(op, t)),
{
    let s2 = exec(s, op);
    let t2 = op_now(op, t);
    if !ok(s, op) {
        assert(clock(s2, t2)) by {
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& tle(r.requested_at, t2)
                &&& (r.approval matches Some(x) ==> tle(x.approved_at, t2))
                &&& (r.rejection matches Some(y) ==> tle(y.rejected_at, t2))
            } by {
                assert(s.requests[i] == s2.requests[i]);
            }
        }
        return;
    }
    match op {
        Op::Add { .. } => {
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < s2.log.len() implies tle(#[trigger] approved_at(s2, j1), #[trigger] approved_at(s2, j2)) by {
                assert(tle(approved_at(s, j1), approved_at(s, j2)));
            }
        },
        Op::Revoke { .. } => {
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& tle(r.requested_at, t2)
                &&& (r.approval matches Some(x) ==> tle(x.approved_at, t2))
                &&& (r.rejection matches Some(y) ==> tle(y.rejected_at, t2))
            } by {
                assert(s.requests[i] == s2.requests[i]);
            }
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < s2.log.len() implies tle(#[trigger] approved_at(s2, j1), #[trigger] approved_at(s2, j2)) by {
                assert(tle(approved_at(s, j1), approved_at(s, j2)));
            }
        },
        Op::Request { c, action, now } => {
            let n = s.requests.len();
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& tle(r.requested_at, t2)
                &&& (r.approval matches Some(x) ==> tle(x.approved_at, t2))
                &&& (r.rejection matches Some(y) ==> tle(y.rejected_at, t2))
            } by {
                if i < n {
                    assert(s.requests[i] == s2.requests[i]);
                }
            }
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& (r.approval matches Some(x) ==> tle(r.requested_at, x.approved_at))
                &&& (r.rejection matches Some(y) ==> tle(r.requested_at, y.rejected_at))
            } by {
                if i < n {
                    assert(s.requests[i] == s2.requests[i]);
                }
            }
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < s2.log.len() implies tle(#[trigger] approved_at(s2, j1), #[trigger] approved_at(s2, j2)) by {
                assert(inv_log(s, j1) && inv_log(s, j2));
                assert(tle(approved_at(s, j1), approved_at(s, j2)));
            }
        },
        Op::Approve { c, id, act, now } => {
            let n = s.log.len();
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& tle(r.requested_at, t2)
                &&& (r.approval matches Some(x) ==> tle(x.approved_at, t2))
                &&& (r.rejection matches Some(y) ==> tle(y.rejected_at, t2))
            } by {
                assert(clock(s, t) ==> tle(s.requests[i].requested_at, t));
            }
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& (r.approval matches Some(x) ==> tle(r.requested_at, x.approved_at))
                &&& (r.rejection matches Some(y) ==> tle(r.requested_at, y.rejected_at))
            } by {
                assert(clock(s, t) ==> tle(s.requests[i].requested_at, t));
                assert(s.requests[i].id == i);
            }
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < s2.log.len() implies tle(#[trigger] approved_at(s2, j1), #[trigger] approved_at(s2, j2)) by {
                if j1 < n {
                    assert(inv_log(s, j1));
                    assert(s.requests[id as int].approval is None);
                    assert(s.log[j1] != id);
                    let i1 = s.log[j1] as int;
                    assert(clock(s, t) ==> tle(s.requests[i1].approval->Some_0.approved_at, t));
                }
                if j2 < n {
                    assert(inv_log(s, j2));
                    assert(s.log[j2] != id);
                    assert(tle(approved_at(s, j1), approved_at(s, j2)));
                }
            }
        },
        Op::Reject { c, id, now } => {
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& tle(r.requested_at, t2)
                &&& (r.approval matches Some(x) ==> tle(x.approved_at, t2))
                &&& (r.rejection matches Some(y) ==> tle(y.rejected_at, t2))
            } by {
                assert(clock(s, t) ==> tle(s.requests[i].requested_at, t));
            }
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& (r.approval matches Some(x) ==> tle(r.requested_at, x.approved_at))
                &&& (r.rejection matches Some(y) ==> tle(r.requested_at, y.rejected_at))
            } by {
                assert(clock(s, t) ==> tle(s.requests[i].requested_at, t));
                assert(s.requests[i].id == i);
            }
            assert forall|j1: int, j2: int| 0 <= j1 <= j2 < s2.log.len() implies tle(#[trigger] approved_at(s2, j1), #[trigger] approved_at(s2, j2)) by {
                assert(inv_log(s, j1) && inv_log(s, j2));
                assert(s.log[j1] != id && s.log[j2] != id);
                assert(tle(approved_at(s, j1), approved_at(s, j2)));
            }
        },
    }
}

// ---------------------------------------------------------------------------
// TR-6: the agent storage potential, per key
// ---------------------------------------------------------------------------

/// Key `k`'s share of `Phi = sum over agent keys of (16 - pending)`.
pub open spec fn phi<A, K>(s: AbsStore<A, K>, k: K) -> int {
    if s.principals.dom().contains(k) && s.principals[k].role == Role::Agent {
        MAX_PENDING_PER_KEY - s.principals[k].pending
    } else {
        0
    }
}

/// TR-6, key by key (the sum over keys follows): every share is >= 0; a
/// successful request lowers the caller's share by 1 and no other; a
/// successful approval or rejection raises the request's agent key's share
/// by 1 and no other; Add gives the new key a full share (16 for an agent);
/// Revoke drops a share; failed calls change nothing. PROP: TR-6
pub proof fn lemma_tr6<A, K>(s: AbsStore<A, K>, op: Op<A, K>, k: K)
    requires
        full_inv(s),
    ensures
        phi(s, k) >= 0,
        ({
            let s2 = exec(s, op);
            match op {
                Op::Request { c, .. } => phi(s2, k) == phi(s, k) - if ok(s, op) && k == c.signer_key { 1int } else { 0int },
                Op::Approve { id, .. } => phi(s2, k) == phi(s, k)
                    + if ok(s, op) && k == s.requests[id as int].agent_key { 1int } else { 0int },
                Op::Reject { id, .. } => phi(s2, k) == phi(s, k)
                    + if ok(s, op) && k == s.requests[id as int].agent_key { 1int } else { 0int },
                Op::Add { key, role, .. } => phi(s2, k) == if ok(s, op) && k == key {
                    if role == Role::Agent { MAX_PENDING_PER_KEY as int } else { 0int }
                } else {
                    phi(s, k)
                },
                Op::Revoke { .. } => phi(s2, k) <= phi(s, k),
            }
        }),
{
    if s.principals.dom().contains(k) {
        assert(inv_key(s, k));
    }
    let s2 = exec(s, op);
    if ok(s, op) {
        match op {
            Op::Approve { c, id, act, now } => {
                let ak = s.requests[id as int].agent_key;
                assert(s.principals.dom().contains(ak) && inv_key(s, ak));
                lemma_count_update(s.requests, id as int, s2.requests[id as int], pend_f::<A, K>(ak, s.principals[ak].active_from));
                assert(s.requests[id as int].id == id);
            },
            Op::Reject { c, id, now } => {
                let ak = s.requests[id as int].agent_key;
                assert(s.principals.dom().contains(ak) && inv_key(s, ak));
                lemma_count_update(s.requests, id as int, s2.requests[id as int], pend_f::<A, K>(ak, s.principals[ak].active_from));
                assert(s.requests[id as int].id == id);
            },
            _ => {},
        }
    }
}

} // verus!
