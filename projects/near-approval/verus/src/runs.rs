//! Trace properties (strategy.md §5.4) over runs of any length, at every
//! store size. A run is a sequence of operations and the states between
//! them; a failed operation leaves the state unchanged (TX-0).

use crate::*;
use vstd::prelude::*;

verus! {

pub open spec fn is_run<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>) -> bool {
    &&& sts.len() == ops.len() + 1
    &&& forall|k: int| 0 <= k < ops.len() ==> sts[k + 1] == exec(sts[k], #[trigger] ops[k])
}

/// A run from the freshly initialised contract.
pub open spec fn from_init<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>) -> bool {
    is_run(sts, ops) && sts[0] == init::<A, K>(sts[0].owner)
}

pub proof fn lemma_run_inv<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= k <= ops.len(),
    ensures
        full_inv(sts[k]),
    decreases k,
{
    if k > 0 {
        lemma_run_inv(sts, ops, k - 1);
        assert(sts[k] == exec(sts[k - 1], ops[k - 1]));
        lemma_full_inv(sts[k - 1], ops[k - 1]);
    }
}

pub proof fn lemma_init_run_inv<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int)
    requires
        from_init(sts, ops),
        0 <= k <= ops.len(),
    ensures
        full_inv(sts[k]),
{
    lemma_init_full::<A, K>(sts[0].owner);
    lemma_run_inv(sts, ops, k);
}

/// `grows` between any two states of a run (HIST-1/2/3/6/10 lifted to runs).
pub proof fn lemma_run_grows<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, a: int, b: int)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= a <= b <= ops.len(),
    ensures
        grows(sts[a], sts[b]),
    decreases b - a,
{
    if a < b {
        lemma_run_grows(sts, ops, a, b - 1);
        lemma_run_inv(sts, ops, b - 1);
        assert(sts[b] == exec(sts[b - 1], ops[b - 1]));
        lemma_hist(sts[b - 1], ops[b - 1]);
        lemma_grows_trans(sts[a], sts[b - 1], sts[b]);
    }
}

// ---------------------------------------------------------------------------
// TR-2: each request is decided at most once
// ---------------------------------------------------------------------------

pub open spec fn decides<A, K>(s: AbsStore<A, K>, op: Op<A, K>, i: int) -> bool {
    &&& ok(s, op)
    &&& match op {
        Op::Approve { id, .. } => id == i,
        Op::Reject { id, .. } => id == i,
        _ => false,
    }
}

/// PROP: TR-2
pub proof fn lemma_tr2<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, i: int, k1: int, k2: int)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= k1 < k2 < ops.len(),
        decides(sts[k1], ops[k1], i),
    ensures
        !decides(sts[k2], ops[k2], i),
{
    let s1 = sts[k1 + 1];
    assert(s1 == exec(sts[k1], ops[k1]));
    assert(0 <= i < s1.requests.len());
    assert(s1.requests[i].approval is Some || s1.requests[i].rejection is Some);
    lemma_run_grows(sts, ops, k1 + 1, k2);
    let s2 = sts[k2];
    assert(s2.requests[i].approval is Some || s2.requests[i].rejection is Some);
}

// ---------------------------------------------------------------------------
// TR-3: durable revocation
// ---------------------------------------------------------------------------

/// A pending request whose agent registration has been revoked is Void.
pub proof fn lemma_revoked_is_void<A, K>(s: AbsStore<A, K>, i: int)
    requires
        full_inv(s),
        0 <= i < s.requests.len(),
        undecided(s.requests[i]),
        s.revocations.dom().contains(s.requests[i].agent_registration_id),
    ensures
        status_spec(s, s.requests[i]) == RequestStatus::Void,
{
    let k = s.requests[i].agent_key;
    if s.principals.dom().contains(k) {
        assert(inv_kr(s, k, i));
        assert(s.requests[i].id == i);
    }
}

/// Void stays Void, over any run.
pub proof fn lemma_run_void<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, a: int, b: int, i: int)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= a <= b <= ops.len(),
        0 <= i < sts[a].requests.len(),
        status_spec(sts[a], sts[a].requests[i]) == RequestStatus::Void,
    ensures
        i < sts[b].requests.len(),
        status_spec(sts[b], sts[b].requests[i]) == RequestStatus::Void,
    decreases b - a,
{
    if a < b {
        lemma_run_void(sts, ops, a, b - 1, i);
        lemma_run_inv(sts, ops, b - 1);
        assert(sts[b] == exec(sts[b - 1], ops[b - 1]));
        lemma_hist(sts[b - 1], ops[b - 1]);
        assert(status_spec(sts[b - 1], sts[b - 1].requests[i]) == RequestStatus::Void);
    }
}

/// TR-3: a request whose agent registration is revoked while it is pending
/// is never approved afterwards, whatever happens later (re-registration of
/// the same key or account included). PROP: TR-3
pub proof fn lemma_tr3<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, a: int, b: int, i: int)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= a <= b <= ops.len(),
        0 <= i < sts[a].requests.len(),
        undecided(sts[a].requests[i]),
        sts[a].revocations.dom().contains(sts[a].requests[i].agent_registration_id),
    ensures
        sts[b].requests[i].approval is None,
{
    lemma_run_inv(sts, ops, a);
    lemma_revoked_is_void(sts[a], i);
    lemma_run_void(sts, ops, a, b, i);
}

// ---------------------------------------------------------------------------
// TR-1: provenance
// ---------------------------------------------------------------------------

/// Step `k1` is a successful request that created request `i` with `r`'s
/// content, by a key registered to the signing account as an Agent under
/// `r`'s registration id.
pub open spec fn request_made<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k1: int, i: int, r: ActionRequest<A, K>) -> bool {
    let s = sts[k1];
    &&& 0 <= k1 < ops.len()
    &&& ok(s, ops[k1])
    &&& ops[k1] matches Op::Request { c, action, now }
    &&& s.requests.len() == i
    &&& c.predecessor == c.signer
    &&& c.signer == r.agent_account_id
    &&& c.signer_key == r.agent_key
    &&& action == r.action
    &&& now == r.requested_at
    &&& s.principals.dom().contains(c.signer_key)
    &&& s.principals[c.signer_key].account_id == c.signer
    &&& s.principals[c.signer_key].role == Role::Agent
    &&& s.principals[c.signer_key].registration_id == r.agent_registration_id
}

/// Step `k2` is a successful approval of request `i` that recorded `a`,
/// restating `r`'s action, signed directly by a key registered to a
/// different account as an Approver under `a`'s registration id.
pub open spec fn approval_made<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k2: int, i: int, r: ActionRequest<A, K>, a: Approval<A, K>) -> bool {
    let s = sts[k2];
    &&& 0 <= k2 < ops.len()
    &&& ok(s, ops[k2])
    &&& ops[k2] matches Op::Approve { c, id, act, now }
    &&& id == i
    &&& act == r.action@
    &&& c.predecessor == c.signer
    &&& c.signer == a.approver_account_id
    &&& c.signer_key == a.approver_key
    &&& now == a.approved_at
    &&& c.signer != r.agent_account_id
    &&& s.principals.dom().contains(c.signer_key)
    &&& s.principals[c.signer_key].account_id == c.signer
    &&& s.principals[c.signer_key].role == Role::Approver
    &&& s.principals[c.signer_key].registration_id == a.approver_registration_id
}

/// Key `key` holds registration `g` at every state from `k1` to `k2`.
pub open spec fn continuous<A, K>(sts: Seq<AbsStore<A, K>>, k1: int, k2: int, key: K, g: RegistrationId) -> bool {
    forall|k: int| k1 <= k <= k2 ==> {
        &&& (#[trigger] sts[k]).principals.dom().contains(key)
        &&& sts[k].principals[key].registration_id == g
    }
}

pub open spec fn req_prov<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int, i: int) -> bool {
    exists|k1: int| k1 < k && #[trigger] request_made(sts, ops, k1, i, sts[k].requests[i])
}

pub open spec fn appr_prov<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int, i: int) -> bool {
    let r = sts[k].requests[i];
    r.approval matches Some(a) ==> exists|k1: int, k2: int|
        #![trigger request_made(sts, ops, k1, i, r), approval_made(sts, ops, k2, i, r, a)]
        k1 < k2 < k
        && request_made(sts, ops, k1, i, r)
        && approval_made(sts, ops, k2, i, r, a)
        && continuous(sts, k1, k2, r.agent_key, r.agent_registration_id)
}

/// A registration that a key holds at `a` and again at `b` was held at
/// every state in between: registration ids are never reissued, and losing
/// one revokes it for good.
pub proof fn lemma_reg_stays<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, a: int, b: int, key: K, g: RegistrationId)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= a <= b <= ops.len(),
        sts[a].principals.dom().contains(key) && sts[a].principals[key].registration_id == g,
        sts[b].principals.dom().contains(key) && sts[b].principals[key].registration_id == g,
    ensures
        continuous(sts, a, b, key, g),
{
    assert forall|k: int| a <= k <= b implies {
        &&& (#[trigger] sts[k]).principals.dom().contains(key)
        &&& sts[k].principals[key].registration_id == g
    } by {
        lemma_held_or_revoked(sts, ops, a, k, key, g);
        if sts[k].revocations.dom().contains(g) {
            lemma_run_grows(sts, ops, k, b);
            lemma_run_inv(sts, ops, b);
        }
    }
}

/// From `a` on, `key` keeps registration `g` until `g` is revoked.
proof fn lemma_held_or_revoked<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, a: int, k: int, key: K, g: RegistrationId)
    requires
        is_run(sts, ops),
        full_inv(sts[0]),
        0 <= a <= k <= ops.len(),
        sts[a].principals.dom().contains(key) && sts[a].principals[key].registration_id == g,
    ensures
        (sts[k].principals.dom().contains(key) && sts[k].principals[key].registration_id == g)
            || sts[k].revocations.dom().contains(g),
    decreases k - a,
{
    if a < k {
        lemma_held_or_revoked(sts, ops, a, k - 1, key, g);
        lemma_run_inv(sts, ops, k - 1);
        let s = sts[k - 1];
        let op = ops[k - 1];
        assert(sts[k] == exec(s, op));
        lemma_hist(s, op);
        if s.principals.dom().contains(key) && s.principals[key].registration_id == g && ok(s, op) {
            match op {
                Op::Revoke { caller, key: kk, now } => {
                    if kk == key {
                        assert(sts[k].revocations.dom().contains(g));
                    }
                },
                Op::Add { .. } => {},
                _ => {
                    assert(same_reg(s.principals[key], sts[k].principals[key]));
                },
            }
        }
    }
}

/// TR-1 for every request present at state `k` of a run from init: it was
/// created by an earlier successful request, and if it is approved, by an
/// earlier successful approval after that, with the agent's registration
/// held throughout. PROP: TR-1
pub proof fn lemma_tr1<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int)
    requires
        from_init(sts, ops),
        0 <= k <= ops.len(),
    ensures
        forall|i: int| 0 <= i < sts[k].requests.len() ==> #[trigger] req_prov(sts, ops, k, i) && appr_prov(sts, ops, k, i),
    decreases k,
{
    if k == 0 {
        return;
    }
    lemma_tr1(sts, ops, k - 1);
    lemma_init_run_inv(sts, ops, k - 1);
    lemma_init_run_inv(sts, ops, k);
    let s = sts[k - 1];
    let op = ops[k - 1];
    let s2 = sts[k];
    assert(s2 == exec(s, op));
    lemma_hist(s, op);
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] req_prov(sts, ops, k, i) && appr_prov(sts, ops, k, i) by {
        let r2 = s2.requests[i];
        if i < s.requests.len() {
            let r = s.requests[i];
            assert(req_prov(sts, ops, k - 1, i));
            assert(appr_prov(sts, ops, k - 1, i));
            assert(same_content(r, r2));
            let k1 = choose|k1: int| k1 < k - 1 && #[trigger] request_made(sts, ops, k1, i, r);
            assert(request_made(sts, ops, k1, i, r2));
            if r2.approval is Some {
                if r.approval is Some {
                    let a = r.approval->Some_0;
                    assert(r2.approval == r.approval);
                    let (j1, j2) = choose|j1: int, j2: int|
                        #![trigger request_made(sts, ops, j1, i, r), approval_made(sts, ops, j2, i, r, a)]
                        j1 < j2 < k - 1
                        && request_made(sts, ops, j1, i, r)
                        && approval_made(sts, ops, j2, i, r, a)
                        && continuous(sts, j1, j2, r.agent_key, r.agent_registration_id);
                    assert(request_made(sts, ops, j1, i, r2));
                    assert(approval_made(sts, ops, j2, i, r2, a));
                } else {
                    // Approved by this very step.
                    let a = r2.approval->Some_0;
                    match op {
                        Op::Approve { c, id, act, now } => {
                            assert(id == i);
                            let ak = r.agent_key;
                            assert(s.principals.dom().contains(ak));
                            assert(r.id == i);
                            assert(inv_kr(s, ak, i));
                            assert(approval_made(sts, ops, k - 1, i, r2, a));
                            // The agent held r's registration at the request and holds it now.
                            assert(k1 <= k - 1);
                            lemma_reg_stays(sts, ops, k1, k - 1, ak, r.agent_registration_id);
                            assert(continuous(sts, k1, k - 1, r2.agent_key, r2.agent_registration_id));
                        },
                        _ => {},
                    }
                }
            }
        } else {
            // Created by this very step.
            match op {
                Op::Request { c, action, now } => {
                    assert(request_made(sts, ops, k - 1, i, r2));
                },
                _ => {},
            }
        }
    }
}

// ---------------------------------------------------------------------------
// TR-7: the revocation record
// ---------------------------------------------------------------------------

/// Step `k` is a successful revocation of registration `g`.
pub open spec fn revoked_at<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int, g: RegistrationId) -> bool {
    &&& 0 <= k < ops.len()
    &&& ok(sts[k], ops[k])
    &&& ops[k] matches Op::Revoke { key, .. }
    &&& sts[k].principals[key].registration_id == g
}

/// Step `k` is a successful Add that issued registration `g`.
pub open spec fn added_at<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int, g: RegistrationId) -> bool {
    &&& 0 <= k < ops.len()
    &&& ok(sts[k], ops[k])
    &&& ops[k] is Add
    &&& sts[k].reg_count == g
}

pub open spec fn op_time<A, K>(op: Op<A, K>) -> BlockTime {
    op_now(op, BlockTime { height: 0, timestamp_ns: 0 })
}

/// TR-7 at state `k`: the revocation record lists exactly the successful
/// revocations before `k`, each once, with its time, and each id it lists
/// was issued, fresh, by an earlier Add.
pub open spec fn tr7<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int) -> bool {
    let v = sts[k].revocations;
    &&& forall|g: RegistrationId| #[trigger] v.dom().contains(g) ==> exists|j: int| j < k && #[trigger] revoked_at(sts, ops, j, g)
    &&& forall|g: RegistrationId, j: int| j < k && #[trigger] revoked_at(sts, ops, j, g) ==> {
        &&& v.dom().contains(g)
        &&& v[g] == op_time(ops[j])
        &&& exists|j0: int| j0 < j && #[trigger] added_at(sts, ops, j0, g)
    }
    &&& forall|g: RegistrationId, j1: int, j2: int|
        j1 < k && j2 < k && #[trigger] revoked_at(sts, ops, j1, g) && #[trigger] revoked_at(sts, ops, j2, g) ==> j1 == j2
}

/// Every live registration was issued by an earlier Add.
pub open spec fn issued<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int) -> bool {
    forall|key: K| #[trigger] sts[k].principals.dom().contains(key)
        ==> exists|j0: int| j0 < k && #[trigger] added_at(sts, ops, j0, sts[k].principals[key].registration_id)
}

/// PROP: TR-7
pub proof fn lemma_tr7<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, k: int)
    requires
        from_init(sts, ops),
        0 <= k <= ops.len(),
    ensures
        tr7(sts, ops, k),
        issued(sts, ops, k),
    decreases k,
{
    if k == 0 {
        assert(sts[0].revocations.dom() =~= Set::empty());
        return;
    }
    lemma_tr7(sts, ops, k - 1);
    lemma_init_run_inv(sts, ops, k - 1);
    let s = sts[k - 1];
    let op = ops[k - 1];
    let s2 = sts[k];
    assert(s2 == exec(s, op));
    lemma_hist(s, op);
    // issued
    assert forall|key: K| #[trigger] s2.principals.dom().contains(key)
        implies exists|j0: int| j0 < k && #[trigger] added_at(sts, ops, j0, s2.principals[key].registration_id) by {
        if s.principals.dom().contains(key) && s.principals[key].registration_id == s2.principals[key].registration_id {
            let j0 = choose|j0: int| j0 < k - 1 && #[trigger] added_at(sts, ops, j0, s.principals[key].registration_id);
            assert(added_at(sts, ops, j0, s2.principals[key].registration_id));
        } else {
            match op {
                Op::Add { .. } => {
                    assert(ok(s, op));
                    assert(added_at(sts, ops, k - 1, s2.principals[key].registration_id));
                },
                Op::Revoke { .. } => {},
                _ => {
                    assert(same_reg(s.principals[key], s2.principals[key]));
                },
            }
        }
    }
    // tr7: listed => revoked earlier
    assert forall|g: RegistrationId| #[trigger] s2.revocations.dom().contains(g)
        implies exists|j: int| j < k && #[trigger] revoked_at(sts, ops, j, g) by {
        if s.revocations.dom().contains(g) {
            let j = choose|j: int| j < k - 1 && #[trigger] revoked_at(sts, ops, j, g);
            assert(revoked_at(sts, ops, j, g));
        } else {
            assert(revoked_at(sts, ops, k - 1, g));
        }
    }
    // tr7: revoked earlier => listed with its time, issued by an Add
    assert forall|g: RegistrationId, j: int| j < k && #[trigger] revoked_at(sts, ops, j, g) implies {
        &&& s2.revocations.dom().contains(g)
        &&& s2.revocations[g] == op_time(ops[j])
        &&& exists|j0: int| j0 < j && #[trigger] added_at(sts, ops, j0, g)
    } by {
        if j < k - 1 {
            assert(s.revocations.dom().contains(g));
        } else {
            match op {
                Op::Revoke { caller, key, now } => {
                    assert(s.principals.dom().contains(key));
                    let j0 = choose|j0: int| j0 < k - 1 && #[trigger] added_at(sts, ops, j0, s.principals[key].registration_id);
                    assert(added_at(sts, ops, j0, g));
                },
                _ => {},
            }
        }
    }
    // tr7: each id revoked once
    assert forall|g: RegistrationId, j1: int, j2: int|
        j1 < k && j2 < k && #[trigger] revoked_at(sts, ops, j1, g) && #[trigger] revoked_at(sts, ops, j2, g) implies j1 == j2 by {
        if j1 < k - 1 && j2 == k - 1 {
            lemma_revoked_then_not_live(sts, ops, j1, k - 1, g);
        } else if j2 < k - 1 && j1 == k - 1 {
            lemma_revoked_then_not_live(sts, ops, j2, k - 1, g);
        }
    }
}

/// Once revoked at step `j`, registration `g` is no key's current one later,
/// so it cannot be revoked again.
proof fn lemma_revoked_then_not_live<A, K>(sts: Seq<AbsStore<A, K>>, ops: Seq<Op<A, K>>, j: int, k: int, g: RegistrationId)
    requires
        from_init(sts, ops),
        0 <= j < k < ops.len(),
        revoked_at(sts, ops, j, g),
    ensures
        !revoked_at(sts, ops, k, g),
{
    lemma_init_run_inv(sts, ops, j);
    lemma_init_run_inv(sts, ops, k);
    lemma_hist(sts[j], ops[j]);
    assert(sts[j + 1] == exec(sts[j], ops[j]));
    match ops[j] {
        Op::Revoke { key, .. } => assert(sts[j].principals.dom().contains(key)),
        _ => {},
    }
    assert(sts[j + 1].revocations.dom().contains(g));
    lemma_run_grows(sts, ops, j + 1, k);
    match ops[k] {
        Op::Revoke { key, .. } => {
            if ok(sts[k], ops[k]) {
                assert(sts[k].principals.dom().contains(key));
            }
        },
        _ => {},
    }
}

} // verus!
