//! The spec machine preserves `inv` at every store size (no bounds). With
//! the twin's `refines` postconditions this closes the precondition chain:
//! a store that satisfies `inv` keeps satisfying it under every core call.

use crate::*;
use vstd::prelude::*;

verus! {

pub open spec fn steps_to<A, K, T>(sp: Result<(AbsStore<A, K>, T), ApprovalError>, s2: AbsStore<A, K>) -> bool {
    sp matches Ok((t, _)) && t == s2
}

pub proof fn lemma_add_inv<A, K>(s: AbsStore<A, K>, caller: A, key: K, acct: A, role: Role, s2: AbsStore<A, K>)
    requires
        inv(s),
        steps_to(add_spec(s, caller, key, acct, role), s2),
    ensures
        inv(s2),
{
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies
        s2.principals[k].registration_id < s2.reg_count
        && !s2.revocations.dom().contains(s2.principals[k].registration_id) by {
        if k != key {
            assert(s.principals.dom().contains(k));
        }
    }
    assert forall|k1: K, k2: K|
        #[trigger] s2.principals.dom().contains(k1) && #[trigger] s2.principals.dom().contains(k2)
            && s2.principals[k1].registration_id == s2.principals[k2].registration_id implies k1 == k2 by {
        if k1 != key {
            assert(s.principals.dom().contains(k1));
        }
        if k2 != key {
            assert(s.principals.dom().contains(k2));
        }
    }
}

pub proof fn lemma_revoke_inv<A, K>(s: AbsStore<A, K>, caller: A, key: K, now: BlockTime, s2: AbsStore<A, K>)
    requires
        inv(s),
        steps_to(revoke_spec(s, caller, key, now), s2),
    ensures
        inv(s2),
{
    let g = s.principals[key].registration_id;
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies
        s2.principals[k].registration_id < s2.reg_count
        && !s2.revocations.dom().contains(s2.principals[k].registration_id) by {
        assert(s.principals.dom().contains(k) && s.principals.dom().contains(key));
    }
    assert forall|x: RegistrationId| #[trigger] s2.revocations.dom().contains(x) implies x < s2.reg_count by {
        assert(s.principals.dom().contains(key));
    }
}

pub proof fn lemma_request_inv<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, action: String, now: BlockTime, s2: AbsStore<A, K>)
    requires
        inv(s),
        steps_to(request_spec(s, c, action, now), s2),
    ensures
        inv(s2),
{
    let k0 = c.signer_key;
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] s2.requests[i].id == i by {
        if i < s.requests.len() {
            assert(s2.requests[i] == s.requests[i]);
        } else {
            assert(s.requests.len() < u64::MAX);
            assert(s2.requests[i].id == s.requests.len() as u64);
        }
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies
        s2.principals[k].registration_id < s2.reg_count
        && !s2.revocations.dom().contains(s2.principals[k].registration_id) by {
        assert(s.principals.dom().contains(k));
    }
    assert forall|k1: K, k2: K|
        #[trigger] s2.principals.dom().contains(k1) && #[trigger] s2.principals.dom().contains(k2)
            && s2.principals[k1].registration_id == s2.principals[k2].registration_id implies k1 == k2 by {
        assert(s.principals.dom().contains(k1) && s.principals.dom().contains(k2));
    }
}

pub proof fn lemma_approve_inv<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, id: RequestId, action: Seq<char>, now: BlockTime, s2: AbsStore<A, K>)
    requires
        inv(s),
        steps_to(approve_spec(s, c, id, action, now), s2),
    ensures
        inv(s2),
{
    let r = s.requests[id as int];
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] s2.requests[i].id == i by {
        assert(s.requests[i].id == i);
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies
        s2.principals[k].registration_id < s2.reg_count
        && !s2.revocations.dom().contains(s2.principals[k].registration_id) by {
        assert(s.principals.dom().contains(k));
    }
    assert forall|k1: K, k2: K|
        #[trigger] s2.principals.dom().contains(k1) && #[trigger] s2.principals.dom().contains(k2)
            && s2.principals[k1].registration_id == s2.principals[k2].registration_id implies k1 == k2 by {
        assert(s.principals.dom().contains(k1) && s.principals.dom().contains(k2));
    }
}

pub proof fn lemma_reject_inv<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, id: RequestId, now: BlockTime, s2: AbsStore<A, K>)
    requires
        inv(s),
        steps_to(reject_spec(s, c, id, now), s2),
    ensures
        inv(s2),
{
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] s2.requests[i].id == i by {
        assert(s.requests[i].id == i);
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies
        s2.principals[k].registration_id < s2.reg_count
        && !s2.revocations.dom().contains(s2.principals[k].registration_id) by {
        assert(s.principals.dom().contains(k));
    }
    assert forall|k1: K, k2: K|
        #[trigger] s2.principals.dom().contains(k1) && #[trigger] s2.principals.dom().contains(k2)
            && s2.principals[k1].registration_id == s2.principals[k2].registration_id implies k1 == k2 by {
        assert(s.principals.dom().contains(k1) && s.principals.dom().contains(k2));
    }
}

/// The empty store satisfies `inv`.
pub proof fn lemma_init_inv<A, K>(owner: A)
    ensures
        inv(AbsStore::<A, K> {
            owner,
            principals: Map::empty(),
            requests: Seq::empty(),
            log: Seq::empty(),
            reg_count: 0,
            revocations: Map::empty(),
        }),
{
}

/// INV-5 (separation of duties) and INV-13 (one decision), at every size.
pub open spec fn duties<A, K>(s: AbsStore<A, K>) -> bool {
    forall|i: int| 0 <= i < s.requests.len() ==> {
        let r = #[trigger] s.requests[i];
        &&& (r.approval matches Some(x) ==> x.approver_account_id != r.agent_account_id)
        &&& (r.rejection matches Some(x) ==> x.approver_account_id != r.agent_account_id)
        &&& !(r.approval is Some && r.rejection is Some)
    }
}

pub proof fn lemma_duties<A, K>(s: AbsStore<A, K>, s2: AbsStore<A, K>, op: Op<A, K>)
    requires
        inv(s),
        duties(s),
        steps_to(op_spec(s, op), s2),
    ensures
        duties(s2),
{
    match op {
        Op::Request { c, action, now } => {
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& (r.approval matches Some(x) ==> x.approver_account_id != r.agent_account_id)
                &&& (r.rejection matches Some(x) ==> x.approver_account_id != r.agent_account_id)
                &&& !(r.approval is Some && r.rejection is Some)
            } by {
                if i < s.requests.len() {
                    assert(s2.requests[i] == s.requests[i]);
                }
            }
        },
        Op::Approve { c, id, act, now } => {
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& (r.approval matches Some(x) ==> x.approver_account_id != r.agent_account_id)
                &&& (r.rejection matches Some(x) ==> x.approver_account_id != r.agent_account_id)
                &&& !(r.approval is Some && r.rejection is Some)
            } by {
                assert(s.requests[i] == s.requests[i]);
            }
        },
        Op::Reject { c, id, now } => {
            assert forall|i: int| 0 <= i < s2.requests.len() implies {
                let r = #[trigger] s2.requests[i];
                &&& (r.approval matches Some(x) ==> x.approver_account_id != r.agent_account_id)
                &&& (r.rejection matches Some(x) ==> x.approver_account_id != r.agent_account_id)
                &&& !(r.approval is Some && r.rejection is Some)
            } by {
                assert(s.requests[i] == s.requests[i]);
            }
        },
        _ => {},
    }
}

/// One step of the machine, for trace-level statements.
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub enum Op<A, K> {
    Add { caller: A, key: K, acct: A, role: Role },
    Revoke { caller: A, key: K, now: BlockTime },
    Request { c: Caller<A, K>, action: String, now: BlockTime },
    Approve { c: Caller<A, K>, id: RequestId, act: Seq<char>, now: BlockTime },
    Reject { c: Caller<A, K>, id: RequestId, now: BlockTime },
}

pub open spec fn op_spec<A, K>(s: AbsStore<A, K>, op: Op<A, K>) -> Result<(AbsStore<A, K>, ()), ApprovalError> {
    match op {
        Op::Add { caller, key, acct, role } => unit(add_spec(s, caller, key, acct, role)),
        Op::Revoke { caller, key, now } => unit(revoke_spec(s, caller, key, now)),
        Op::Request { c, action, now } => unit(request_spec(s, c, action, now)),
        Op::Approve { c, id, act, now } => unit(approve_spec(s, c, id, act, now)),
        Op::Reject { c, id, now } => unit(reject_spec(s, c, id, now)),
    }
}

pub open spec fn unit<A, K, T>(r: Result<(AbsStore<A, K>, T), ApprovalError>) -> Result<(AbsStore<A, K>, ()), ApprovalError> {
    match r {
        Ok((s, _)) => Ok((s, ())),
        Err(e) => Err(e),
    }
}

pub proof fn lemma_inv<A, K>(s: AbsStore<A, K>, s2: AbsStore<A, K>, op: Op<A, K>)
    requires
        inv(s),
        steps_to(op_spec(s, op), s2),
    ensures
        inv(s2),
{
    match op {
        Op::Add { caller, key, acct, role } => lemma_add_inv(s, caller, key, acct, role, s2),
        Op::Revoke { caller, key, now } => lemma_revoke_inv(s, caller, key, now, s2),
        Op::Request { c, action, now } => lemma_request_inv(s, c, action, now, s2),
        Op::Approve { c, id, act, now } => lemma_approve_inv(s, c, id, act, now, s2),
        Op::Reject { c, id, now } => lemma_reject_inv(s, c, id, now, s2),
    }
}

} // verus!
