//! Catalogue invariants (strategy.md §5.2) over the spec machine, at every
//! store size. `full_inv` is the conjunction INV-0..16 and LEM-1/2; it holds
//! on the empty store and every operation preserves it (`lemma_full_inv`).
//! With the twin's `refines` postconditions these are statements about the
//! real core on any `Store` that meets the trait contract (ASM-STORE).
//!
//! Each property's predicate carries a `PROP:` tag (status-lint).

use crate::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Counting over the request sequence
// ---------------------------------------------------------------------------

/// Number of positions `i` with `f(i, rs[i])`.
pub open spec fn count<A, K>(rs: Seq<ActionRequest<A, K>>, f: spec_fn(int, ActionRequest<A, K>) -> bool) -> nat
    decreases rs.len(),
{
    if rs.len() == 0 {
        0
    } else {
        count(rs.drop_last(), f) + if f(rs.len() - 1, rs.last()) { 1nat } else { 0nat }
    }
}

pub proof fn lemma_count_push<A, K>(rs: Seq<ActionRequest<A, K>>, r: ActionRequest<A, K>, f: spec_fn(int, ActionRequest<A, K>) -> bool)
    ensures
        count(rs.push(r), f) == count(rs, f) + if f(rs.len() as int, r) { 1nat } else { 0nat },
{
    assert(rs.push(r).drop_last() =~= rs);
}

pub proof fn lemma_count_update<A, K>(rs: Seq<ActionRequest<A, K>>, i: int, r: ActionRequest<A, K>, f: spec_fn(int, ActionRequest<A, K>) -> bool)
    requires
        0 <= i < rs.len(),
    ensures
        count(rs.update(i, r), f) + (if f(i, rs[i]) { 1nat } else { 0nat })
            == count(rs, f) + (if f(i, r) { 1nat } else { 0nat }),
    decreases rs.len(),
{
    let u = rs.update(i, r);
    if i == rs.len() - 1 {
        assert(u.drop_last() =~= rs.drop_last());
    } else {
        assert(u.drop_last() =~= rs.drop_last().update(i, r));
        lemma_count_update(rs.drop_last(), i, r, f);
    }
}

pub proof fn lemma_count_le<A, K>(rs: Seq<ActionRequest<A, K>>, f: spec_fn(int, ActionRequest<A, K>) -> bool)
    ensures
        count(rs, f) <= rs.len(),
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_count_le(rs.drop_last(), f);
    }
}

pub proof fn lemma_count_lt<A, K>(rs: Seq<ActionRequest<A, K>>, f: spec_fn(int, ActionRequest<A, K>) -> bool, i: int)
    requires
        0 <= i < rs.len(),
        !f(i, rs[i]),
    ensures
        count(rs, f) < rs.len(),
    decreases rs.len(),
{
    lemma_count_le(rs.drop_last(), f);
    if i < rs.len() - 1 {
        lemma_count_lt(rs.drop_last(), f, i);
    }
}

pub proof fn lemma_count_zero<A, K>(rs: Seq<ActionRequest<A, K>>, f: spec_fn(int, ActionRequest<A, K>) -> bool)
    requires
        forall|i: int| 0 <= i < rs.len() ==> !f(i, #[trigger] rs[i]),
    ensures
        count(rs, f) == 0,
    decreases rs.len(),
{
    if rs.len() > 0 {
        lemma_count_zero(rs.drop_last(), f);
    }
}

pub open spec fn undecided<A, K>(r: ActionRequest<A, K>) -> bool {
    r.approval is None && r.rejection is None
}

/// `Pend(s, k)`: undecided requests of key `k` at positions `>= from`.
pub open spec fn pend_f<A, K>(k: K, from: u64) -> spec_fn(int, ActionRequest<A, K>) -> bool {
    |i: int, r: ActionRequest<A, K>| i >= from && r.agent_key == k && undecided(r)
}

pub open spec fn pend<A, K>(s: AbsStore<A, K>, k: K, from: u64) -> nat {
    count(s.requests, pend_f(k, from))
}

pub open spec fn app_f<A, K>() -> spec_fn(int, ActionRequest<A, K>) -> bool {
    |i: int, r: ActionRequest<A, K>| r.approval is Some
}

/// Number of approved requests.
pub open spec fn napp<A, K>(s: AbsStore<A, K>) -> nat {
    count(s.requests, app_f())
}

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// Per request `i`.
pub open spec fn inv_req<A, K>(s: AbsStore<A, K>, i: int) -> bool {
    let r = s.requests[i];
    // PROP: INV-2
    &&& r.action@.len() > 0
    &&& byte_len(r.action@) <= MAX_ACTION_LEN
    // PROP: INV-4 INV-5 INV-6 INV-14
    &&& (r.approval matches Some(x) ==> {
        &&& x.approval_index < s.log.len()
        &&& s.log[x.approval_index as int] == i
        &&& x.approver_account_id != r.agent_account_id
        &&& x.approver_key != r.agent_key
        &&& x.approver_registration_id < s.reg_count
    })
    &&& (r.rejection matches Some(y) ==> {
        &&& y.approver_account_id != r.agent_account_id
        &&& y.approver_key != r.agent_key
        &&& y.approver_registration_id < s.reg_count
    })
    // PROP: INV-13
    &&& !(r.approval is Some && r.rejection is Some)
    &&& r.agent_registration_id < s.reg_count
}

/// Per log slot `j`. PROP: INV-3
pub open spec fn inv_log<A, K>(s: AbsStore<A, K>, j: int) -> bool {
    &&& s.log[j] < s.requests.len()
    &&& s.requests[s.log[j] as int].approval matches Some(x)
    &&& x.approval_index == j
}

/// Per registered key `k`. PROP: INV-7 INV-9
pub open spec fn inv_key<A, K>(s: AbsStore<A, K>, k: K) -> bool {
    let p = s.principals[k];
    &&& p.active_from <= s.requests.len()
    &&& p.pending == pend(s, k, p.active_from)
    &&& p.pending <= MAX_PENDING_PER_KEY
}

/// Per registered key `k` and request `i`. PROP: INV-8 INV-16
pub open spec fn inv_kr<A, K>(s: AbsStore<A, K>, k: K, i: int) -> bool {
    let p = s.principals[k];
    let r = s.requests[i];
    // INV-8
    &&& (r.agent_key == k && i >= p.active_from ==> {
        &&& r.agent_account_id == p.account_id
        &&& p.role == Role::Agent
        &&& r.agent_registration_id == p.registration_id
    })
    // INV-16
    &&& (r.agent_registration_id == p.registration_id ==> {
        &&& r.agent_key == k
        &&& r.agent_account_id == p.account_id
        &&& p.role == Role::Agent
    })
    &&& (r.approval matches Some(x) ==> (x.approver_registration_id == p.registration_id ==> {
        &&& x.approver_key == k
        &&& x.approver_account_id == p.account_id
        &&& p.role == Role::Approver
    }))
    &&& (r.rejection matches Some(y) ==> (y.approver_registration_id == p.registration_id ==> {
        &&& y.approver_key == k
        &&& y.approver_account_id == p.account_id
        &&& p.role == Role::Approver
    }))
}

/// Registration id `g` is some registered key's current registration.
pub open spec fn live_reg<A, K>(s: AbsStore<A, K>, g: RegistrationId) -> bool {
    exists|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == g
}

/// INV-0 holds by representation: `principals` is a `Map` (a function from
/// keys), and MemStore's `wf` keeps its association list duplicate-free.
/// PROP: INV-0 INV-1 INV-11 INV-12 (in `inv`) INV-15 LEM-2
pub open spec fn full_inv<A, K>(s: AbsStore<A, K>) -> bool {
    &&& inv(s)
    &&& forall|i: int| 0 <= i < s.requests.len() ==> #[trigger] inv_req(s, i)
    &&& forall|j: int| 0 <= j < s.log.len() ==> #[trigger] inv_log(s, j)
    &&& forall|k: K| #[trigger] s.principals.dom().contains(k) ==> inv_key(s, k)
    &&& forall|k: K, i: int| #[trigger] s.principals.dom().contains(k) && 0 <= i < s.requests.len()
        ==> #[trigger] inv_kr(s, k, i)
    // INV-15: every issued registration is live or revoked, and the counts add up.
    &&& forall|g: RegistrationId| g < s.reg_count ==> live_reg(s, g) || #[trigger] s.revocations.dom().contains(g)
    &&& s.principals.len() + s.revocations.len() == s.reg_count
    // LEM-2
    &&& s.log.len() == napp(s)
}

pub open spec fn init<A, K>(owner: A) -> AbsStore<A, K> {
    AbsStore {
        owner,
        principals: Map::empty(),
        requests: Seq::empty(),
        log: Seq::empty(),
        reg_count: 0,
        revocations: Map::empty(),
    }
}

pub proof fn lemma_init_full<A, K>(owner: A)
    ensures
        full_inv(init::<A, K>(owner)),
{
    lemma_init_inv::<A, K>(owner);
    let s = init::<A, K>(owner);
    assert(s.principals.dom() =~= Set::empty());
    assert(s.revocations.dom() =~= Set::empty());
}

/// The post-state of `op` (the pre-state when it fails: TX-0).
pub open spec fn exec<A, K>(s: AbsStore<A, K>, op: Op<A, K>) -> AbsStore<A, K> {
    match op_spec(s, op) {
        Ok((t, _)) => t,
        Err(_) => s,
    }
}

pub open spec fn ok<A, K>(s: AbsStore<A, K>, op: Op<A, K>) -> bool {
    op_spec(s, op) is Ok
}

// ---------------------------------------------------------------------------
// Preservation, one operation at a time
// ---------------------------------------------------------------------------

proof fn lemma_add_full<A, K>(s: AbsStore<A, K>, caller: A, key: K, acct: A, role: Role, s2: AbsStore<A, K>)
    requires
        full_inv(s),
        steps_to(add_spec(s, caller, key, acct, role), s2),
    ensures
        full_inv(s2),
{
    lemma_add_inv(s, caller, key, acct, role, s2);
    let g = s.reg_count;
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] inv_req(s2, i) by {
        assert(inv_req(s, i));
    }
    assert forall|j: int| 0 <= j < s2.log.len() implies #[trigger] inv_log(s2, j) by {
        assert(inv_log(s, j));
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies inv_key(s2, k) by {
        if k == key {
            lemma_count_zero(s.requests, pend_f::<A, K>(key, s.requests.len() as u64));
        } else {
            assert(s.principals.dom().contains(k) && inv_key(s, k));
        }
    }
    assert forall|k: K, i: int| #[trigger] s2.principals.dom().contains(k) && 0 <= i < s2.requests.len()
        implies #[trigger] inv_kr(s2, k, i) by {
        assert(inv_req(s, i));
        if k != key {
            assert(s.principals.dom().contains(k) && inv_kr(s, k, i));
        }
    }
    assert forall|x: RegistrationId| x < s2.reg_count implies live_reg(s2, x) || #[trigger] s2.revocations.dom().contains(x) by {
        if x == g {
            assert(s2.principals.dom().contains(key));
        } else if !s.revocations.dom().contains(x) {
            assert(live_reg(s, x));
            let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == x;
            assert(s2.principals.dom().contains(k0));
        }
    }
    assert(s2.principals.dom() =~= s.principals.dom().insert(key));
    vstd::set::lemma_set_insert_len(s.principals.dom(), key);
}

proof fn lemma_revoke_full<A, K>(s: AbsStore<A, K>, caller: A, key: K, now: BlockTime, s2: AbsStore<A, K>)
    requires
        full_inv(s),
        steps_to(revoke_spec(s, caller, key, now), s2),
    ensures
        full_inv(s2),
{
    lemma_revoke_inv(s, caller, key, now, s2);
    let g = s.principals[key].registration_id;
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] inv_req(s2, i) by {
        assert(inv_req(s, i));
    }
    assert forall|j: int| 0 <= j < s2.log.len() implies #[trigger] inv_log(s2, j) by {
        assert(inv_log(s, j));
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies inv_key(s2, k) by {
        assert(s.principals.dom().contains(k) && inv_key(s, k));
    }
    assert forall|k: K, i: int| #[trigger] s2.principals.dom().contains(k) && 0 <= i < s2.requests.len()
        implies #[trigger] inv_kr(s2, k, i) by {
        assert(s.principals.dom().contains(k) && inv_kr(s, k, i));
    }
    assert forall|x: RegistrationId| x < s2.reg_count implies live_reg(s2, x) || #[trigger] s2.revocations.dom().contains(x) by {
        if !s.revocations.dom().contains(x) && x != g {
            assert(live_reg(s, x));
            let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == x;
            assert(k0 != key);
            assert(s2.principals.dom().contains(k0));
        }
    }
    assert(s.principals.dom().contains(key));
    assert(s2.principals.dom() =~= s.principals.dom().remove(key));
    assert(s2.revocations.dom() =~= s.revocations.dom().insert(g));
    vstd::set::lemma_set_remove_len(s.principals.dom(), key);
    vstd::set::lemma_set_insert_len(s.revocations.dom(), g);
}

proof fn lemma_request_full<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, action: String, now: BlockTime, s2: AbsStore<A, K>)
    requires
        full_inv(s),
        steps_to(request_spec(s, c, action, now), s2),
    ensures
        full_inv(s2),
{
    lemma_request_inv(s, c, action, now, s2);
    let ck = c.signer_key;
    let p = s.principals[ck];
    let n = s.requests.len();
    let r = s2.requests[n as int];
    assert(s.principals.dom().contains(ck));
    assert(inv_key(s, ck));
    assert(s2.requests == s.requests.push(r));
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] inv_req(s2, i) by {
        if i < n {
            assert(inv_req(s, i));
        }
    }
    assert forall|j: int| 0 <= j < s2.log.len() implies #[trigger] inv_log(s2, j) by {
        assert(inv_log(s, j));
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies inv_key(s2, k) by {
        assert(s.principals.dom().contains(k) && inv_key(s, k));
        lemma_count_push(s.requests, r, pend_f::<A, K>(k, s.principals[k].active_from));
    }
    assert forall|k: K, i: int| #[trigger] s2.principals.dom().contains(k) && 0 <= i < s2.requests.len()
        implies #[trigger] inv_kr(s2, k, i) by {
        assert(s.principals.dom().contains(k));
        if i < n {
            assert(inv_kr(s, k, i));
        } else if r.agent_registration_id == s2.principals[k].registration_id {
            assert(k == ck);
        }
    }
    assert forall|x: RegistrationId| x < s2.reg_count implies live_reg(s2, x) || #[trigger] s2.revocations.dom().contains(x) by {
        if !s.revocations.dom().contains(x) {
            assert(live_reg(s, x));
            let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == x;
            assert(s2.principals.dom().contains(k0));
        }
    }
    assert(s2.principals.dom() =~= s.principals.dom());
    lemma_count_push(s.requests, r, app_f::<A, K>());
}

proof fn lemma_approve_full<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, id: RequestId, act: Seq<char>, now: BlockTime, s2: AbsStore<A, K>)
    requires
        full_inv(s),
        steps_to(approve_spec(s, c, id, act, now), s2),
    ensures
        full_inv(s2),
{
    lemma_approve_inv(s, c, id, act, now, s2);
    let ck = c.signer_key;
    let r = s.requests[id as int];
    let ak = r.agent_key;
    let g = s.principals[ak];
    let n = s.log.len();
    let r2 = s2.requests[id as int];
    assert(s.principals.dom().contains(ck) && s.principals.dom().contains(ak));
    assert(ck != ak);  // roles differ
    assert(inv_req(s, id as int) && inv_key(s, ak));
    assert(s2.requests == s.requests.update(id as int, r2));
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] inv_req(s2, i) by {
        assert(inv_req(s, i));
    }
    assert forall|j: int| 0 <= j < s2.log.len() implies #[trigger] inv_log(s2, j) by {
        if j < n {
            assert(inv_log(s, j));
        }
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies inv_key(s2, k) by {
        assert(s.principals.dom().contains(k) && inv_key(s, k));
        lemma_count_update(s.requests, id as int, r2, pend_f::<A, K>(k, s.principals[k].active_from));
    }
    assert forall|k: K, i: int| #[trigger] s2.principals.dom().contains(k) && 0 <= i < s2.requests.len()
        implies #[trigger] inv_kr(s2, k, i) by {
        assert(s.principals.dom().contains(k) && inv_kr(s, k, i));
        if i == id && s2.principals[k].registration_id == s.principals[ck].registration_id {
            assert(k == ck);
        }
    }
    assert forall|x: RegistrationId| x < s2.reg_count implies live_reg(s2, x) || #[trigger] s2.revocations.dom().contains(x) by {
        if !s.revocations.dom().contains(x) {
            assert(live_reg(s, x));
            let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == x;
            assert(s2.principals.dom().contains(k0));
        }
    }
    assert(s2.principals.dom() =~= s.principals.dom());
    lemma_count_update(s.requests, id as int, r2, app_f::<A, K>());
}

proof fn lemma_reject_full<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, id: RequestId, now: BlockTime, s2: AbsStore<A, K>)
    requires
        full_inv(s),
        steps_to(reject_spec(s, c, id, now), s2),
    ensures
        full_inv(s2),
{
    lemma_reject_inv(s, c, id, now, s2);
    let ck = c.signer_key;
    let r = s.requests[id as int];
    let ak = r.agent_key;
    let r2 = s2.requests[id as int];
    assert(s.principals.dom().contains(ck) && s.principals.dom().contains(ak));
    assert(ck != ak);
    assert(inv_req(s, id as int) && inv_key(s, ak));
    assert(s2.requests == s.requests.update(id as int, r2));
    assert forall|i: int| 0 <= i < s2.requests.len() implies #[trigger] inv_req(s2, i) by {
        assert(inv_req(s, i));
    }
    assert forall|j: int| 0 <= j < s2.log.len() implies #[trigger] inv_log(s2, j) by {
        assert(inv_log(s, j));
    }
    assert forall|k: K| #[trigger] s2.principals.dom().contains(k) implies inv_key(s2, k) by {
        assert(s.principals.dom().contains(k) && inv_key(s, k));
        lemma_count_update(s.requests, id as int, r2, pend_f::<A, K>(k, s.principals[k].active_from));
    }
    assert forall|k: K, i: int| #[trigger] s2.principals.dom().contains(k) && 0 <= i < s2.requests.len()
        implies #[trigger] inv_kr(s2, k, i) by {
        assert(s.principals.dom().contains(k) && inv_kr(s, k, i));
        if i == id && s2.principals[k].registration_id == s.principals[ck].registration_id {
            assert(k == ck);
        }
    }
    assert forall|x: RegistrationId| x < s2.reg_count implies live_reg(s2, x) || #[trigger] s2.revocations.dom().contains(x) by {
        if !s.revocations.dom().contains(x) {
            assert(live_reg(s, x));
            let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == x;
            assert(s2.principals.dom().contains(k0));
        }
    }
    assert(s2.principals.dom() =~= s.principals.dom());
    lemma_count_update(s.requests, id as int, r2, app_f::<A, K>());
}

/// Every operation preserves the full invariant, at every store size.
pub proof fn lemma_full_inv<A, K>(s: AbsStore<A, K>, op: Op<A, K>)
    requires
        full_inv(s),
    ensures
        full_inv(exec(s, op)),
{
    let s2 = exec(s, op);
    if ok(s, op) {
        match op {
            Op::Add { caller, key, acct, role } => lemma_add_full(s, caller, key, acct, role, s2),
            Op::Revoke { caller, key, now } => lemma_revoke_full(s, caller, key, now, s2),
            Op::Request { c, action, now } => lemma_request_full(s, c, action, now, s2),
            Op::Approve { c, id, act, now } => lemma_approve_full(s, c, id, act, now, s2),
            Op::Reject { c, id, now } => lemma_reject_full(s, c, id, now, s2),
        }
    }
}

// ---------------------------------------------------------------------------
// Consequences
// ---------------------------------------------------------------------------

/// LEM-1: the approval log has no duplicates. PROP: LEM-1
pub proof fn lemma_log_distinct<A, K>(s: AbsStore<A, K>, j1: int, j2: int)
    requires
        full_inv(s),
        0 <= j1 < s.log.len(),
        0 <= j2 < s.log.len(),
        j1 != j2,
    ensures
        s.log[j1] != s.log[j2],
{
    assert(inv_log(s, j1) && inv_log(s, j2));
}

/// LEM-2's bound and LEM-3: an unapproved request exists => #L < #R, so
/// approve's LogFull is unreachable (F-7). PROP: LEM-2 LEM-3
pub proof fn lemma_log_room<A, K>(s: AbsStore<A, K>, i: int)
    requires
        full_inv(s),
        0 <= i < s.requests.len(),
        s.requests[i].approval is None,
    ensures
        s.log.len() < s.requests.len(),
        s.log.len() < u64::MAX,
{
    lemma_count_lt(s.requests, app_f::<A, K>(), i);
}

/// LEM-4: under INV-8 the agent's liveness is just "the key is registered
/// with `active_from <= id`"; the role and account checks never decide.
/// PROP: LEM-4
pub proof fn lemma_live_reduces<A, K>(s: AbsStore<A, K>, i: int)
    requires
        full_inv(s),
        0 <= i < s.requests.len(),
    ensures
        (live_spec(s, s.requests[i]) is Some) <==> ({
            let k = s.requests[i].agent_key;
            s.principals.dom().contains(k) && s.principals[k].active_from <= i
        }),
{
    let k = s.requests[i].agent_key;
    if s.principals.dom().contains(k) {
        assert(inv_kr(s, k, i));
    }
}

/// INV-9's corollary: approver keys have nothing pending. PROP: INV-9
pub proof fn lemma_approver_pending<A, K>(s: AbsStore<A, K>, k: K)
    requires
        full_inv(s),
        s.principals.dom().contains(k),
        s.principals[k].role == Role::Approver,
    ensures
        s.principals[k].pending == 0,
{
    let p = s.principals[k];
    assert(inv_key(s, k));
    assert forall|i: int| 0 <= i < s.requests.len() implies !(pend_f::<A, K>(k, p.active_from))(i, #[trigger] s.requests[i]) by {
        assert(inv_kr(s, k, i));
    }
    lemma_count_zero(s.requests, pend_f::<A, K>(k, p.active_from));
}

} // verus!
