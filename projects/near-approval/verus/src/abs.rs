//! Abstract store and the spec machine the twin refines (strategy.md §7,
//! path A). Written from the catalogue (§5, §6.1), not from the core: guard
//! order and post-states follow the property tables and `kani/src/spec.rs`.
//!
//! Every public core function `f` has a spec `f_spec(s, ..)` returning
//! `Err(e)` (the first failing guard) or `Ok((s', ret))`. The twin's
//! `ensures` say: the function returns `Err(e)` and leaves `store@ == s`, or
//! returns `Ok(ret)` with `store@ == s'`. Nothing here is bounded.

use crate::*;
use vstd::prelude::*;

verus! {

/// What a `Store` holds, as mathematical values.
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct AbsStore<A, K> {
    pub owner: A,
    pub principals: Map<K, Principal<A>>,
    pub requests: Seq<ActionRequest<A, K>>,
    pub log: Seq<RequestId>,
    pub reg_count: u64,
    pub revocations: Map<RegistrationId, BlockTime>,
}

pub open spec fn opt<K, V>(m: Map<K, V>, k: K) -> Option<V> {
    if m.dom().contains(k) {
        Some(m[k])
    } else {
        None
    }
}

impl<A, K> AbsStore<A, K> {
    pub open spec fn principal(self, k: K) -> Option<Principal<A>> {
        opt(self.principals, k)
    }

    pub open spec fn request(self, id: RequestId) -> Option<ActionRequest<A, K>> {
        if id < self.requests.len() {
            Some(self.requests[id as int])
        } else {
            None
        }
    }

    pub open spec fn with_principal(self, k: K, p: Principal<A>) -> Self {
        AbsStore { principals: self.principals.insert(k, p), ..self }
    }
}

/// UTF-8 byte length of a string's characters: what `String::len` returns
/// (ASM-STRLEN).
pub open spec fn byte_len(s: Seq<char>) -> nat {
    vstd::utf8::encode_utf8(s).len()
}


/// `res` and the store's post-state `s2` are what the spec `sp` says for
/// pre-state `s`: on `Err(e)` the store is unchanged.
///
/// Every core mutator `ensures refines(<op>_spec(..), ..)`, which is TX-0
/// (failure leaves the store as it was) and TX-1..5/7 (exact result, guard
/// order and post-state) at every store size; `authenticate` ensures
/// `auth_spec` (TX-3). PROP: TX-0 TX-1 TX-2 TX-3 TX-4 TX-5 TX-7
pub open spec fn refines<A, K, T>(
    sp: Result<(AbsStore<A, K>, T), ApprovalError>,
    s: AbsStore<A, K>,
    s2: AbsStore<A, K>,
    res: Result<T, ApprovalError>,
) -> bool {
    match sp {
        Ok((t, v)) => res == Ok::<T, ApprovalError>(v) && s2 == t,
        Err(e) => res == Err::<T, ApprovalError>(e) && s2 == s,
    }
}

/// The part of the invariant (strategy.md §6.1) the code's own
/// preconditions need: INV-1 (dense ids, so `replace_request` hits the
/// request that was read), INV-11 and INV-12 (a live registration is not
/// yet revoked, so `insert_revocation`'s write-once law holds), and the
/// counter bounds every concrete store has.
pub open spec fn inv<A, K>(s: AbsStore<A, K>) -> bool {
    // Counters fit their `u64`s (the `Store` getters return them as `u64`).
    &&& s.requests.len() <= u64::MAX
    &&& s.log.len() <= u64::MAX
    // INV-1
    &&& forall|i: int| 0 <= i < s.requests.len() ==> #[trigger] s.requests[i].id == i
    // INV-11
    &&& forall|k: K| #[trigger] s.principals.dom().contains(k) ==> {
        &&& s.principals[k].registration_id < s.reg_count
        &&& !s.revocations.dom().contains(s.principals[k].registration_id)
    }
    &&& forall|k1: K, k2: K|
        #[trigger] s.principals.dom().contains(k1) && #[trigger] s.principals.dom().contains(k2)
            && s.principals[k1].registration_id == s.principals[k2].registration_id ==> k1 == k2
    // INV-12
    &&& forall|g: RegistrationId| #[trigger] s.revocations.dom().contains(g) ==> g < s.reg_count
}

// ---------------------------------------------------------------------------
// Spec machine
// ---------------------------------------------------------------------------

pub open spec fn add_spec<A, K>(s: AbsStore<A, K>, caller: A, key: K, acct: A, role: Role)
    -> Result<(AbsStore<A, K>, Principal<A>), ApprovalError>
{
    if caller != s.owner {
        Err(ApprovalError::NotOwner)
    } else if s.principals.dom().contains(key) {
        Err(ApprovalError::KeyAlreadyRegistered)
    } else if s.reg_count == u64::MAX {
        Err(ApprovalError::LogFull)
    } else {
        let p = Principal {
            account_id: acct,
            role,
            registration_id: s.reg_count,
            active_from: s.requests.len() as u64,
            pending: 0,
        };
        Ok((AbsStore { reg_count: (s.reg_count + 1) as u64, ..s.with_principal(key, p) }, p))
    }
}

pub open spec fn revoke_spec<A, K>(s: AbsStore<A, K>, caller: A, key: K, now: BlockTime)
    -> Result<(AbsStore<A, K>, Principal<A>), ApprovalError>
{
    if caller != s.owner {
        Err(ApprovalError::NotOwner)
    } else if !s.principals.dom().contains(key) {
        Err(ApprovalError::KeyNotRegistered)
    } else {
        let p = s.principals[key];
        Ok((
            AbsStore {
                principals: s.principals.remove(key),
                revocations: s.revocations.insert(p.registration_id, now),
                ..s
            },
            p,
        ))
    }
}

pub open spec fn auth_spec<A, K>(s: AbsStore<A, K>, c: Caller<A, K>, role: Role)
    -> Result<Principal<A>, ApprovalError>
{
    if c.predecessor != c.signer {
        Err(ApprovalError::IndirectCall)
    } else if !s.principals.dom().contains(c.signer_key) {
        Err(ApprovalError::UnknownKey)
    } else if s.principals[c.signer_key].role != role {
        Err(ApprovalError::WrongRole)
    } else if s.principals[c.signer_key].account_id != c.signer {
        Err(ApprovalError::KeyAccountMismatch)
    } else {
        Ok(s.principals[c.signer_key])
    }
}

pub open spec fn live_spec<A, K>(s: AbsStore<A, K>, r: ActionRequest<A, K>) -> Option<Principal<A>> {
    match s.principal(r.agent_key) {
        Some(p) => if p.role == Role::Agent && p.account_id == r.agent_account_id
            && p.active_from <= r.id {
            Some(p)
        } else {
            None
        },
        None => None,
    }
}

pub open spec fn request_spec<A, K>(
    s: AbsStore<A, K>,
    c: Caller<A, K>,
    action: String,
    now: BlockTime,
) -> Result<(AbsStore<A, K>, ActionRequest<A, K>), ApprovalError> {
    match auth_spec(s, c, Role::Agent) {
        Err(e) => Err(e),
        Ok(p) => if action@.len() == 0 {
            Err(ApprovalError::EmptyAction)
        } else if byte_len(action@) > MAX_ACTION_LEN {
            Err(ApprovalError::ActionTooLong)
        } else if p.pending >= MAX_PENDING_PER_KEY {
            Err(ApprovalError::TooManyPending)
        } else if s.requests.len() == u64::MAX {
            Err(ApprovalError::LogFull)
        } else {
            let r = ActionRequest {
                id: s.requests.len() as u64,
                agent_account_id: c.signer,
                agent_key: c.signer_key,
                agent_registration_id: p.registration_id,
                action,
                requested_at: now,
                approval: None,
                rejection: None,
            };
            let p2 = Principal { pending: (p.pending + 1) as u32, ..p };
            Ok((AbsStore { requests: s.requests.push(r), ..s.with_principal(c.signer_key, p2) }, r))
        },
    }
}

pub open spec fn decidable_spec<A, K>(s: AbsStore<A, K>, id: RequestId)
    -> Result<(ActionRequest<A, K>, Principal<A>), ApprovalError>
{
    match s.request(id) {
        None => Err(ApprovalError::RequestNotFound),
        Some(r) => if r.approval is Some {
            Err(ApprovalError::AlreadyApproved)
        } else if r.rejection is Some {
            Err(ApprovalError::AlreadyRejected)
        } else {
            match live_spec(s, r) {
                None => Err(ApprovalError::AgentRevoked),
                Some(p) => Ok((r, p)),
            }
        },
    }
}

pub open spec fn proof_for_spec<A, K>(r: ActionRequest<A, K>, a: Approval<A, K>) -> ApprovalProof<A, K> {
    ApprovalProof {
        approval_index: a.approval_index,
        request_id: r.id,
        action: r.action,
        agent_account_id: r.agent_account_id,
        agent_key: r.agent_key,
        agent_registration_id: r.agent_registration_id,
        requested_at: r.requested_at,
        approver_account_id: a.approver_account_id,
        approver_key: a.approver_key,
        approver_registration_id: a.approver_registration_id,
        approved_at: a.approved_at,
    }
}

pub open spec fn approve_spec<A, K>(
    s: AbsStore<A, K>,
    c: Caller<A, K>,
    id: RequestId,
    action: Seq<char>,
    now: BlockTime,
) -> Result<(AbsStore<A, K>, ApprovalProof<A, K>), ApprovalError> {
    match auth_spec(s, c, Role::Approver) {
        Err(e) => Err(e),
        Ok(b) => match decidable_spec(s, id) {
            Err(e) => Err(e),
            Ok((r, g)) => if r.action@ != action {
                Err(ApprovalError::ActionMismatch)
            } else if c.signer == r.agent_account_id {
                Err(ApprovalError::SelfApproval)
            } else if s.log.len() == u64::MAX {
                Err(ApprovalError::LogFull)
            } else {
                let a = Approval {
                    approval_index: s.log.len() as u64,
                    approver_account_id: c.signer,
                    approver_key: c.signer_key,
                    approver_registration_id: b.registration_id,
                    approved_at: now,
                };
                let r2 = ActionRequest { approval: Some(a), ..r };
                let g2 = Principal { pending: sat_sub(g.pending), ..g };
                Ok((
                    AbsStore {
                        requests: s.requests.update(id as int, r2),
                        log: s.log.push(id),
                        ..s.with_principal(r.agent_key, g2)
                    },
                    proof_for_spec(r, a),
                ))
            },
        },
    }
}

pub open spec fn sat_sub(n: u32) -> u32 {
    if n == 0 { 0 } else { (n - 1) as u32 }
}

pub open spec fn reject_spec<A, K>(
    s: AbsStore<A, K>,
    c: Caller<A, K>,
    id: RequestId,
    now: BlockTime,
) -> Result<(AbsStore<A, K>, ActionRequest<A, K>), ApprovalError> {
    match auth_spec(s, c, Role::Approver) {
        Err(e) => Err(e),
        Ok(b) => match decidable_spec(s, id) {
            Err(e) => Err(e),
            Ok((r, g)) => if c.signer == r.agent_account_id {
                Err(ApprovalError::SelfApproval)
            } else {
                let r2 = ActionRequest {
                    rejection: Some(Rejection {
                        approver_account_id: c.signer,
                        approver_key: c.signer_key,
                        approver_registration_id: b.registration_id,
                        rejected_at: now,
                    }),
                    ..r
                };
                let g2 = Principal { pending: sat_sub(g.pending), ..g };
                Ok((
                    AbsStore {
                        requests: s.requests.update(id as int, r2),
                        ..s.with_principal(r.agent_key, g2)
                    },
                    r2,
                ))
            },
        },
    }
}

pub open spec fn status_spec<A, K>(s: AbsStore<A, K>, r: ActionRequest<A, K>) -> RequestStatus {
    if r.approval is Some {
        RequestStatus::Approved
    } else if r.rejection is Some {
        RequestStatus::Rejected
    } else if live_spec(s, r) is Some {
        RequestStatus::Pending
    } else {
        RequestStatus::Void
    }
}

pub open spec fn approval_spec<A, K>(s: AbsStore<A, K>, id: RequestId) -> Option<ApprovalProof<A, K>> {
    match s.request(id) {
        Some(r) => match r.approval {
            Some(a) => Some(proof_for_spec(r, a)),
            None => None,
        },
        None => None,
    }
}

/// Proofs for log positions `i..end`, skipping positions without one.
pub open spec fn approvals_from<A, K>(s: AbsStore<A, K>, i: int, end: int) -> Seq<ApprovalProof<A, K>>
    decreases end - i,
{
    if i >= end || i >= s.log.len() {
        Seq::empty()
    } else {
        let rest = approvals_from(s, i + 1, end);
        match approval_spec(s, s.log[i]) {
            Some(p) => seq![p] + rest,
            None => rest,
        }
    }
}

pub open spec fn page_end<A, K>(s: AbsStore<A, K>, from: u64, limit: u64) -> u64 {
    let l = if limit < MAX_PAGE_SIZE { limit } else { MAX_PAGE_SIZE };
    let e = if from + l > u64::MAX { u64::MAX } else { (from + l) as u64 };
    if e < s.log.len() { e } else { s.log.len() as u64 }
}

pub open spec fn approvals_spec<A, K>(s: AbsStore<A, K>, from: u64, limit: u64) -> Seq<ApprovalProof<A, K>> {
    approvals_from(s, from as int, page_end(s, from, limit) as int)
}

} // verus!

// ---------------------------------------------------------------------------
// Association lists (MemStore's representation)
// ---------------------------------------------------------------------------

verus! {

pub open spec fn distinct_keys<K, V>(s: Seq<(K, V)>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i].0 != s[j].0
}

pub open spec fn has_key<K, V>(s: Seq<(K, V)>, k: K) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i].0 == k
}

pub open spec fn key_index<K, V>(s: Seq<(K, V)>, k: K) -> int {
    choose|i: int| 0 <= i < s.len() && s[i].0 == k
}

pub open spec fn keys<K, V>(s: Seq<(K, V)>) -> Seq<K> {
    s.map_values(|e: (K, V)| e.0)
}

pub open spec fn assoc_map<K, V>(s: Seq<(K, V)>) -> Map<K, V> {
    Map::new(keys(s).to_set(), |k: K| s[key_index(s, k)].1)
}

pub proof fn lemma_assoc_dom<K, V>(s: Seq<(K, V)>, k: K)
    ensures
        assoc_map(s).dom().contains(k) <==> has_key(s, k),
{
    keys(s).to_set_ensures();
    if has_key(s, k) {
        let i = choose|i: int| 0 <= i < s.len() && s[i].0 == k;
        assert(keys(s)[i] == k);
    }
}

pub proof fn lemma_assoc_at<K, V>(s: Seq<(K, V)>, i: int)
    requires
        distinct_keys(s),
        0 <= i < s.len(),
    ensures
        assoc_map(s).dom().contains(s[i].0),
        assoc_map(s)[s[i].0] == s[i].1,
{
    assert(has_key(s, s[i].0));
    lemma_assoc_dom(s, s[i].0);
    let j = key_index(s, s[i].0);
    assert(s[j].0 == s[i].0);
}

pub proof fn lemma_assoc_find<K, V>(s: Seq<(K, V)>, k: K)
    requires
        distinct_keys(s),
    ensures
        forall|i: int| 0 <= i < s.len() && s[i].0 == k ==> opt(assoc_map(s), k) == Some(s[i].1),
        (forall|i: int| 0 <= i < s.len() ==> s[i].0 != k) ==> opt(assoc_map(s), k) is None,
{
    lemma_assoc_dom(s, k);
    assert forall|i: int| 0 <= i < s.len() && s[i].0 == k implies opt(assoc_map(s), k) == Some(s[i].1) by {
        lemma_assoc_at(s, i);
    }
}

pub proof fn lemma_assoc_push<K, V>(s: Seq<(K, V)>, k: K, v: V)
    requires
        distinct_keys(s),
        !assoc_map(s).dom().contains(k),
    ensures
        distinct_keys(s.push((k, v))),
        assoc_map(s.push((k, v))) =~= assoc_map(s).insert(k, v),
{
    let t = s.push((k, v));
    lemma_assoc_dom(s, k);
    assert(distinct_keys(t));
    assert forall|x: K| #[trigger] assoc_map(t).dom().contains(x) <==> assoc_map(s).insert(k, v).dom().contains(x) by {
        lemma_assoc_dom(t, x);
        lemma_assoc_dom(s, x);
        if has_key(t, x) && x != k {
            let i = choose|i: int| 0 <= i < t.len() && t[i].0 == x;
            assert(s[i].0 == x);
        }
        if has_key(s, x) {
            let i = choose|i: int| 0 <= i < s.len() && s[i].0 == x;
            assert(t[i].0 == x);
        }
        if x == k {
            assert(t[s.len() as int].0 == x);
        }
    }
    assert forall|x: K| #[trigger] assoc_map(t).dom().contains(x) implies assoc_map(t)[x] == assoc_map(s).insert(k, v)[x] by {
        lemma_assoc_dom(t, x);
        let i = choose|i: int| 0 <= i < t.len() && t[i].0 == x;
        lemma_assoc_at(t, i);
        if i < s.len() {
            lemma_assoc_at(s, i);
        }
    }
}

pub proof fn lemma_assoc_update<K, V>(s: Seq<(K, V)>, i: int, v: V)
    requires
        distinct_keys(s),
        0 <= i < s.len(),
    ensures
        distinct_keys(s.update(i, (s[i].0, v))),
        assoc_map(s.update(i, (s[i].0, v))) =~= assoc_map(s).insert(s[i].0, v),
{
    let k = s[i].0;
    let t = s.update(i, (k, v));
    assert(distinct_keys(t));
    assert forall|x: K| #[trigger] assoc_map(t).dom().contains(x) <==> assoc_map(s).insert(k, v).dom().contains(x) by {
        lemma_assoc_dom(t, x);
        lemma_assoc_dom(s, x);
        if has_key(t, x) {
            let j = choose|j: int| 0 <= j < t.len() && t[j].0 == x;
            assert(s[j].0 == x);
        }
        if has_key(s, x) {
            let j = choose|j: int| 0 <= j < s.len() && s[j].0 == x;
            assert(t[j].0 == x);
        }
        lemma_assoc_at(s, i);
    }
    assert forall|x: K| #[trigger] assoc_map(t).dom().contains(x) implies assoc_map(t)[x] == assoc_map(s).insert(k, v)[x] by {
        lemma_assoc_dom(t, x);
        let j = choose|j: int| 0 <= j < t.len() && t[j].0 == x;
        lemma_assoc_at(t, j);
        lemma_assoc_at(s, j);
    }
}

pub proof fn lemma_assoc_remove<K, V>(s: Seq<(K, V)>, i: int)
    requires
        distinct_keys(s),
        0 <= i < s.len(),
    ensures
        distinct_keys(s.remove(i)),
        assoc_map(s.remove(i)) =~= assoc_map(s).remove(s[i].0),
{
    let k = s[i].0;
    let t = s.remove(i);
    assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && a != b implies t[a].0 != t[b].0 by {
        let a2 = if a < i { a } else { a + 1 };
        let b2 = if b < i { b } else { b + 1 };
        assert(t[a] == s[a2] && t[b] == s[b2]);
    }
    assert forall|x: K| #[trigger] assoc_map(t).dom().contains(x) <==> assoc_map(s).remove(k).dom().contains(x) by {
        lemma_assoc_dom(t, x);
        lemma_assoc_dom(s, x);
        if has_key(t, x) {
            let j = choose|j: int| 0 <= j < t.len() && t[j].0 == x;
            let j2 = if j < i { j } else { j + 1 };
            assert(t[j] == s[j2]);
        }
        if has_key(s, x) && x != k {
            let j = choose|j: int| 0 <= j < s.len() && s[j].0 == x;
            assert(j != i);
            let j2 = if j < i { j } else { j - 1 };
            assert(t[j2] == s[j]);
        }
    }
    assert forall|x: K| #[trigger] assoc_map(t).dom().contains(x) implies assoc_map(t)[x] == assoc_map(s).remove(k)[x] by {
        lemma_assoc_dom(t, x);
        let j = choose|j: int| 0 <= j < t.len() && t[j].0 == x;
        let j2 = if j < i { j } else { j + 1 };
        assert(t[j] == s[j2]);
        lemma_assoc_at(t, j);
        lemma_assoc_at(s, j2);
    }
}

} // verus!
