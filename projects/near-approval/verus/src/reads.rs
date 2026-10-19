//! Read properties (strategy.md §5.5) over the read specs the core refines
//! (`approval`, `approvals`, `request_status`, `proof_revocations`), at
//! every store size.

use crate::*;
use vstd::prelude::*;

verus! {

/// The proof of the request at log slot `j`.
pub open spec fn page_entry<A, K>(s: AbsStore<A, K>, j: int) -> ApprovalProof<A, K> {
    let r = s.requests[s.log[j] as int];
    proof_for_spec(r, r.approval->Some_0)
}

/// RD-1: `approval(s, i)` is `Some(proof(R[i]))` exactly when `R[i]` is
/// approved, and `None` for pending, rejected, void or unknown ids.
/// PROP: RD-1
pub proof fn lemma_rd1<A, K>(s: AbsStore<A, K>, id: RequestId)
    ensures
        id < s.requests.len() && s.requests[id as int].approval is Some
            ==> approval_spec(s, id) == Some(proof_for_spec(s.requests[id as int], s.requests[id as int].approval->Some_0)),
        !(id < s.requests.len() && s.requests[id as int].approval is Some) ==> approval_spec(s, id) is None,
{
}

/// Under the invariant every log slot has a proof, so a page drops nothing.
pub proof fn lemma_approvals_from<A, K>(s: AbsStore<A, K>, i: int, end: int)
    requires
        full_inv(s),
        0 <= i <= end <= s.log.len(),
    ensures
        approvals_from(s, i, end) =~= Seq::new((end - i) as nat, |n: int| page_entry(s, i + n)),
    decreases end - i,
{
    if i < end {
        lemma_approvals_from(s, i + 1, end);
        assert(inv_log(s, i));
    }
}

/// RD-2 and RD-5: a page is exactly the proofs of log slots
/// `from .. min(from saturating_add min(limit, 100), #L)`, in order, with no
/// drops; entry `n` carries approval index `from + n`, and the per-request
/// view returns the same proof. PROP: RD-2 RD-5
pub proof fn lemma_rd2<A, K>(s: AbsStore<A, K>, from: u64, limit: u64)
    requires
        full_inv(s),
    ensures
        ({
            let e = page_end(s, from, limit);
            let page = approvals_spec(s, from, limit);
            &&& page =~= Seq::new(if from < e { (e - from) as nat } else { 0 }, |n: int| page_entry(s, from + n))
            &&& forall|n: int| 0 <= n < page.len() ==> {
                &&& (#[trigger] page[n]).approval_index == from + n
                &&& page[n].request_id == s.log[from + n]
                &&& approval_spec(s, page[n].request_id) == Some(page[n])
            }
        }),
{
    let e = page_end(s, from, limit);
    if from < e {
        lemma_approvals_from(s, from as int, e as int);
        assert forall|n: int| 0 <= n < e - from implies {
            let p = #[trigger] page_entry(s, from + n);
            &&& p.approval_index == from + n
            &&& p.request_id == s.log[from + n]
            &&& approval_spec(s, p.request_id) == Some(p)
        } by {
            assert(inv_log(s, from + n));
            assert(s.requests[s.log[from + n] as int].id == s.log[from + n]);
        }
    }
}

/// The client loop of RD-4: page from `from` until an empty page (or until
/// `from` reaches the log length), concatenating the pages.
pub open spec fn client<A, K>(s: AbsStore<A, K>, from: int, limit: u64) -> Seq<ApprovalProof<A, K>>
    decreases if from < s.log.len() { s.log.len() - from } else { 0 },
{
    if from < 0 || from >= s.log.len() {
        Seq::empty()
    } else {
        let p = approvals_spec(s, from as u64, limit);
        if p.len() == 0 {
            Seq::empty()
        } else {
            p + client(s, from + p.len(), limit)
        }
    }
}

/// RD-4: with any `limit >= 1`, the client loop enumerates the log exactly
/// once, in order. PROP: RD-4
pub proof fn lemma_rd4<A, K>(s: AbsStore<A, K>, from: int, limit: u64)
    requires
        full_inv(s),
        0 <= from <= s.log.len(),
        limit >= 1,
    ensures
        client(s, from, limit) =~= Seq::new((s.log.len() - from) as nat, |n: int| page_entry(s, from + n)),
    decreases s.log.len() - from,
{
    if from < s.log.len() {
        let e = page_end(s, from as u64, limit);
        lemma_rd2(s, from as u64, limit);
        assert(from < e);
        lemma_rd4(s, e as int, limit);
    }
}

/// RD-7: status is Approved, Rejected, Pending (agent registration still
/// live) or Void; unknown ids have none (the code's `request_status`
/// returns `None` for them). PROP: RD-7
pub proof fn lemma_rd7<A, K>(s: AbsStore<A, K>, i: int)
    requires
        full_inv(s),
        0 <= i < s.requests.len(),
    ensures
        ({
            let r = s.requests[i];
            let st = status_spec(s, r);
            &&& (st == RequestStatus::Approved) <==> r.approval is Some
            &&& (st == RequestStatus::Rejected) <==> r.rejection is Some
            &&& (st == RequestStatus::Pending) <==> (undecided(r) && live_spec(s, r) is Some)
            &&& (st == RequestStatus::Void) <==> (undecided(r) && live_spec(s, r) is None)
        }),
{
    assert(inv_req(s, i));
}

/// RD-8: `proof_revocations` reports `V(agent registration)` and
/// `V(approver registration)`; under the invariant each is `None` exactly
/// when that registration is still its key's current one. PROP: RD-8
pub proof fn lemma_rd8<A, K>(s: AbsStore<A, K>, id: RequestId)
    requires
        full_inv(s),
        approval_spec(s, id) is Some,
    ensures
        ({
            let p = approval_spec(s, id)->Some_0;
            &&& (opt(s.revocations, p.agent_registration_id) is None) <==> (
                s.principals.dom().contains(p.agent_key)
                && s.principals[p.agent_key].registration_id == p.agent_registration_id)
            &&& (opt(s.revocations, p.approver_registration_id) is None) <==> (
                s.principals.dom().contains(p.approver_key)
                && s.principals[p.approver_key].registration_id == p.approver_registration_id)
        }),
{
    let i = id as int;
    let p = approval_spec(s, id)->Some_0;
    assert(inv_req(s, i));
    if !s.revocations.dom().contains(p.agent_registration_id) {
        assert(live_reg(s, p.agent_registration_id));
        let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == p.agent_registration_id;
        assert(inv_kr(s, k0, i));
    }
    if !s.revocations.dom().contains(p.approver_registration_id) {
        assert(live_reg(s, p.approver_registration_id));
        let k0 = choose|k: K| #[trigger] s.principals.dom().contains(k) && s.principals[k].registration_id == p.approver_registration_id;
        assert(inv_kr(s, k0, i));
    }
    if s.principals.dom().contains(p.agent_key) {
        assert(inv_key(s, p.agent_key));
    }
}

} // verus!
