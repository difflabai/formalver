//! Non-vacuity (TR-5 for the twin): the core's preconditions are
//! satisfiable and its specs are not contradictory. A concrete trace on a
//! `MemStore<u64, u64>` (u64 has vstd's `==`/`clone` specs) reaches an
//! approved request, and the approval log page returns its proof. If the
//! trusted specs were inconsistent this would still verify, but so would
//! every spec mutant, which run-verus.sh checks don't.

use crate::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub fn witness_trace() {
    let mut s = MemStore::<u64, u64>::new(0);
    proof {
        assert(s.view().principals =~= Map::empty());
        assert(s.view().revocations =~= Map::empty());
        lemma_init_inv::<u64, u64>(0);
    }
    let t = BlockTime { height: 1, timestamp_ns: 1 };
    let agent = Caller { predecessor: 10u64, signer: 10u64, signer_key: 1u64 };
    let approver = Caller { predecessor: 20u64, signer: 20u64, signer_key: 2u64 };

    let ghost s0 = s.view();
    let r = add_principal(&mut s, &0, 1, 10, Role::Agent);
    assert(r is Ok);
    proof { lemma_add_inv(s0, 0, 1, 10, Role::Agent, s.view()); }

    let ghost s1 = s.view();
    let r = add_principal(&mut s, &0, 2, 20, Role::Approver);
    assert(r is Ok);
    proof { lemma_add_inv(s1, 0, 2, 20, Role::Approver, s.view()); }

    let x = "x";
    proof {
        reveal_strlit("x");
    }
    let action = x.to_owned();
    proof {
        assert(action@.len() == 1);
        assert(action@ =~= seq!['x']);
        assert(byte_len(seq!['x']) == 1) by (compute);
    }
    let ghost s2 = s.view();
    let r = request_action(&mut s, &agent, action, t);
    assert(r is Ok);
    proof { lemma_request_inv(s2, agent, action, t, s.view()); }

    let ghost s3 = s.view();
    let r = approve(&mut s, &approver, 0, x, t);
    assert(r is Ok);
    proof { lemma_approve_inv(s3, approver, 0, x@, t, s.view()); }

    let page = approvals(&s, 0, 10);
    proof {
        assert(s.view().log.len() == 1 && s.view().log[0] == 0);
        assert(s.view().requests[0].approval is Some);
        reveal_with_fuel(approvals_from, 2);
    }
    assert(page@.len() == 1);
}

} // verus!
