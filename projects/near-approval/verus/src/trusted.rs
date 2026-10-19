//! Everything the twin's proofs take on trust (strategy.md §7 hygiene gate).
//! Each item maps to an entry in `../TRUSTED.toml`.
//!
//! The data types stay outside `verus!` exactly as upstream writes them, with
//! their `#[derive]`s, so the derived impls are not Verus-checked. This file
//! gives Verus their shape (`external_type_specification`) and states what
//! the derives do.
#![allow(unsafe_code)]

use crate::*;
use vstd::prelude::*;
use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};
use vstd::std_specs::iter::IteratorSpec;

verus! {

// ---------------------------------------------------------------------------
// ASM-IDTYPE: the identity types behave like values. On-chain `A` is
// `near_sdk::AccountId` (a `String` newtype) and `K` is
// `near_sdk::PublicKey` (curve byte + `Vec<u8>`); both derive `PartialEq`
// and `Clone`. These are hypotheses (`requires`) of the core functions, so
// they are discharged per instantiation, not assumed here.
// ---------------------------------------------------------------------------

/// `==` is structural equality.
pub open spec fn eq_laws<T: PartialEq>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| (x == y) <==> x.eq_spec(&y)
}

/// `clone` returns an equal value.
pub open spec fn clone_laws<T: Clone>() -> bool {
    forall|x: T, y: T| call_ensures(T::clone, (&x,), y) ==> x == y
}

pub open spec fn ident<T: PartialEq + Clone>() -> bool {
    eq_laws::<T>() && clone_laws::<T>()
}

// ---------------------------------------------------------------------------
// ASM-DERIVE: the data types' shapes, and what `#[derive(Clone, PartialEq)]`
// generates (field-wise clone, structural equality).
// ---------------------------------------------------------------------------

#[verifier::external_type_specification]
pub struct ExRole(Role);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
pub struct ExPrincipal<A>(Principal<A>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct ExCaller<A, K>(Caller<A, K>);

#[verifier::external_type_specification]
pub struct ExBlockTime(BlockTime);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct ExApproval<A, K>(Approval<A, K>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct ExRejection<A, K>(Rejection<A, K>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct ExActionRequest<A, K>(ActionRequest<A, K>);

#[verifier::external_type_specification]
pub struct ExRequestStatus(RequestStatus);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct ExApprovalProof<A, K>(ApprovalProof<A, K>);

#[verifier::external_type_specification]
pub struct ExProofRevocations(ProofRevocations);

#[verifier::external_type_specification]
pub struct ExApprovalError(ApprovalError);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
pub struct ExMemStore<A, K>(MemStore<A, K>);

impl PartialEqSpecImpl for Role {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Role) -> bool {
        *self == *other
    }
}

pub assume_specification<A: Clone>[ <Principal<A> as Clone>::clone ](p: &Principal<A>) -> (r: Principal<A>)
    ensures
        clone_laws::<A>() ==> r == *p,
;

pub assume_specification<A: Clone, K: Clone>[ <ActionRequest<A, K> as Clone>::clone ](
    r: &ActionRequest<A, K>,
) -> (c: ActionRequest<A, K>)
    ensures
        clone_laws::<A>() && clone_laws::<K>() ==> c == *r,
;

// ---------------------------------------------------------------------------
// ASM-STRLEN: `String::len` is the UTF-8 byte length of the characters.
// ---------------------------------------------------------------------------

pub assume_specification[ String::len ](s: &String) -> (r: usize)
    ensures
        r as nat == byte_len(s@),
;

// ---------------------------------------------------------------------------
// ASM-TOOLS (std spec missing from vstd): `String != &str` compares
// characters; `Option::filter` keeps the value iff the predicate holds.
// ---------------------------------------------------------------------------

pub assume_specification<'a>[ <String as PartialEq<&'a str>>::ne ](s: &String, o: &&str) -> (r: bool)
    ensures
        r == (s@ != (*o)@),
;

pub assume_specification<T, P: FnOnce(&T) -> bool>[ Option::<T>::filter ](o: Option<T>, p: P) -> (r: Option<T>)
    requires
        o is Some ==> call_requires(p, (&o->0,)),
    ensures
        match o {
            None => r is None,
            Some(x) => exists|b: bool| call_ensures(p, (&x,), b) && r == (if b { Some(x) } else { None }),
        },
;

// MemStore only (not deployed): `Option<&T>::copied` and slice `position`.

pub assume_specification<'a, T: Copy>[ Option::<&'a T>::copied ](o: Option<&'a T>) -> (r: Option<T>)
    ensures
        r == (match o {
            Some(x) => Some(*x),
            None => None,
        }),
;

pub assume_specification<'a, T, P: FnMut(&'a T) -> bool>[ <core::slice::Iter<'a, T> as Iterator>::position ](
    it: &mut core::slice::Iter<'a, T>,
    p: P,
) -> (r: Option<usize>)
    where
        core::slice::Iter<'a, T>: Sized,
    requires
        forall|k: int| 0 <= k < old(it).remaining().len() ==> call_requires(p, (old(it).remaining()[k],)),
    ensures
        match r {
            Some(i) => {
                &&& i < old(it).remaining().len()
                &&& call_ensures(p, (old(it).remaining()[i as int],), true)
                &&& forall|j: int| 0 <= j < i ==> call_ensures(p, (old(it).remaining()[j],), false)
            },
            None => forall|j: int| 0 <= j < old(it).remaining().len() ==> call_ensures(p, (old(it).remaining()[j],), false),
        },
;

} // verus!
