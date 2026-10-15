//! Ghost stores (strategy.md sections 6.1 and 6.2, milestone M2).
//!
//! - [`Sparse`]: a line-by-line transliteration of `impl Store for
//!   ApprovalContract` (the deployed store), with each `LookupMap` replaced
//!   by an association list ([`Assoc`]) and the counters kept as plain
//!   `u64` fields, so `+= 1` at `u64::MAX` panics exactly as it does
//!   on-chain under `overflow-checks`. It records every mutating `Store`
//!   call ([`Rec`]) for the store protocol ST-2.
//! - [`Window`]: a log of any `u64` length, of which only one page is
//!   materialised. Reads outside the page and every write panic (RD-3, RD-6).
//! - [`Counting`]: forwards to any store (`MemStore` in `h_count_*`) and
//!   counts reads and writes (ROB-4).
//!
//! Plus what the M2 harnesses need over *any* store: [`Obs`], the abstraction
//! `α` observed through the `Store` interface (ST-1, ST-3); [`expect`], the
//! exact TX result including both counter `LogFull` guards, which a bounded
//! `ArrStore` cannot reach (ROB-2, TR-5); and [`protocol`], the ST-2 call
//! sequence.
//!
//! Upstream: difflabai/trust-framework `contracts/approval/contract/src/lib.rs`
//! Pin:      8635ca7b8b1d64bb226eb0b3b3a35779fcbf461b
//! sha256:   7033fc7acf27d8c678c0f28167ed8cd01ad0c851382d83a661d8f96b83357900
//! Covers:   `impl Store<AccountId, PublicKey> for ApprovalContract` and
//!           `ApprovalContract::new`'s initial values.
//! The `sparse_header_hash` plain test fails when that file's sha256 no
//! longer equals [`CONTRACT_SHA256`]: re-transliterate, then update both.

use crate::ids::{Acct, Key, NK};
use crate::spec::{Op, Out, Req, C};
use approval_core::{
    add_principal, approve, reject, request_action, revoke_key, ActionRequest, Approval,
    ApprovalError as E, ApprovalProof, BlockTime, MemStore, Principal, RegistrationId, Rejection,
    RequestId, Role, Store, MAX_ACTION_LEN, MAX_PAGE_SIZE, MAX_PENDING_PER_KEY,
};
use core::cell::Cell;

/// sha256 of upstream `contract/src/lib.rs` that [`Sparse`] transliterates.
pub const CONTRACT_SHA256: &str =
    "7033fc7acf27d8c678c0f28167ed8cd01ad0c851382d83a661d8f96b83357900";

/// Run `op` through the real core over any store (`spec::apply` is the
/// `ArrStore` instance).
pub fn run<T: Store<Acct, Key>>(s: &mut T, op: &Op) -> Out {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => Out::Add(add_principal(s, caller, key.clone(), acct.clone(), *role)),
        Op::Revoke { caller, key, t } => Out::Revoke(revoke_key(s, caller, key, *t)),
        Op::Req { c, action, t } => Out::Req(request_action(s, c, action.clone(), *t)),
        Op::Appr { c, id, action, t } => Out::Appr(approve(s, c, *id, action, *t)),
        Op::Rej { c, id, t } => Out::Rej(reject(s, c, *id, *t)),
    }
}

// ---------------------------------------------------------------------------
// Assoc: a LookupMap as an association list
// ---------------------------------------------------------------------------

/// Entries an [`Assoc`] holds. Generated stores hold at most 3; one step
/// adds at most one entry per map.
pub const CAP_M: usize = 4;

/// `near_sdk::store::LookupMap<K, V>` as an association list: `get`,
/// `insert` (overwrite or add, returning the old value) and `remove`. Keys
/// are distinct by construction, as in a map. Order carries no meaning.
/// Loops run to the fixed capacity, guarded by the count (as in `ArrStore`).
#[derive(Clone, Debug)]
pub struct Assoc<K: Clone + PartialEq, V: Clone> {
    n: usize,
    e: [Option<(K, V)>; CAP_M],
}

impl<K: Clone + PartialEq, V: Clone> Assoc<K, V> {
    pub fn new() -> Self {
        Assoc {
            n: 0,
            e: [None, None, None, None],
        }
    }
    pub fn len(&self) -> usize {
        self.n
    }
    fn find(&self, k: &K) -> Option<usize> {
        let mut found = None;
        let mut i = 0;
        while i < CAP_M {
            if found.is_none() && i < self.n {
                if let Some((k2, _)) = &self.e[i] {
                    if k2 == k {
                        found = Some(i);
                    }
                }
            }
            i += 1;
        }
        found
    }
    pub fn get(&self, k: &K) -> Option<&V> {
        let i = self.find(k)?;
        self.e[i].as_ref().map(|(_, v)| v)
    }
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        match self.find(&k) {
            Some(i) => self.e[i].replace((k, v)).map(|(_, old)| old),
            None => {
                assert!(self.n < CAP_M, "harness bound: Assoc capacity");
                self.e[self.n] = Some((k, v));
                self.n += 1;
                None
            }
        }
    }
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let i = self.find(k)?;
        let out = self.e[i].take();
        let mut j = 0;
        while j + 1 < CAP_M {
            if j >= i && j + 1 < self.n {
                self.e[j] = self.e[j + 1].take();
            }
            j += 1;
        }
        self.n -= 1;
        out.map(|(_, v)| v)
    }
    /// The `i`-th entry (`i < len()`), for building and probing.
    pub fn entry(&self, i: usize) -> Option<&(K, V)> {
        if i < self.n {
            self.e[i].as_ref()
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Sparse: the contract's store, transliterated
// ---------------------------------------------------------------------------

/// One mutating `Store` call, with its arguments (ST-2).
#[derive(Clone, Debug, PartialEq)]
pub enum Call {
    IncrementRegistrationCount,
    InsertPrincipal(Key, Principal<Acct>),
    RemovePrincipal(Key),
    PushRequest(Req),
    ReplaceRequest(Req),
    PushApproval(RequestId),
    InsertRevocation(RegistrationId, BlockTime),
}

/// Most mutating calls any operation makes (approve: 3), plus one so an
/// extra call is seen rather than dropped.
pub const CAP_CALLS: usize = 4;

/// The recorded mutating calls, in order. `n` counts every call, also past
/// capacity.
#[derive(Clone, Debug, PartialEq)]
pub struct Rec {
    pub n: usize,
    pub c: [Option<Call>; CAP_CALLS],
}

impl Rec {
    pub fn new() -> Self {
        Rec {
            n: 0,
            c: [None, None, None, None],
        }
    }
    pub fn push(&mut self, call: Call) {
        if self.n < CAP_CALLS {
            self.c[self.n] = Some(call);
        }
        self.n += 1;
    }
    pub fn of(calls: &[Call]) -> Self {
        let mut r = Rec::new();
        for c in calls {
            r.push(c.clone());
        }
        r
    }
}

/// `ApprovalContract`'s fields, in declaration order, with `LookupMap`
/// replaced by [`Assoc`], plus the call record.
#[derive(Clone, Debug)]
pub struct Sparse {
    pub owner: Acct,
    pub principals: Assoc<Key, Principal<Acct>>,
    pub requests: Assoc<RequestId, Req>,
    pub request_count: u64,
    /// Approval index -> request id, in approval order.
    pub approval_log: Assoc<u64, RequestId>,
    pub approval_count: u64,
    pub registration_count: u64,
    /// Registration id -> when that registration was revoked.
    pub revocations: Assoc<RegistrationId, BlockTime>,
    /// Ghost: every mutating `Store` call, in order.
    pub calls: Rec,
}

impl Sparse {
    /// `ApprovalContract::new(owner_id)`.
    pub fn new(owner_id: Acct) -> Self {
        Sparse {
            owner: owner_id,
            principals: Assoc::new(),
            requests: Assoc::new(),
            request_count: 0,
            approval_log: Assoc::new(),
            approval_count: 0,
            registration_count: 0,
            revocations: Assoc::new(),
            calls: Rec::new(),
        }
    }

    /// The contract state holding `s`'s contents: request `i` and log slot
    /// `j` under keys `i` and `j`, counters equal to the stored sizes and
    /// `G`. Principals and revocations go through the map's `insert`, so a
    /// raw `ArrStore` with a repeated key becomes some map (the last entry
    /// wins); under `refine_pre` the keys are distinct and nothing is lost.
    pub fn from_arr(s: &crate::store::ArrStore) -> Self {
        let mut t = Sparse::new(s.owner.clone());
        let mut i = 0;
        while i < crate::store::CAP_P {
            if i < s.np() {
                let (k, p) = s.prin(i);
                t.principals.insert(k.clone(), p.clone());
            }
            i += 1;
        }
        let mut i = 0;
        while i < crate::store::CAP_R {
            if i < s.nr() {
                t.requests.insert(i as u64, s.req(i).clone());
            }
            i += 1;
        }
        t.request_count = s.nr() as u64;
        let mut j = 0;
        while j < crate::store::CAP_R {
            if j < s.nl() {
                t.approval_log.insert(j as u64, s.log(j));
            }
            j += 1;
        }
        t.approval_count = s.nl() as u64;
        t.registration_count = s.g();
        let mut j = 0;
        while j < crate::store::CAP_V {
            if j < s.nv() {
                let (g, at) = s.rev(j);
                t.revocations.insert(g, at);
            }
            j += 1;
        }
        t
    }
}

// The body of each method is the contract's, with `self.<map>.get(k)`,
// `.insert(k, v)` and `.remove(k)` on an `Assoc`, plus one `self.calls.push`
// in each mutator.
impl Store<Acct, Key> for Sparse {
    fn owner(&self) -> &Acct {
        &self.owner
    }

    fn principal(&self, key: &Key) -> Option<Principal<Acct>> {
        self.principals.get(key).cloned()
    }

    fn insert_principal(&mut self, key: Key, principal: Principal<Acct>) {
        self.calls
            .push(Call::InsertPrincipal(key.clone(), principal.clone()));
        self.principals.insert(key, principal);
    }

    fn remove_principal(&mut self, key: &Key) -> Option<Principal<Acct>> {
        self.calls.push(Call::RemovePrincipal(key.clone()));
        self.principals.remove(key)
    }

    fn request_count(&self) -> u64 {
        self.request_count
    }

    fn request(&self, id: RequestId) -> Option<Req> {
        self.requests.get(&id).cloned()
    }

    fn push_request(&mut self, request: Req) {
        self.calls.push(Call::PushRequest(request.clone()));
        self.requests.insert(self.request_count, request);
        self.request_count += 1;
    }

    fn replace_request(&mut self, request: Req) {
        self.calls.push(Call::ReplaceRequest(request.clone()));
        self.requests.insert(request.id, request);
    }

    fn approval_count(&self) -> u64 {
        self.approval_count
    }

    fn approved_request_id(&self, approval_index: u64) -> Option<RequestId> {
        self.approval_log.get(&approval_index).copied()
    }

    fn push_approval(&mut self, request_id: RequestId) {
        self.calls.push(Call::PushApproval(request_id));
        self.approval_log.insert(self.approval_count, request_id);
        self.approval_count += 1;
    }

    fn registration_count(&self) -> u64 {
        self.registration_count
    }

    fn increment_registration_count(&mut self) {
        self.calls.push(Call::IncrementRegistrationCount);
        self.registration_count += 1;
    }

    fn revocation(&self, registration_id: RegistrationId) -> Option<BlockTime> {
        self.revocations.get(&registration_id).copied()
    }

    fn insert_revocation(&mut self, registration_id: RegistrationId, revoked_at: BlockTime) {
        self.calls
            .push(Call::InsertRevocation(registration_id, revoked_at));
        self.revocations.insert(registration_id, revoked_at);
    }
}

// ---------------------------------------------------------------------------
// Window: one page of a log of any length
// ---------------------------------------------------------------------------

/// A store whose log has `count` entries (any `u64`), slot `j` holding
/// request id `j + shift` (wrapping), and request `j + shift` approved with
/// `approval_index = j`. Only slots `offset..offset + MAX_PAGE_SIZE` exist:
/// any other read, any read of a principal, counter or revocation, and any
/// write panics. It also checks the order of reads: slots strictly in
/// sequence from `offset`, each followed by at most one `request` of the id
/// that slot returned (RD-3).
pub struct Window {
    pub count: u64,
    pub offset: u64,
    pub shift: u64,
    /// Next slot the core may read.
    pub next: Cell<u64>,
    /// The id the last slot read returned, until it is requested.
    pending: Cell<Option<RequestId>>,
    pub count_reads: Cell<u32>,
    pub slot_reads: Cell<u64>,
    pub request_reads: Cell<u64>,
}

impl Window {
    pub fn new(count: u64, offset: u64, shift: u64) -> Self {
        Window {
            count,
            offset,
            shift,
            next: Cell::new(offset),
            pending: Cell::new(None),
            count_reads: Cell::new(0),
            slot_reads: Cell::new(0),
            request_reads: Cell::new(0),
        }
    }
    /// Store-call count, for ROB-4.
    pub fn reads(&self) -> u64 {
        self.count_reads.get() as u64 + self.slot_reads.get() + self.request_reads.get()
    }
}

impl Store<Acct, Key> for Window {
    fn owner(&self) -> &Acct {
        panic!("Window: owner read")
    }
    fn principal(&self, _key: &Key) -> Option<Principal<Acct>> {
        panic!("Window: principal read")
    }
    fn insert_principal(&mut self, _key: Key, _principal: Principal<Acct>) {
        panic!("Window: write")
    }
    fn remove_principal(&mut self, _key: &Key) -> Option<Principal<Acct>> {
        panic!("Window: write")
    }
    fn request_count(&self) -> u64 {
        panic!("Window: request_count read")
    }
    fn request(&self, id: RequestId) -> Option<Req> {
        assert!(
            self.pending.get() == Some(id),
            "RD-3 request read only for the id a slot returned"
        );
        self.pending.set(None);
        self.request_reads.set(self.request_reads.get() + 1);
        let j = id.wrapping_sub(self.shift);
        Some(ActionRequest {
            id,
            agent_account_id: Acct(1),
            agent_key: Key(1),
            agent_registration_id: 0,
            // Cost fallback 6: content equality (RD-2) is h_read's.
            action: String::new(),
            requested_at: crate::store::T0,
            approval: Some(Approval {
                approval_index: j,
                approver_account_id: Acct(2),
                approver_key: Key(2),
                approver_registration_id: 1,
                approved_at: crate::store::T0,
            }),
            rejection: None,
        })
    }
    fn push_request(&mut self, _request: Req) {
        panic!("Window: write")
    }
    fn replace_request(&mut self, _request: Req) {
        panic!("Window: write")
    }
    fn approval_count(&self) -> u64 {
        self.count_reads.set(self.count_reads.get() + 1);
        self.count
    }
    fn approved_request_id(&self, approval_index: u64) -> Option<RequestId> {
        let j = approval_index;
        assert!(
            j >= self.offset && j - self.offset < MAX_PAGE_SIZE && j < self.count,
            "RD-3 read outside the page"
        );
        assert!(j == self.next.get(), "RD-3 slots read in order");
        // `j < count <= u64::MAX`, so this cannot wrap.
        self.next.set(j + 1);
        self.slot_reads.set(self.slot_reads.get() + 1);
        let id = j.wrapping_add(self.shift);
        self.pending.set(Some(id));
        Some(id)
    }
    fn push_approval(&mut self, _request_id: RequestId) {
        panic!("Window: write")
    }
    fn registration_count(&self) -> u64 {
        panic!("Window: registration_count read")
    }
    fn increment_registration_count(&mut self) {
        panic!("Window: write")
    }
    fn revocation(&self, _registration_id: RegistrationId) -> Option<BlockTime> {
        panic!("Window: revocation read")
    }
    fn insert_revocation(&mut self, _registration_id: RegistrationId, _revoked_at: BlockTime) {
        panic!("Window: write")
    }
}

// ---------------------------------------------------------------------------
// Counting: reads and writes of any store
// ---------------------------------------------------------------------------

/// Forwards every call to `inner` and counts reads (including `owner`) and
/// writes (ROB-4).
pub struct Counting<T> {
    pub inner: T,
    pub reads: Cell<u32>,
    pub writes: u32,
}

impl<T> Counting<T> {
    pub fn new(inner: T) -> Self {
        Counting {
            inner,
            reads: Cell::new(0),
            writes: 0,
        }
    }
    fn r(&self) {
        self.reads.set(self.reads.get() + 1);
    }
}

impl<T: Store<Acct, Key>> Store<Acct, Key> for Counting<T> {
    fn owner(&self) -> &Acct {
        self.r();
        self.inner.owner()
    }
    fn principal(&self, key: &Key) -> Option<Principal<Acct>> {
        self.r();
        self.inner.principal(key)
    }
    fn insert_principal(&mut self, key: Key, principal: Principal<Acct>) {
        self.writes += 1;
        self.inner.insert_principal(key, principal)
    }
    fn remove_principal(&mut self, key: &Key) -> Option<Principal<Acct>> {
        self.writes += 1;
        self.inner.remove_principal(key)
    }
    fn request_count(&self) -> u64 {
        self.r();
        self.inner.request_count()
    }
    fn request(&self, id: RequestId) -> Option<Req> {
        self.r();
        self.inner.request(id)
    }
    fn push_request(&mut self, request: Req) {
        self.writes += 1;
        self.inner.push_request(request)
    }
    fn replace_request(&mut self, request: Req) {
        self.writes += 1;
        self.inner.replace_request(request)
    }
    fn approval_count(&self) -> u64 {
        self.r();
        self.inner.approval_count()
    }
    fn approved_request_id(&self, approval_index: u64) -> Option<RequestId> {
        self.r();
        self.inner.approved_request_id(approval_index)
    }
    fn push_approval(&mut self, request_id: RequestId) {
        self.writes += 1;
        self.inner.push_approval(request_id)
    }
    fn registration_count(&self) -> u64 {
        self.r();
        self.inner.registration_count()
    }
    fn increment_registration_count(&mut self) {
        self.writes += 1;
        self.inner.increment_registration_count()
    }
    fn revocation(&self, registration_id: RegistrationId) -> Option<BlockTime> {
        self.r();
        self.inner.revocation(registration_id)
    }
    fn insert_revocation(&mut self, registration_id: RegistrationId, revoked_at: BlockTime) {
        self.writes += 1;
        self.inner.insert_revocation(registration_id, revoked_at)
    }
}

/// `MemStore` holding `s`'s contents (in order; a raw repeated key stays
/// repeated, which `MemStore` reads as "first match", like `ArrStore`).
pub fn to_mem(s: &crate::store::ArrStore) -> MemStore<Acct, Key> {
    let mut m = MemStore::new(s.owner.clone());
    let mut i = 0;
    while i < crate::store::CAP_P {
        if i < s.np() {
            m.principals.push(s.prin(i).clone());
        }
        i += 1;
    }
    let mut i = 0;
    while i < crate::store::CAP_R {
        if i < s.nr() {
            m.requests.push(s.req(i).clone());
        }
        i += 1;
    }
    let mut j = 0;
    while j < crate::store::CAP_R {
        if j < s.nl() {
            m.approval_log.push(s.log(j));
        }
        j += 1;
    }
    m.registration_count = s.g();
    let mut j = 0;
    while j < crate::store::CAP_V {
        if j < s.nv() {
            m.revocations.push(s.rev(j));
        }
        j += 1;
    }
    m
}

// ---------------------------------------------------------------------------
// Obs: α through the Store interface
// ---------------------------------------------------------------------------

/// Request ids and log slots probed: `0..OR`, one past the largest store
/// the M2 harnesses build after one step (3 + 1).
pub const OR: usize = 5;
/// Registration ids probed: `0..OV`. States for `Obs` draw registration ids
/// from `0..8` (`gen::reg_id` with `raw = false`), and one `add` issues
/// `G ≤ 7`.
pub const OV: usize = 8;

/// Everything the core can observe of a store, read only through `Store`:
/// the owner, `P(k)` for every key, `#R` and `R[i]`, `#L` and `L[j]`, `G`
/// and `V(g)`. Equal `Obs` means the core cannot tell two stores apart
/// within these ids (ST-1, ST-3).
#[derive(Clone, Debug, PartialEq)]
pub struct Obs {
    pub owner: Acct,
    pub p: [Option<Principal<Acct>>; NK as usize],
    pub nr: u64,
    pub r: [Option<ObsReq>; OR],
    pub nl: u64,
    pub l: [Option<RequestId>; OR],
    pub g: u64,
    pub v: [Option<BlockTime>; OV],
}

/// A request with its action as a code of the closed harness alphabet
/// (`spec::act_code`), so snapshots hold no `String` (CBMC cost, as
/// `spec::SnapReq`). `act_code` panics on any other action.
#[derive(Clone, Debug, PartialEq)]
pub struct ObsReq {
    pub id: RequestId,
    pub aa: Acct,
    pub ak: Key,
    pub ag: RegistrationId,
    pub act: u8,
    pub rt: BlockTime,
    pub ap: Option<Approval<Acct, Key>>,
    pub rj: Option<Rejection<Acct, Key>>,
}

pub fn obs_req(r: &Req) -> ObsReq {
    ObsReq {
        id: r.id,
        aa: r.agent_account_id.clone(),
        ak: r.agent_key.clone(),
        ag: r.agent_registration_id,
        act: crate::spec::act_code(&r.action),
        rt: r.requested_at,
        ap: r.approval.clone(),
        rj: r.rejection.clone(),
    }
}

pub fn obs<T: Store<Acct, Key>>(s: &T) -> Obs {
    let mut o = Obs {
        owner: s.owner().clone(),
        p: [None, None, None, None],
        nr: s.request_count(),
        r: [None, None, None, None, None],
        nl: s.approval_count(),
        l: [None; OR],
        g: s.registration_count(),
        v: [None; OV],
    };
    let mut k = 0;
    while k < NK {
        o.p[k as usize] = s.principal(&Key(k));
        k += 1;
    }
    let mut i = 0;
    while i < OR {
        o.r[i] = s.request(i as u64).as_ref().map(obs_req);
        o.l[i] = s.approved_request_id(i as u64);
        i += 1;
    }
    let mut g = 0;
    while g < OV {
        o.v[g] = s.revocation(g as u64);
        g += 1;
    }
    o
}

impl Obs {
    /// ST-1 sequence laws: `request(i)` exists exactly for `i < #R`, and
    /// `approved_request_id(j)` exactly for `j < #L` (within the probes).
    pub fn sequences(&self) -> bool {
        let mut ok = true;
        let mut i = 0;
        while i < OR {
            ok &= self.r[i].is_some() == ((i as u64) < self.nr);
            ok &= self.l[i].is_some() == ((i as u64) < self.nl);
            i += 1;
        }
        ok
    }
}

// ---------------------------------------------------------------------------
// expect: TX-1..7 over any store, with both counter LogFull guards
// ---------------------------------------------------------------------------

/// TX-3 over any store: the first failing authentication guard.
fn auth<T: Store<Acct, Key>>(s: &T, c: &C, role: Role) -> Result<Principal<Acct>, E> {
    if c.predecessor != c.signer {
        return Err(E::IndirectCall);
    }
    let p = s.principal(&c.signer_key).ok_or(E::UnknownKey)?;
    if p.role != role {
        return Err(E::WrongRole);
    }
    if p.account_id != c.signer {
        return Err(E::KeyAccountMismatch);
    }
    Ok(p)
}

/// `Decidable(s,i)` over any store: the request and its live agent
/// registration, or the first failing guard.
fn decidable<T: Store<Acct, Key>>(s: &T, id: u64) -> Result<(Req, Principal<Acct>), E> {
    let r = s.request(id).ok_or(E::RequestNotFound)?;
    if r.approval.is_some() {
        return Err(E::AlreadyApproved);
    }
    if r.rejection.is_some() {
        return Err(E::AlreadyRejected);
    }
    match s.principal(&r.agent_key) {
        Some(p)
            if p.role == Role::Agent
                && p.account_id == r.agent_account_id
                && p.active_from <= r.id =>
        {
            Ok((r, p))
        }
        _ => Err(E::AgentRevoked),
    }
}

/// The exact result of `op` on `s` (section 5.1), first failing guard wins,
/// over any store and any counter values: this is `spec::expected` plus
/// `request_action`'s `LogFull` at `#R = MAXU` and `approve`'s at
/// `#L = MAXU`.
// PROP: TX-1 TX-2 TX-4 TX-5 TX-7 ROB-2
pub fn expect<T: Store<Acct, Key>>(s: &T, op: &Op) -> Out {
    match op {
        Op::Add {
            caller,
            key,
            acct,
            role,
        } => Out::Add(if caller != s.owner() {
            Err(E::NotOwner)
        } else if s.principal(key).is_some() {
            Err(E::KeyAlreadyRegistered)
        } else if s.registration_count() == u64::MAX {
            Err(E::LogFull)
        } else {
            Ok(Principal {
                account_id: acct.clone(),
                role: *role,
                registration_id: s.registration_count(),
                active_from: s.request_count(),
                pending: 0,
            })
        }),
        Op::Revoke { caller, key, .. } => Out::Revoke(if caller != s.owner() {
            Err(E::NotOwner)
        } else {
            s.principal(key).ok_or(E::KeyNotRegistered)
        }),
        Op::Req { c, action, t } => Out::Req(match auth(s, c, Role::Agent) {
            Err(e) => Err(e),
            Ok(_) if action.is_empty() => Err(E::EmptyAction),
            Ok(_) if action.len() > MAX_ACTION_LEN => Err(E::ActionTooLong),
            Ok(p) if p.pending >= MAX_PENDING_PER_KEY => Err(E::TooManyPending),
            Ok(_) if s.request_count() == u64::MAX => Err(E::LogFull),
            Ok(p) => Ok(ActionRequest {
                id: s.request_count(),
                agent_account_id: c.signer.clone(),
                agent_key: c.signer_key.clone(),
                agent_registration_id: p.registration_id,
                action: action.clone(),
                requested_at: *t,
                approval: None,
                rejection: None,
            }),
        }),
        Op::Appr { c, id, action, t } => Out::Appr(match auth(s, c, Role::Approver) {
            Err(e) => Err(e),
            Ok(b) => match decidable(s, *id) {
                Err(e) => Err(e),
                Ok((r, _)) if r.action != *action => Err(E::ActionMismatch),
                Ok((r, _)) if c.signer == r.agent_account_id => Err(E::SelfApproval),
                Ok(_) if s.approval_count() == u64::MAX => Err(E::LogFull),
                Ok((r, _)) => Ok(ApprovalProof {
                    approval_index: s.approval_count(),
                    request_id: r.id,
                    action: r.action.clone(),
                    agent_account_id: r.agent_account_id.clone(),
                    agent_key: r.agent_key.clone(),
                    agent_registration_id: r.agent_registration_id,
                    requested_at: r.requested_at,
                    approver_account_id: c.signer.clone(),
                    approver_key: c.signer_key.clone(),
                    approver_registration_id: b.registration_id,
                    approved_at: *t,
                }),
            },
        }),
        Op::Rej { c, id, t } => Out::Rej(match auth(s, c, Role::Approver) {
            Err(e) => Err(e),
            Ok(b) => match decidable(s, *id) {
                Err(e) => Err(e),
                Ok((r, _)) if c.signer == r.agent_account_id => Err(E::SelfApproval),
                Ok((mut r, _)) => {
                    r.rejection = Some(Rejection {
                        approver_account_id: c.signer.clone(),
                        approver_key: c.signer_key.clone(),
                        approver_registration_id: b.registration_id,
                        rejected_at: *t,
                    });
                    Ok(r)
                }
            },
        }),
    }
}

/// ST-2: the mutating `Store` calls `op` must make on `s`, given its
/// expected result `exp` (from [`expect`] on the same pre-state).
// PROP: ST-2
pub fn protocol<T: Store<Acct, Key>>(s: &T, op: &Op, exp: &Out) -> Rec {
    match (op, exp) {
        (Op::Add { key, .. }, Out::Add(Ok(p))) => Rec::of(&[
            Call::IncrementRegistrationCount,
            Call::InsertPrincipal(key.clone(), p.clone()),
        ]),
        // F-6: `remove_principal` runs before the absence is known.
        (Op::Revoke { key, .. }, Out::Revoke(Err(E::KeyNotRegistered))) => {
            Rec::of(&[Call::RemovePrincipal(key.clone())])
        }
        (Op::Revoke { key, t, .. }, Out::Revoke(Ok(p))) => Rec::of(&[
            Call::RemovePrincipal(key.clone()),
            Call::InsertRevocation(p.registration_id, *t),
        ]),
        (Op::Req { c, .. }, Out::Req(Ok(r))) => {
            let mut p = s.principal(&c.signer_key).unwrap();
            p.pending += 1;
            Rec::of(&[
                Call::InsertPrincipal(c.signer_key.clone(), p),
                Call::PushRequest(r.clone()),
            ])
        }
        (Op::Appr { c, id, t, .. }, Out::Appr(Ok(pi))) => {
            let (mut r, mut agent) = decidable(s, *id).unwrap();
            agent.pending = agent.pending.saturating_sub(1);
            r.approval = Some(Approval {
                approval_index: s.approval_count(),
                approver_account_id: c.signer.clone(),
                approver_key: c.signer_key.clone(),
                approver_registration_id: pi.approver_registration_id,
                approved_at: *t,
            });
            Rec::of(&[
                Call::InsertPrincipal(r.agent_key.clone(), agent),
                Call::ReplaceRequest(r),
                Call::PushApproval(*id),
            ])
        }
        (Op::Rej { id, .. }, Out::Rej(Ok(r))) => {
            let (_, mut agent) = decidable(s, *id).unwrap();
            agent.pending = agent.pending.saturating_sub(1);
            Rec::of(&[
                Call::InsertPrincipal(r.agent_key.clone(), agent),
                Call::ReplaceRequest(r.clone()),
            ])
        }
        _ => Rec::new(),
    }
}
