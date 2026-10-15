//! M2 harness bodies over the ghost stores (strategy.md section 6.2),
//! generic over [`Src`] like `checks.rs`: the proof under Kani
//! (`proofs.rs`), a random test in plain mode (`plain.rs`).
//!
//! - `h_page_arith`: `approvals` over a [`Window`] (RD-3, RD-6, ROB-4).
//! - `h_proto_*`: one operation on a raw recording [`Sparse`] with free
//!   counters (ST-2, ROB-2, TR-5).
//! - `h_count_*`: one operation on [`Counting`] over `MemStore` (ROB-4).
//! - `h_refine_*`: one operation on the same state in `ArrStore`, `Sparse`
//!   and `MemStore` (ST-3, and ST-2 from states with counters equal to size).
//! - `h_store_laws_*`: one `Store` mutator on a small store (ST-1, INV-0).
//! - `h_action_len`: the byte-length boundaries of `request_action` (ROB-3).
//! - `client_enum` (plain mode only): the RD-4 client loop.

use crate::checks::{LONG, PART_POST, PART_REG, PART_TX};
use crate::gen;
use crate::ghost::*;
use crate::ids::{Acct, Key, NA, OWNER};
use crate::spec::{apply, inv0, inv1, inv8, v_get, Ghost, Op, Out, Req, S};
use crate::src::{assume, Src};
use crate::store::{ArrStore, CAP_P, CAP_V};
use approval_core::{
    approvals, ActionRequest, ApprovalError as E, BlockTime, Caller, MemStore, Principal, Role,
    Store, MAX_ACTION_LEN, MAX_PAGE_SIZE, MAX_PENDING_PER_KEY,
};

// ---------------------------------------------------------------------------
// h_page_arith
// ---------------------------------------------------------------------------

/// `h_page_arith`: requests approved, `limit ≤ PAGE_SMALL`.
pub const PAGE_FULL: u8 = 1;
/// `h_page_arith_empty`: requests absent, any `limit`.
pub const PAGE_EMPTY: u8 = 2;

/// `approvals(from, limit)` over a log of any length `count`: the core reads
/// `approval_count` once, then exactly slots `from..e` in order, each
/// followed by the request it names, and nothing else; it writes nothing and
/// cannot overflow. `e = min(from ⊕ min(limit, PG), count)`. Under Kani
/// `src.part()` picks one `Window` instance (see there); plain mode runs
/// both, with any limit.
pub fn page_arith(src: &mut impl Src) {
    let part = src.part();
    if part & PAGE_FULL != 0 && (part & PAGE_EMPTY == 0 || src.bool()) {
        // Under Kani the limit is at most PAGE_SMALL; plain mode takes any.
        let small = part & PAGE_EMPTY == 0;
        page_case::<true>(src, small);
    } else {
        page_case::<false>(src, false);
    }
}

/// `from` values for the 100-slot instance under Kani: the bottom, the
/// middle, and every distance to `u64::MAX` that changes the page (more than
/// a page away, exactly a page, inside a page, the last slot, past it).
pub const PAGE_FROMS: [u64; 10] = [
    0,
    1,
    1 << 32,
    1 << 63,
    u64::MAX - 200,
    u64::MAX - 100,
    u64::MAX - 99,
    u64::MAX - 50,
    u64::MAX - 1,
    u64::MAX,
];

fn page_case<const APPROVED: bool>(src: &mut impl Src, small: bool) {
    let mut from = src.u64();
    // Under Kani with any limit (h_page_arith_empty), `from` is one of
    // PAGE_FROMS: with `from` free, relating 100 unrolled increments of the
    // range to `from + min(l, PG)` was a SAT query that did not finish in
    // 40 minutes. `h_page_arith` keeps `from` free (limit <= PAGE_SMALL).
    #[cfg(kani)]
    if !small {
        from = PAGE_FROMS[src.below(PAGE_FROMS.len() as u8) as usize];
    }
    let limit = if small {
        src.below(PAGE_SMALL as u8 + 1) as u64
    } else {
        src.u64()
    };
    let mut count = src.u64();
    let shift = src.u64();
    // Plain mode: steer toward the top of the u64 range, where saturation
    // matters. Under Kani `hint` is false and every value is free.
    if src.hint(30) {
        from = u64::MAX - src.below(4) as u64 - 100 * src.below(2) as u64;
        count = u64::MAX - src.below(2) as u64;
    }
    let e = from.saturating_add(limit.min(MAX_PAGE_SIZE)).min(count);
    let n = e.saturating_sub(from);
    let w = Window::<APPROVED>::new(count, from, shift, e);
    // PROP: RD-3 RD-6 (`approvals` takes `&S`; every Window write panics)
    // Inside each read the Window asserts: slot `j` is the next one from
    // `f` and `j < e`; its request is read before the next slot; nothing
    // else is read or written.
    let page = approvals(&w, from, limit);
    // PROP: RD-3
    assert!(w.count_reads.get() == 1, "RD-3 approval_count read once");
    assert!(w.settled(), "RD-3 reads one request per slot");
    // PROP: ROB-4
    // The slots read are f, f + 1, ... (each checked against `next`), all
    // below e, so there are at most e - f <= min(l, PG) of them, and the
    // reads are 1 + 2 * slots <= 2 min(l, PG) + 1. The empty-page instance
    // relies on that argument: asserting the count itself (or completeness)
    // over 100 unrolled iterations was a SAT query that did not finish in
    // 40 minutes. The approved instance asserts both.
    if APPROVED {
        assert!(w.slots() == n, "RD-3 reads every slot f..e");
        assert!(page.len() as u64 == n, "RD-3 page length e - f");
        assert!(
            w.slots() <= limit.min(MAX_PAGE_SIZE),
            "ROB-4 approvals reads <= 2 min(l, PG) + 1"
        );
        let mut k = 0;
        while k < page.len() {
            let j = from + k as u64;
            assert!(
                page[k].approval_index == j && page[k].request_id == j.wrapping_add(shift),
                "RD-3 page entry k is slot f + k"
            );
            k += 1;
        }
    } else {
        assert!(page.is_empty(), "RD-3 absent requests are dropped");
    }
    // Plain mode checks completeness for empty pages too.
    #[cfg(not(kani))]
    assert!(w.slots() == n, "RD-3 reads every slot f..e");
    cover!(
        !page.is_empty() && count == u64::MAX,
        "page: non-empty page at count = MAXU"
    );
    cover!(
        !page.is_empty() && from.checked_add(limit.min(MAX_PAGE_SIZE)).is_none(),
        "page: non-empty page where f + l overflows"
    );
    cover!(n == MAX_PAGE_SIZE, "page: a full page of slots read");
}

// ---------------------------------------------------------------------------
// h_proto_*: raw recording Sparse, counters free
// ---------------------------------------------------------------------------

/// A counter at least `n`: any `u64 ≥ n`.
fn at_least(src: &mut impl Src, n: u64) -> u64 {
    let v = src.u64();
    if v < n {
        n
    } else {
        v
    }
}

/// A raw `Sparse` state (no `Inv`) with the contents of the raw `ArrStore`
/// `a` and `#R`, `#L` any `u64` at least the stored sizes (`G` is already
/// free in `a`).
pub fn sparse_raw(src: &mut impl Src, a: &S) -> Sparse {
    let mut t = Sparse::from_arr(a);
    t.request_count = at_least(src, t.request_count);
    t.approval_count = at_least(src, t.approval_count);
    // Plain mode: the counters at their maximum often enough to reach both
    // LogFull guards. Under Kani `hint` is false and the counters are free.
    if src.hint(20) {
        t.request_count = u64::MAX;
    }
    if src.hint(20) {
        t.approval_count = u64::MAX;
    }
    t
}

/// Exact result (with the `LogFull` guards) and exact mutating calls.
// PROP: ST-2 ROB-1 ROB-2 TX-0
fn check_proto(s: &mut Sparse, op: &Op) -> Out {
    let exp = expect(s, op);
    let calls = protocol(s, op, &exp);
    // No panic here: in particular no `+= 1` overflow in the transliterated
    // counters (ROB-2).
    let out = run(s, op);
    assert!(out == exp, "TX exact result (Sparse, any counters)");
    assert!(s.calls == calls, "ST-2 store protocol");
    if out.err() == Some(E::LogFull) {
        assert!(s.calls.n == 0, "ROB-2 LogFull: no writes");
    }
    out
}

pub fn proto_add(src: &mut impl Src) {
    let a = gen::state(src, true);
    let op = gen::op_add(src, &a);
    let mut s = sparse_raw(src, &a);
    let g = s.registration_count;
    let out = check_proto(&mut s, &op);
    if out.is_ok() {
        assert!(g < u64::MAX, "ST-2 add: G < MAXU");
    }
    cover!(out.is_ok(), "proto add: Ok");
    cover!(out.err() == Some(E::NotOwner), "proto add: NotOwner");
    cover!(
        out.err() == Some(E::KeyAlreadyRegistered),
        "proto add: KeyAlreadyRegistered"
    );
    cover!(out.err() == Some(E::LogFull), "proto add: LogFull");
}

pub fn proto_revoke(src: &mut impl Src) {
    let a = gen::state(src, true);
    let op = gen::op_revoke(src, &a, &Ghost::init());
    let mut s = sparse_raw(src, &a);
    let out = check_proto(&mut s, &op);
    if let Out::Revoke(Ok(p)) = &out {
        // F-16: the write-once law of `insert_revocation` holds only if this
        // registration was not revoked before, which raw states can break;
        // record whether it held (INV-11 rules it out in `Inv` states).
        cover!(
            v_get(&a, p.registration_id).is_none(),
            "proto revoke: Ok with a fresh revocation id"
        );
    }
    cover!(out.is_ok(), "proto revoke: Ok");
    cover!(out.err() == Some(E::NotOwner), "proto revoke: NotOwner");
    cover!(
        out.err() == Some(E::KeyNotRegistered),
        "proto revoke: KeyNotRegistered"
    );
}

pub fn proto_request(src: &mut impl Src) {
    let a = gen::state(src, true);
    let op = gen::op_req(src, &a, &Ghost::init());
    let mut s = sparse_raw(src, &a);
    let n_r = s.request_count;
    let out = check_proto(&mut s, &op);
    // PROP: ROB-2 TR-5
    if out.err() == Some(E::LogFull) {
        assert!(n_r == u64::MAX, "TR-5 request LogFull only at #R = MAXU");
    }
    if out.is_ok() {
        assert!(n_r < u64::MAX, "ST-2 request: r.id = #R < MAXU");
    }
    cover!(out.is_ok(), "proto request: Ok");
    cover!(
        out.err() == Some(E::LogFull),
        "proto request: LogFull at #R = MAXU"
    );
}

pub fn proto_approve(src: &mut impl Src) {
    let a = gen::state(src, true);
    let op = gen::op_appr(src, &a, &Ghost::init());
    let mut s = sparse_raw(src, &a);
    let (n_r, n_l) = (s.request_count, s.approval_count);
    let out = check_proto(&mut s, &op);
    let Op::Appr { id, .. } = &op else {
        unreachable!()
    };
    // PROP: ROB-2
    if out.err() == Some(E::LogFull) {
        assert!(n_l == u64::MAX, "ROB-2 approve LogFull only at #L = MAXU");
    }
    if out.is_ok() {
        assert!(
            *id < n_r && n_l < u64::MAX,
            "ST-2 approve: i < #R and #L < MAXU"
        );
    }
    cover!(out.is_ok(), "proto approve: Ok");
    // LEM-3: unreachable from Inv states; here from a raw one.
    cover!(
        out.err() == Some(E::LogFull),
        "proto approve: LogFull at #L = MAXU"
    );
}

pub fn proto_reject(src: &mut impl Src) {
    let a = gen::state(src, true);
    let op = gen::op_rej(src, &a, &Ghost::init());
    let mut s = sparse_raw(src, &a);
    let n_r = s.request_count;
    let out = check_proto(&mut s, &op);
    let Op::Rej { id, .. } = &op else {
        unreachable!()
    };
    if out.is_ok() {
        assert!(*id < n_r, "ST-2 reject: i < #R");
    }
    cover!(out.is_ok(), "proto reject: Ok");
}

// ---------------------------------------------------------------------------
// h_count_*: Counting over MemStore
// ---------------------------------------------------------------------------

/// One operation from a raw state on `Counting<MemStore>`.
// PROP: ROB-4
fn count(src: &mut impl Src, kind: u8) {
    let a = gen::state(src, true);
    let h = Ghost::init();
    let op = match kind {
        0 => gen::op_add(src, &a),
        1 => gen::op_revoke(src, &a, &h),
        2 => gen::op_req(src, &a, &h),
        3 => gen::op_appr(src, &a, &h),
        _ => gen::op_rej(src, &a, &h),
    };
    let mut c = Counting::new(to_mem(&a));
    let out = run(&mut c, &op);
    let (r, w) = (c.reads.get(), c.writes);
    assert!(r <= 4, "ROB-4 at most 4 Store reads per mutator");
    assert!(w <= 3, "ROB-4 at most 3 Store writes per mutator");
    // Per operation (section 5.6): add reads owner, the key, G and #R;
    // approve the caller's principal, the request, the agent's principal and
    // #L.
    let (max_r, max_w) = match kind {
        0 => (4, 2),
        1 => (1, 2),
        2 => (2, 2),
        3 => (4, 3),
        _ => (3, 2),
    };
    assert!(r <= max_r && w <= max_w, "ROB-4 per-operation bound");
    if !out.is_ok() && out.err() != Some(E::KeyNotRegistered) {
        assert!(w == 0, "TX-0 no write on failure");
    }
}

pub fn count_add(src: &mut impl Src) {
    count(src, 0)
}
pub fn count_revoke(src: &mut impl Src) {
    count(src, 1)
}
pub fn count_request(src: &mut impl Src) {
    count(src, 2)
}
pub fn count_approve(src: &mut impl Src) {
    count(src, 3)
}
pub fn count_reject(src: &mut impl Src) {
    count(src, 4)
}

// ---------------------------------------------------------------------------
// h_refine_*: ArrStore, Sparse and MemStore in lockstep
// ---------------------------------------------------------------------------

/// Revocation ids are distinct: the map part of INV-12.
pub fn rev_distinct(s: &S) -> bool {
    let mut ok = true;
    let mut j = 0;
    while j < CAP_V {
        let mut j2 = 0;
        while j2 < CAP_V {
            ok &= !(j < j2 && j2 < s.nv()) || s.rev(j).0 != s.rev(j2).0;
            j2 += 1;
        }
        j += 1;
    }
    ok
}

/// No live registration is revoked: part of INV-11.
pub fn live_not_revoked(s: &S) -> bool {
    let mut ok = true;
    let mut k = 0;
    while k < CAP_P {
        ok &= k >= s.np() || v_get(s, s.prin(k).1.registration_id).is_none();
        k += 1;
    }
    ok
}

/// A well-formed store: one entry per key (INV-0, so `ArrStore`'s list and
/// `MemStore`'s vector are maps), dense ids (INV-1, so requests are a
/// sequence) and distinct revocation ids. Contents are otherwise arbitrary.
pub fn wf(s: &S) -> bool {
    inv0(s) && inv1(s) && rev_distinct(s)
}

/// What refinement needs of a state, implied by `Inv`: `wf`, registration
/// provenance (INV-8, under which `expect`'s liveness test agrees with the
/// core's, F-14) and `live_not_revoked` (so a revocation never overwrites
/// one, F-16). Generated with `raw = false`, so registration ids are in
/// `0..8` and `G = #P + #V`. Every `Inv` state qualifies; so do many
/// non-`Inv` ones.
pub fn refine_pre(s: &S) -> bool {
    wf(s) && inv8(s) && live_not_revoked(s)
}

/// The same state in `ArrStore` and `Sparse` (and, in plain mode,
/// `MemStore`); one operation on each. Same results, same `α` (as [`Obs`])
/// before and after, and `Sparse` makes exactly the ST-2 calls.
///
/// Under Kani the `MemStore` leg is left out: a `Vec` of symbolic length
/// exhausts memory (RESULTS.md deviation 1). `MemStore` is tied in by ST-1
/// instead: the laws `h_store_laws_{mem,arr}` prove determine the post-`Obs`
/// of every mutator call from the pre-`Obs` and the arguments, and ST-2 keeps
/// the core's calls within the laws' preconditions, so two stores with equal
/// `Obs` that both satisfy the laws stay equal under the core.
// PROP: ST-3 ST-2
fn refine(src: &mut impl Src, kind: u8) {
    let mut a = gen::state(src, false);
    assume!(refine_pre(&a));
    let h = Ghost::init();
    let op = match kind {
        0 => gen::op_add(src, &a),
        1 => gen::op_revoke(src, &a, &h),
        2 => gen::op_req(src, &a, &h),
        3 => gen::op_appr(src, &a, &h),
        _ => gen::op_rej(src, &a, &h),
    };
    // `part`: PART_TX checks the results and the ST-2 calls, PART_POST the
    // observations. Under Kani `h_refine_approve` and `h_refine_reject` run
    // the two as `_tx` and `_post` (as one, approve ran out of memory at
    // 15 GB); the other harnesses and plain mode pass both bits.
    let part = src.part();
    let mut sp = Sparse::from_arr(&a);
    #[cfg(not(kani))]
    let mut m = to_mem(&a);
    if part & PART_POST != 0 {
        let o0 = obs(&a);
        assert!(obs(&sp) == o0, "ST-3 the start states agree");
        #[cfg(not(kani))]
        assert!(obs(&m) == o0, "ST-3 the start states agree (MemStore)");
    }
    let tx = part & PART_TX != 0;
    let exp = if tx { Some(expect(&sp, &op)) } else { None };
    let calls = match &exp {
        Some(e) => protocol(&sp, &op, e),
        None => Rec::new(),
    };
    let out_a = apply(&mut a, &op);
    let out_s = run(&mut sp, &op);
    if let Some(e) = exp {
        assert!(out_s == out_a, "ST-3 Sparse result = ArrStore result");
        assert!(out_s == e, "TX exact result (Sparse)");
        assert!(sp.calls == calls, "ST-2 store protocol (counters = sizes)");
    }
    if part & PART_POST != 0 {
        let o1 = obs(&a);
        assert!(obs(&sp) == o1, "ST-3 Sparse α = ArrStore α");
    }
    #[cfg(not(kani))]
    {
        let out_m = run(&mut m, &op);
        assert!(out_m == out_a, "ST-3 MemStore result = ArrStore result");
        assert!(obs(&m) == obs(&a), "ST-3 MemStore α = ArrStore α");
    }
}

pub fn refine_add(src: &mut impl Src) {
    refine(src, 0)
}
pub fn refine_revoke(src: &mut impl Src) {
    refine(src, 1)
}
pub fn refine_request(src: &mut impl Src) {
    refine(src, 2)
}
pub fn refine_approve(src: &mut impl Src) {
    refine(src, 3)
}
pub fn refine_reject(src: &mut impl Src) {
    refine(src, 4)
}

// ---------------------------------------------------------------------------
// h_store_laws_*: one mutator on a small well-formed store
// ---------------------------------------------------------------------------

/// One `Store` mutator call with its arguments.
pub enum Law {
    InsertPrincipal(Key, Principal<Acct>),
    RemovePrincipal(Key),
    PushRequest(Req),
    ReplaceRequest(Req),
    PushApproval(u64),
    IncrementRegistrationCount,
    InsertRevocation(u64, BlockTime),
}

/// A small well-formed store (distinct keys, dense ids, distinct revocation
/// ids; contents otherwise arbitrary, no `Inv`) and one mutator call within
/// its law's precondition.
fn law_case(src: &mut impl Src) -> Option<(S, Law)> {
    let a = gen::state(src, false);
    if !assume(wf(&a)) {
        return None;
    }
    let k = src.below(7);
    // `part` picks the laws: PART_REG the registry's two (insert and remove
    // principal), PART_POST the other five. Under Kani `h_store_laws_mem`
    // runs them as two harnesses (as one it ran out of memory at 15 GB);
    // every other caller passes both bits.
    let part = src.part();
    let bit = if k < 2 { PART_REG } else { PART_POST };
    if !assume(part & bit != 0) {
        return None;
    }
    let law = match k {
        0 => Law::InsertPrincipal(
            src.key(),
            Principal {
                account_id: src.acct(),
                role: gen::role(src),
                registration_id: gen::reg_id(src, false),
                active_from: src.u64(),
                pending: src.u32(),
            },
        ),
        1 => Law::RemovePrincipal(src.key()),
        k @ (2 | 3) => {
            let id = if k == 2 {
                a.nr() as u64
            } else {
                let id = src.below(4) as u64;
                if !assume(id < a.nr() as u64) {
                    return None;
                }
                id
            };
            let r = ActionRequest {
                id,
                agent_account_id: src.acct(),
                agent_key: src.key(),
                agent_registration_id: gen::reg_id(src, false),
                action: gen::alphabet_action(src),
                requested_at: gen::state_time(src, false),
                approval: None,
                rejection: None,
            };
            if k == 2 {
                Law::PushRequest(r)
            } else {
                Law::ReplaceRequest(r)
            }
        }
        4 => Law::PushApproval(src.u64()),
        5 => Law::IncrementRegistrationCount,
        _ => {
            let g = gen::reg_id(src, false);
            // F-16: `insert_revocation` is only ever called with a fresh id.
            if !assume(v_get(&a, g).is_none()) {
                return None;
            }
            Law::InsertRevocation(g, gen::state_time(src, false))
        }
    };
    Some((a, law))
}

/// ST-1 on store `s`: the mutator changes exactly what its law says, as
/// seen through every read.
// PROP: ST-1
fn check_law<T: Store<Acct, Key>>(s: &mut T, law: &Law) {
    let pre = obs(s);
    assert!(pre.sequences(), "ST-1 requests and log are sequences");
    assert!(obs(s) == pre, "ST-1 reads are pure");
    let mut want = pre.clone();
    let mut absent_removed = false;
    let mut overwrote = false;
    match law {
        Law::InsertPrincipal(k, p) => {
            overwrote = pre.p[k.0 as usize].is_some();
            s.insert_principal(k.clone(), p.clone());
            want.p[k.0 as usize] = Some(p.clone());
        }
        Law::RemovePrincipal(k) => {
            let got = s.remove_principal(k);
            assert!(got == pre.p[k.0 as usize], "ST-1 remove returns P(k)");
            absent_removed = got.is_none(); // L-REMOVE-ABSENT
            want.p[k.0 as usize] = None;
        }
        Law::PushRequest(r) => {
            s.push_request(r.clone());
            want.r[pre.nr as usize] = Some(obs_req(r));
            want.nr += 1;
        }
        Law::ReplaceRequest(r) => {
            s.replace_request(r.clone());
            want.r[r.id as usize] = Some(obs_req(r));
        }
        Law::PushApproval(i) => {
            s.push_approval(*i);
            want.l[pre.nl as usize] = Some(*i);
            want.nl += 1;
        }
        Law::IncrementRegistrationCount => {
            s.increment_registration_count();
            want.g += 1;
        }
        Law::InsertRevocation(g, t) => {
            s.insert_revocation(*g, *t);
            want.v[*g as usize] = Some(*t);
        }
    }
    let post = obs(s);
    assert!(post == want, "ST-1 the mutator's law");
    assert!(post.sequences(), "ST-1 requests and log stay sequences");
    cover!(overwrote, "laws: insert over an existing key");
    cover!(absent_removed, "laws: remove of an absent key");
}

/// `MemStore`: the laws, and INV-0 (no repeated key after any insert or
/// remove from a store without one).
pub fn store_laws_mem(src: &mut impl Src) {
    let Some((a, law)) = law_case(src) else {
        return;
    };
    let mut m = to_mem(&a);
    check_law(&mut m, &law);
    // PROP: INV-0
    assert!(mem_keys_distinct(&m), "INV-0 MemStore keys distinct");
}

/// Most entries a `MemStore` built from an `ArrStore` holds after one insert.
pub const CAP_MEM: usize = 5;
const _: () = assert!(CAP_MEM == CAP_P + 1);

fn mem_keys_distinct(m: &MemStore<Acct, Key>) -> bool {
    let n = m.principals.len();
    let mut ok = true;
    let mut i = 0;
    while i < CAP_MEM {
        let mut j = 0;
        while j < CAP_MEM {
            ok &= !(i < j && j < n) || m.principals[i].0 != m.principals[j].0;
            j += 1;
        }
        i += 1;
    }
    ok
}

pub fn store_laws_sparse(src: &mut impl Src) {
    let Some((a, law)) = law_case(src) else {
        return;
    };
    let mut sp = Sparse::from_arr(&a);
    check_law(&mut sp, &law);
}

/// `ArrStore`, the store every M1 harness runs the core over
/// (RESULTS.md deviation 1).
pub fn store_laws_arr(src: &mut impl Src) {
    let Some((mut a, law)) = law_case(src) else {
        return;
    };
    check_law(&mut a, &law);
    // PROP: INV-0
    assert!(inv0(&a), "INV-0 ArrStore keys distinct");
}

// ---------------------------------------------------------------------------
// h_action_len
// ---------------------------------------------------------------------------

const fn repeat<const L: usize>(pat: &[u8]) -> [u8; L] {
    let mut b = [0u8; L];
    let mut i = 0;
    while i < L {
        b[i] = pat[i % pat.len()];
        i += 1;
    }
    b
}

const AT_MAX_BYTES: [u8; MAX_ACTION_LEN] = repeat(b"x");
/// `MAX_ACTION_LEN` one-byte characters.
pub const AT_MAX: &str = match core::str::from_utf8(&AT_MAX_BYTES) {
    Ok(s) => s,
    Err(_) => panic!(),
};
const MULTI_BYTES: [u8; 2050] = repeat(&[0xC3, 0xA9]);
/// 1025 two-byte characters (`é`), 2050 bytes: within the limit in
/// characters, over it in bytes.
pub const MULTI: &str = match core::str::from_utf8(&MULTI_BYTES) {
    Ok(s) => s,
    Err(_) => panic!(),
};

/// Number of ROB-3 cases.
pub const N_CASES: usize = 5;
/// ROB-3 cases: action and the exact result.
pub const LEN_CASES: [(&str, Option<E>); N_CASES] = [
    ("", Some(E::EmptyAction)),
    (" ", None),
    (AT_MAX, None),
    (LONG, Some(E::ActionTooLong)),
    (MULTI, Some(E::ActionTooLong)),
];

/// An agent registered with room for one more request, calling directly
/// with its key; each case's action. Lengths are concrete per case.
/// Section 6.3 cost fallback 5: the result is checked by kind and by the
/// fields that do not hold the action (a full comparison is a `memcmp` over
/// 2048 bytes, which CBMC unrolls); the stored action's length is compared,
/// and `h_step_request` checks exact content on the 2-byte alphabet.
// PROP: ROB-3 TR-5 TX-4
pub fn action_len(src: &mut impl Src) {
    let mut seen = [false; 3];
    let mut i = 0;
    while i < N_CASES {
        let (action, want) = LEN_CASES[i];
        let mut s = ArrStore::new(OWNER);
        let acct = Acct(1 + src.below(NA - 1));
        let key = src.key();
        let pending = src.below(MAX_PENDING_PER_KEY as u8) as u32;
        s.push_principal_entry(
            key.clone(),
            Principal {
                account_id: acct.clone(),
                role: Role::Agent,
                registration_id: src.u64(),
                active_from: src.u64(),
                pending,
            },
        );
        let op = Op::Req {
            c: Caller {
                predecessor: acct.clone(),
                signer: acct.clone(),
                signer_key: key.clone(),
            },
            action: action.to_string(),
            t: gen::time(src),
        };
        let out = apply(&mut s, &op);
        assert!(out.err() == want, "ROB-3 length boundary in bytes");
        match &out {
            Out::Req(Ok(r)) => {
                assert!(
                    r.id == 0
                        && r.agent_account_id == acct
                        && r.agent_key == key
                        && r.action.len() == action.len()
                        && r.approval.is_none()
                        && r.rejection.is_none(),
                    "TX-4 the request records the action"
                );
                assert!(
                    s.nr() == 1 && s.req(0).action.len() == action.len(),
                    "TX-4 the request is stored"
                );
                assert!(s.prin(0).1.pending == pending + 1, "TX-4 pending + 1");
            }
            _ => assert!(
                s.nr() == 0 && s.prin(0).1.pending == pending,
                "TX-0 atomic failure"
            ),
        }
        seen[0] |= out.is_ok();
        seen[1] |= out.err() == Some(E::EmptyAction);
        seen[2] |= out.err() == Some(E::ActionTooLong);
        i += 1;
    }
    cover!(seen[0], "action_len: Ok");
    cover!(seen[1], "action_len: EmptyAction");
    cover!(seen[2], "action_len: ActionTooLong");
}

// ---------------------------------------------------------------------------
// RD-4: the client enumeration loop (plain mode only)
// ---------------------------------------------------------------------------

/// Page sizes RD-4 is checked with (section 13, M2).
#[cfg(not(kani))]
pub const RD4_LIMITS: [u64; 6] = [1, 2, 99, 100, 101, 200];

/// RD-4: with `l ≥ 1`, `from_{k+1} = from_k + len_k`, stopping at the first
/// empty page or at `from ≥ get_approval_count()`, the client reads `L`
/// exactly once and in order. Built over `MemStore` through the real core,
/// with a log of up to 250 entries, some requests rejected or left pending
/// (so log entries are not positions). With `grow`, the log also grows
/// between pages, and the loop must still end with the whole log (HIST-3,
/// HIST-5: earlier pages stay valid).
// PROP: RD-4
#[cfg(not(kani))]
pub fn client_enum(src: &mut crate::src::Rng) {
    use approval_core::{add_principal, approve, reject, request_action};
    type M = MemStore<Acct, Key>;
    let agent = Acct(1);
    let approver = Acct(2);
    let t = BlockTime {
        height: 1,
        timestamp_ns: 1,
    };
    let mut m: M = MemStore::new(OWNER);
    add_principal(&mut m, &OWNER, Key(0), agent.clone(), Role::Agent).unwrap();
    add_principal(&mut m, &OWNER, Key(1), approver.clone(), Role::Approver).unwrap();
    let ca = Caller {
        predecessor: agent.clone(),
        signer: agent,
        signer_key: Key(0),
    };
    let cb = Caller {
        predecessor: approver.clone(),
        signer: approver,
        signer_key: Key(1),
    };
    // Appends approvals until the log has `n` entries; a fifth of the
    // requests is rejected and some stay pending.
    let grow_to = |m: &mut M, n: usize, src: &mut crate::src::Rng| {
        while m.approval_log.len() < n {
            let r = request_action(m, &ca, "a".to_string(), t).unwrap();
            match src.below(10) {
                0 | 1 => {
                    reject(m, &cb, r.id, t).unwrap();
                }
                2 if m.principal(&Key(0)).unwrap().pending < 8 => {}
                _ => {
                    approve(m, &cb, r.id, "a", t).unwrap();
                }
            }
        }
    };
    let n = src.below(251) as usize;
    grow_to(&mut m, n, src);
    let grow = src.bool();
    let l = RD4_LIMITS[src.below(RD4_LIMITS.len() as u8) as usize];
    // Rule 1: stop at the first empty page. Rule 2: stop at from >= count.
    for rule in 0..2 {
        let mut m = m.clone();
        let mut from = 0u64;
        let mut got: Vec<u64> = Vec::new();
        loop {
            if rule == 1 && from >= m.approval_count() {
                break;
            }
            let page = approvals(&m, from, l);
            if page.is_empty() {
                break;
            }
            assert!(page.len() as u64 <= l.min(MAX_PAGE_SIZE), "RD-4 page size");
            for (k, p) in page.iter().enumerate() {
                assert!(p.approval_index == from + k as u64, "RD-4 index order");
                got.push(p.request_id);
            }
            from += page.len() as u64;
            if grow && src.hint(30) {
                let more = m.approval_log.len() + src.below(5) as usize;
                grow_to(&mut m, more, src);
            }
        }
        assert!(
            got == m.approval_log,
            "RD-4 the client reads L exactly once, in order"
        );
    }
    cover!(n == 250, "rd4: log of 250");
    cover!(grow, "rd4: log grows while paging");
}
