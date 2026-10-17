//! `#[kani::proof]` wrappers: each runs a `checks` body with symbolic values.
//! Bounds are in section 6.3 of strategy.md; covers are listed in section 6.2.

use crate::checks;
use crate::src::Sym;

#[kani::proof]
fn h_init() {
    checks::init(&mut Sym(None, checks::PART_ALL, false));
}

/// A step harness in five parts (section 6.3 fallback 1: split further):
/// `_tx` exact result and atomic failure, `_post` exact post-state, `_hist`
/// history and potential, `_inv`
/// the `5736251` invariants, `_reg` the registration and decision
/// invariants. Each part is its own CBMC run; a family's covers are checked
/// across its parts.
macro_rules! step_parts {
    ($body:path, $empty:expr, $tx:ident, $post:ident, $hist:ident, $inv:ident, $reg:ident) => {
        #[kani::proof]
        #[kani::unwind(5)]
        fn $tx() {
            $body(&mut Sym(None, checks::PART_TX, $empty));
        }
        #[kani::proof]
        #[kani::unwind(5)]
        fn $post() {
            $body(&mut Sym(None, checks::PART_POST, $empty));
        }
        #[kani::proof]
        #[kani::unwind(5)]
        fn $hist() {
            $body(&mut Sym(None, checks::PART_HIST, $empty));
        }
        #[kani::proof]
        #[kani::unwind(5)]
        fn $inv() {
            $body(&mut Sym(None, checks::PART_INV, $empty));
        }
        #[kani::proof]
        #[kani::unwind(5)]
        fn $reg() {
            $body(&mut Sym(None, checks::PART_REG, $empty));
        }
    };
}

step_parts!(
    checks::step_add,
    false,
    h_step_add_tx,
    h_step_add_post,
    h_step_add_hist,
    h_step_add_inv,
    h_step_add_reg
);
step_parts!(
    checks::step_revoke,
    false,
    h_step_revoke_tx,
    h_step_revoke_post,
    h_step_revoke_hist,
    h_step_revoke_inv,
    h_step_revoke_reg
);
step_parts!(
    checks::step_request,
    false,
    h_step_request_tx,
    h_step_request_post,
    h_step_request_hist,
    h_step_request_inv,
    h_step_request_reg
);
// `""` action instances (lengths stay concrete, see `Src::empty_action`).
step_parts!(
    checks::step_request,
    true,
    h_step_request_empty_tx,
    h_step_request_empty_post,
    h_step_request_empty_hist,
    h_step_request_empty_inv,
    h_step_request_empty_reg
);
step_parts!(
    checks::step_approve,
    false,
    h_step_approve_tx,
    h_step_approve_post,
    h_step_approve_hist,
    h_step_approve_inv,
    h_step_approve_reg
);
step_parts!(
    checks::step_reject,
    false,
    h_step_reject_tx,
    h_step_reject_post,
    h_step_reject_hist,
    h_step_reject_inv,
    h_step_reject_reg
);

#[kani::proof]
#[kani::unwind(5)]
fn h_raw_add() {
    checks::raw_add(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_raw_revoke() {
    checks::raw_revoke(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_raw_request() {
    checks::raw_request(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_raw_request_empty() {
    checks::raw_request(&mut Sym(None, checks::PART_ALL, true));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_raw_approve() {
    checks::raw_approve(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_raw_reject() {
    checks::raw_reject(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_read() {
    checks::read(&mut Sym(None, checks::READ_POINT, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_read_page() {
    checks::read(&mut Sym(None, checks::READ_PAGE, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_read_find() {
    checks::read(&mut Sym(None, checks::READ_FIND, false));
}

#[kani::proof]
#[kani::unwind(8)]
fn h_bmc_from_init() {
    // Ghost only: TX, HIST and INV are proven for one step from any Inv
    // state by h_step_* (and Init is Inv by h_init), so re-checking them
    // at every depth here adds cost and no coverage.
    checks::bmc_from_init(&mut Sym(None, 0, false));
}

/// The TR-3 witness, one step longer than `h_bmc_from_init`.
#[kani::proof]
#[kani::unwind(8)]
fn h_bmc_from_init_witness() {
    checks::witness_revival(&mut Sym(None, 0, false));
}

/// Must report FAILED (run-kani.sh inverts it).
#[kani::proof]
#[kani::unwind(5)]
fn h_canary() {
    checks::canary(&mut Sym(None, checks::PART_ALL, false));
}

// ---------------------------------------------------------------------------
// h_ref_*: one step of the core refines the TLA+ spec (REF-1..4, tla.rs).
// Same states and operations as h_step_*, only the refinement checks.
// Unwind 6: the abstract state's arrays hold CR + 1 = 5 entries.
// ---------------------------------------------------------------------------

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_add() {
    checks::step_add(&mut Sym(None, checks::PART_REF, false));
}

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_revoke() {
    checks::step_revoke(&mut Sym(None, checks::PART_REF, false));
}

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_request() {
    checks::step_request(&mut Sym(None, checks::PART_REF, false));
}

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_request_empty() {
    checks::step_request(&mut Sym(None, checks::PART_REF, true));
}

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_approve() {
    checks::step_approve(&mut Sym(None, checks::PART_REF, false));
}

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_reject() {
    checks::step_reject(&mut Sym(None, checks::PART_REF, false));
}

#[kani::proof]
#[kani::unwind(6)]
fn h_ref_toolong() {
    checks::ref_toolong(&mut Sym(None, checks::PART_REF, false));
}

// CUT-1: footprint of each operation, from a raw state (CUTOFF.md).
#[kani::proof]
#[kani::unwind(5)]
fn h_cut_add() {
    crate::cutoff::cut_add(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_cut_revoke() {
    crate::cutoff::cut_revoke(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_cut_request() {
    crate::cutoff::cut_request(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_cut_approve() {
    crate::cutoff::cut_approve(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_cut_reject() {
    crate::cutoff::cut_reject(&mut Sym(None, checks::PART_ALL, false));
}

// ---------------------------------------------------------------------------
// M2: ghost stores (ghost.rs, ghost_checks.rs; strategy.md section 6.2)
// ---------------------------------------------------------------------------

use crate::ghost_checks as g2;
use crate::src::Shape;

/// The `MemStore` harnesses' state shape. A `MemStore` built from a state
/// of symbolic size is a `Vec` of symbolic length, which exhausted 13.5 GB
/// (RESULTS.md deviation 1), so these fix `#P = #R = #L = #V = 3`. The
/// contents stay symbolic: a key is present at any of the three positions
/// or absent, an id names any request or none. The core has no loops
/// (CUT-1), so its call counts do not depend on the sizes; the laws are
/// per call, and `h_store_laws_{arr,sparse}` check them at every size.
const MEM_SHAPE: Shape = Shape {
    np: 3,
    nr: 3,
    nl: 3,
    nv: 3,
};

/// `h_store_laws_mem_law_{insert,remove}`: the registry laws touch only
/// principals, so the other parts are one entry each (the frame); `MEM_SHAPE`
/// ran out of memory at 15 GB. The other five laws: one principal. The `Sparse` halves use the same shapes (with a symbolic
/// shape 20 and 23 min at 9.7 GB); `h_store_laws_arr` keeps every shape.
const MEM_SHAPE_REG: Shape = Shape {
    np: 3,
    nr: 1,
    nl: 1,
    nv: 1,
};
const MEM_SHAPE_SEQ: Shape = Shape {
    np: 1,
    nr: 3,
    nl: 3,
    nv: 3,
};

/// RD-3, RD-6, ROB-4 (approvals), one cover family. `h_page_arith`:
/// approved requests, `from` and `count` any `u64`, `limit <= PAGE_SMALL`
/// (non-empty pages, including at the top of the range). Unwind 5: at most
/// `PAGE_SMALL` = 2 slots, and a page check loop of at most `CAP_R`.
#[kani::proof]
#[kani::unwind(5)]
fn h_page_arith() {
    g2::page_arith(&mut Sym(None, g2::PAGE_FULL, false));
}

/// `h_page_arith_empty`: requests absent, `from`, `limit` and `count` any
/// `u64`. Unwind 102: at most `MAX_PAGE_SIZE` = 100 slots.
#[kani::proof]
#[kani::unwind(102)]
fn h_page_arith_empty() {
    g2::page_arith(&mut Sym(None, g2::PAGE_EMPTY, false));
}

// ST-2, ROB-2, TR-5: raw recording `Sparse`, counters any u64 >= size.
#[kani::proof]
#[kani::unwind(5)]
fn h_proto_add() {
    g2::proto_add(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_proto_revoke() {
    g2::proto_revoke(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_proto_request() {
    g2::proto_request(&mut Sym(None, checks::PART_ALL, false));
}

/// `""` action instance (lengths stay concrete, see `Src::empty_action`).
#[kani::proof]
#[kani::unwind(5)]
fn h_proto_request_empty() {
    g2::proto_request(&mut Sym(None, checks::PART_ALL, true));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_proto_approve() {
    g2::proto_approve(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_proto_reject() {
    g2::proto_reject(&mut Sym(None, checks::PART_ALL, false));
}

// K-ORACLE: approve and reject at any store size (requests and log slots at
// any positions, counters free); see `ghost_checks::sparse_free`.
#[kani::proof]
#[kani::unwind(5)]
fn h_oracle_approve() {
    g2::oracle_approve(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_oracle_reject() {
    g2::oracle_reject(&mut Sym(None, checks::PART_ALL, false));
}

// ROB-4: `Counting` over `MemStore`, state shape `MEM_SHAPE`.
#[kani::proof]
#[kani::unwind(5)]
fn h_count_add() {
    g2::count_add(&mut Sym(Some(MEM_SHAPE), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_count_revoke() {
    g2::count_revoke(&mut Sym(Some(MEM_SHAPE), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_count_request() {
    g2::count_request(&mut Sym(Some(MEM_SHAPE), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_count_approve() {
    g2::count_approve(&mut Sym(Some(MEM_SHAPE), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_count_reject() {
    g2::count_reject(&mut Sym(Some(MEM_SHAPE), checks::PART_ALL, false));
}

// ST-3 (and ST-2 with counters equal to size): ArrStore and Sparse (the
// MemStore leg runs in plain mode; see `ghost_checks::refine`).
// Unwind 9: `Obs` probes 8 registration ids.
#[kani::proof]
#[kani::unwind(9)]
fn h_refine_add() {
    g2::refine_add(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_refine_revoke() {
    g2::refine_revoke(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_refine_request() {
    g2::refine_request(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_refine_approve_tx() {
    g2::refine_approve(&mut Sym(None, checks::PART_TX, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_refine_approve_post() {
    g2::refine_approve(&mut Sym(None, checks::PART_POST, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_refine_reject_tx() {
    g2::refine_reject(&mut Sym(None, checks::PART_TX, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_refine_reject_post() {
    g2::refine_reject(&mut Sym(None, checks::PART_POST, false));
}

// ST-1, INV-0. One harness per law (`ghost_checks::mem_law`): through the
// shared `Law` dispatch they ran out of memory on the 64 GB CI runners. Insert and remove
// principal use `MEM_SHAPE_REG` and carry the covers and INV-0's
// interesting cases; the others `MEM_SHAPE_SEQ`. run-kani.sh puts all seven
// in the `h_store_laws_mem` cover family.
#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_insert() {
    g2::mem_law_insert(&mut Sym(Some(MEM_SHAPE_REG), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_remove() {
    g2::mem_law_remove(&mut Sym(Some(MEM_SHAPE_REG), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_push_request() {
    g2::mem_law_push_request(&mut Sym(Some(MEM_SHAPE_SEQ), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_replace_request() {
    g2::mem_law_replace_request(&mut Sym(Some(MEM_SHAPE_SEQ), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_push_approval() {
    g2::mem_law_push_approval(&mut Sym(Some(MEM_SHAPE_SEQ), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_count() {
    g2::mem_law_count(&mut Sym(Some(MEM_SHAPE_SEQ), checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_mem_law_revocation() {
    g2::mem_law_revocation(&mut Sym(Some(MEM_SHAPE_SEQ), checks::PART_ALL, false));
}

// Split by law: as one harness 29 min and 9.6 GB.
#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_sparse() {
    g2::store_laws_sparse(&mut Sym(Some(MEM_SHAPE_SEQ), checks::PART_POST, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_sparse_reg() {
    g2::store_laws_sparse(&mut Sym(Some(MEM_SHAPE_REG), checks::PART_REG, false));
}

#[kani::proof]
#[kani::unwind(9)]
fn h_store_laws_arr() {
    g2::store_laws_arr(&mut Sym(None, checks::PART_ALL, false));
}

/// ROB-3. Every string is concrete. Unwind 2051: no loop of the harness
/// itself needs more than 6, but a mutant that counts characters walks all
/// 2050 bytes of the last case and must fail on its assertion, not on an
/// unwinding assertion.
#[kani::proof]
#[kani::unwind(2051)]
fn h_action_len() {
    g2::action_len(&mut Sym(None, checks::PART_ALL, false));
}
