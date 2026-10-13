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
