//! `#[kani::proof]` wrappers: each runs a `checks` body with symbolic values.
//! Bounds are in section 6.3 of strategy.md; covers are listed in section 6.2.

use crate::checks;
use crate::src::Sym;

#[kani::proof]
fn h_init() {
    checks::init(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_step_add() {
    checks::step_add(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_step_revoke() {
    checks::step_revoke(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_step_request() {
    checks::step_request(&mut Sym(None, checks::PART_ALL, false));
}

/// `h_step_request` with an empty action argument (lengths stay concrete,
/// see `Src::empty_action`). Same family for cover checking.
#[kani::proof]
#[kani::unwind(5)]
fn h_step_request_empty() {
    checks::step_request(&mut Sym(None, checks::PART_ALL, true));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_step_approve() {
    checks::step_approve(&mut Sym(None, checks::PART_ALL, false));
}

#[kani::proof]
#[kani::unwind(5)]
fn h_step_reject() {
    checks::step_reject(&mut Sym(None, checks::PART_ALL, false));
}

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

/// Must report FAILED (run-kani.sh inverts it).
#[kani::proof]
#[kani::unwind(5)]
fn h_canary() {
    checks::canary(&mut Sym(None, checks::PART_ALL, false));
}
