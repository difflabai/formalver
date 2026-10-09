//! Plain mode: every harness body with the random source. **Not a proof.**
//! Each test also requires every cover it evaluated to have fired, the
//! plain-mode counterpart of Kani's cover check.

use crate::checks;
use crate::src::{take_covers, Rng};

fn run(name: &str, seed: u64, iters: u32, body: fn(&mut Rng)) {
    let _ = take_covers();
    let mut rng = Rng(seed | 1);
    for _ in 0..iters {
        body(&mut rng);
    }
    let covers = take_covers();
    let missed: Vec<_> = covers.iter().filter(|(_, (_, hit))| *hit == 0).collect();
    assert!(missed.is_empty(), "{name}: unsatisfied covers {missed:?}");
}

#[test]
fn h_init() {
    run("h_init", 1, 1, checks::init);
}

#[test]
fn h_step_add() {
    run("h_step_add", 0x9E37_79B9, 20_000, checks::step_add);
}

#[test]
fn h_step_revoke() {
    run("h_step_revoke", 0x85EB_CA6B, 20_000, checks::step_revoke);
}

#[test]
fn h_step_request() {
    run("h_step_request", 0xC2B2_AE35, 20_000, checks::step_request);
}

#[test]
fn h_step_approve() {
    run("h_step_approve", 0x27D4_EB2F, 40_000, checks::step_approve);
}

#[test]
fn h_step_reject() {
    run("h_step_reject", 0x7F4A_7C15, 40_000, checks::step_reject);
}

#[test]
fn h_raw_add() {
    run("h_raw_add", 0x1656_67B1, 20_000, checks::raw_add);
}

#[test]
fn h_raw_revoke() {
    run("h_raw_revoke", 0xD3A2_646C, 20_000, checks::raw_revoke);
}

#[test]
fn h_raw_request() {
    run("h_raw_request", 0xFD70_46C5, 40_000, checks::raw_request);
}

#[test]
fn h_raw_approve() {
    run("h_raw_approve", 0xB55A_4F09, 40_000, checks::raw_approve);
}

#[test]
fn h_raw_reject() {
    run("h_raw_reject", 0x94D0_49BB, 40_000, checks::raw_reject);
}

#[test]
fn h_read() {
    run("h_read", 0x5172_8A3D, 20_000, checks::read);
}

#[test]
fn h_bmc_from_init() {
    run(
        "h_bmc_from_init",
        0x6C8E_9CF5,
        400_000,
        checks::bmc_from_init,
    );
}

#[test]
#[should_panic(expected = "canary")]
fn h_canary() {
    run("h_canary", 0x2F0E_1A1B, 2_000, checks::canary);
}
