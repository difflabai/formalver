//! Kani harnesses over the real `approval-core` (strategy.md section 6).
//!
//! `cargo test` runs every harness body in plain mode (random, not a proof).
//! `cargo kani` runs the same bodies symbolically (`proofs.rs`).

pub mod ids;
#[macro_use]
pub mod src;
pub mod checks;
pub mod cutoff;
pub mod gen;
pub mod ghost;
pub mod ghost_checks;
pub mod norm;
pub mod spec;
pub mod store;
pub mod tla;
#[cfg(not(kani))]
pub mod trace;

#[cfg(kani)]
mod proofs;

#[cfg(all(test, not(kani)))]
mod plain;

#[cfg(all(test, not(kani)))]
mod facts;

#[cfg(all(test, not(kani)))]
mod mc2;

#[cfg(all(test, not(kani)))]
mod link;
