//! Kani harnesses over the real `approval-core` (strategy.md section 6).
//!
//! `cargo test` runs every harness body in plain mode (random, not a proof).
//! `cargo kani` runs the same bodies symbolically (`proofs.rs`).

pub mod ids;
#[macro_use]
pub mod src;
pub mod checks;
pub mod gen;
pub mod spec;
pub mod store;

#[cfg(kani)]
mod proofs;

#[cfg(all(test, not(kani)))]
mod plain;
