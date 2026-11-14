//! Kani harnesses over the real `pool-core` (shared-pool strategy, Kani layer).
//!
//! `cargo test --release` runs every harness body in plain mode (random, **not
//! a proof**). `cargo kani` runs the same bodies symbolically (`proofs.rs`):
//! that is the bounded proof.
//!
//! Verified: shared-pool-controls v1.0.0 (contract code byte-identical to the
//! pin). Pin: difflabai/shared-pool-controls PR #1 head
//! `a4bb5c3c9cef1ed03bcbe8f3350ab6e84200eae7`, `crates/core/src/lib.rs`
//! sha256 `9a4eb36cc9690d353f8ec78e4eec6e389a895caccab24ced54994b8a8e7505c4`.

#![cfg_attr(kani, feature(allocator_api))]

#[macro_use]
pub mod src;
pub mod checks;
pub mod gen;
pub mod spec;
/// The TLA+ transcription for REF-1..3 (`tla/SharedPool.tla`).
pub mod tla;

#[cfg(kani)]
pub mod model;
#[cfg(kani)]
mod proofs;

#[cfg(all(test, not(kani)))]
mod plain;
#[cfg(all(test, not(kani)))]
mod conform;
