//! Formal verification models for ironclaw safety module.
//!
//! This crate contains Verus-annotated models of ironclaw's security-critical
//! code paths. The models mirror the types and algorithms from ironclaw's
//! `src/safety/` module, with formal specifications and proofs.
//!
//! Upstream: https://github.com/nearai/ironclaw
//! Pinned commit: 34550add3ee85bab6fe1c670dff46871d1a41e04
//!
//! # Building
//!
//! - `cargo build` — compiles plain Rust types (syntax checking only)
//! - `verus src/lib.rs --crate-type=lib` — runs full verification with proofs
//!
//! # Structure
//!
//! - `common/` — Reusable spec functions (string properties, pattern matching)
//! - `safety/` — Verified models of ironclaw's safety module

#[cfg(feature = "verus")]
use builtin::*;
#[cfg(feature = "verus")]
use builtin_macros::*;

pub mod common;
pub mod safety;
