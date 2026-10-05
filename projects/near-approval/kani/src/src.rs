//! Dual-mode value sources (strategy.md section 6.1).
//!
//! Harness bodies are written once, against [`Src`]. Under `cfg(kani)` they
//! are instantiated with [`Sym`], whose values are symbolic: **that is the
//! proof**. Under `cargo test` they run with [`Rng`], a xorshift generator with
//! hints toward interesting states: **that is a test, not a proof**. Plain
//! mode debugs specs in seconds and gates CI without Kani.
//!
//! `assume!` prunes a path (Kani) or abandons a sample (plain). `cover!` is a
//! Kani cover (must be SATISFIED) or a plain-mode hit counter that the plain
//! driver requires to fire at least once.

use crate::ids::{Acct, Key, NA, NK};
use crate::spec::{Ghost, S};

/// Sizes of a generated state: `#P`, `#R`, `#L`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Shape {
    pub np: u8,
    pub nr: u8,
    pub nl: u8,
}

pub trait Src {
    /// Any `u64`.
    fn u64(&mut self) -> u64;
    /// Any `u32`.
    fn u32(&mut self) -> u32;
    fn bool(&mut self) -> bool;
    /// A value in `0..n`.
    fn below(&mut self, n: u8) -> u8;
    /// Plain mode only: true with roughly `percent` probability, steering
    /// samples toward states where guards pass. Always false under Kani,
    /// so the unconstrained branch is the one that is verified.
    fn hint(&mut self, percent: u8) -> bool;
    /// Plain mode only: a state reached from `Init` by a random walk, with
    /// its ghost history. Always `None` under Kani.
    fn reach(&mut self) -> Option<(S, Ghost)>;
    /// Sizes `(#P, #R, #L)` of a generated state. Fixed per harness instance
    /// under Kani (see `proofs.rs`), random in plain mode.
    fn shape(&mut self) -> Shape;
    /// Which groups of step checks to run (`checks::PART_*`). Kani splits
    /// a step into separate harnesses per group; plain mode runs them all.
    fn part(&self) -> u8;
    /// Whether an operation's action argument is `""`. Fixed per harness
    /// instance under Kani (lengths must stay concrete), random in plain mode.
    fn empty_action(&mut self) -> bool;

    fn acct(&mut self) -> Acct {
        Acct(self.below(NA))
    }
    fn key(&mut self) -> Key {
        Key(self.below(NK))
    }
}

/// Prune the current path (Kani) or abandon the current sample (plain).
#[macro_export]
macro_rules! assume {
    ($cond:expr) => {{
        if !$crate::src::assume($cond) {
            return;
        }
    }};
}

/// Function form of `assume!`: returns the condition, which is always true
/// on the paths Kani keeps.
pub fn assume(c: bool) -> bool {
    #[cfg(kani)]
    kani::assume(c);
    c
}

/// A reachability goal: Kani cover (fails the run if UNSATISFIABLE, see
/// run-kani.sh) or a plain-mode hit counter.
#[macro_export]
macro_rules! cover {
    ($cond:expr, $msg:literal) => {{
        let c: bool = $cond;
        #[cfg(kani)]
        kani::cover!(c, $msg);
        #[cfg(not(kani))]
        $crate::src::record_cover(c, $msg);
    }};
}

// ---------------------------------------------------------------------------
// Symbolic source
// ---------------------------------------------------------------------------

/// Symbolic source. With `Some(shape)` generated states have that fixed
/// shape; with `None` every size up to the bound is symbolic.
#[cfg(kani)]
pub struct Sym(pub Option<Shape>, pub u8, pub bool);

#[cfg(kani)]
impl Src for Sym {
    fn u64(&mut self) -> u64 {
        kani::any()
    }
    fn u32(&mut self) -> u32 {
        kani::any()
    }
    fn bool(&mut self) -> bool {
        kani::any()
    }
    fn below(&mut self, n: u8) -> u8 {
        kani::any_where(|v: &u8| *v < n)
    }
    fn hint(&mut self, _percent: u8) -> bool {
        false
    }
    fn reach(&mut self) -> Option<(S, Ghost)> {
        None
    }
    fn part(&self) -> u8 {
        self.1
    }
    fn empty_action(&mut self) -> bool {
        self.2
    }
    fn shape(&mut self) -> Shape {
        match self.0 {
            Some(s) => s,
            None => Shape {
                np: self.below(4),
                nr: self.below(4),
                nl: self.below(4),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Random source (plain mode)
// ---------------------------------------------------------------------------

#[cfg(not(kani))]
pub struct Rng(pub u64);

#[cfg(not(kani))]
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
}

#[cfg(not(kani))]
impl Src for Rng {
    fn u64(&mut self) -> u64 {
        // Mostly small values (ids, counts) and the arithmetic edges.
        match self.next() % 8 {
            0 => u64::MAX - self.next() % 3,
            1 => self.next(),
            _ => self.next() % 6,
        }
    }
    fn u32(&mut self) -> u32 {
        match self.next() % 6 {
            0 => u32::MAX - (self.next() % 3) as u32,
            1 => approval_core::MAX_PENDING_PER_KEY - 1 + (self.next() % 3) as u32,
            2 => self.next() as u32,
            _ => (self.next() % 5) as u32,
        }
    }
    fn bool(&mut self) -> bool {
        self.next() % 2 == 0
    }
    fn below(&mut self, n: u8) -> u8 {
        (self.next() % n as u64) as u8
    }
    fn hint(&mut self, percent: u8) -> bool {
        self.next() % 100 < percent as u64
    }
    fn reach(&mut self) -> Option<(S, Ghost)> {
        if !self.hint(85) {
            return None;
        }
        let steps = (self.next() % 24) as usize;
        Some(crate::gen::random_walk(self, steps))
    }
    fn part(&self) -> u8 {
        crate::checks::PART_ALL
    }
    fn empty_action(&mut self) -> bool {
        self.hint(25)
    }
    fn shape(&mut self) -> Shape {
        Shape {
            np: self.below(4),
            nr: self.below(4),
            nl: self.below(4),
        }
    }
}

#[cfg(not(kani))]
thread_local! {
    static COVERS: std::cell::RefCell<std::collections::BTreeMap<&'static str, (u64, u64)>> =
        Default::default();
}

#[cfg(not(kani))]
pub fn record_cover(hit: bool, msg: &'static str) {
    COVERS.with(|c| {
        let mut c = c.borrow_mut();
        let e = c.entry(msg).or_default();
        e.0 += 1;
        e.1 += hit as u64;
    });
}

/// Plain driver: clears and returns `(evaluated, satisfied)` per cover.
#[cfg(not(kani))]
pub fn take_covers() -> std::collections::BTreeMap<&'static str, (u64, u64)> {
    COVERS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}
