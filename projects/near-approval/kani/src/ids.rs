//! Opaque identities (ASM-IDENT, strategy.md section 6.3).
//!
//! `approval-core` is generic over `A` (account) and `K` (key) and uses them
//! only through `Clone` and `PartialEq`. These newtypes implement nothing
//! else the core could use, so a new trait bound upstream breaks this build
//! instead of silently widening what the bounds must cover.

/// Account. `Acct(0)` is the owner.
#[derive(Clone, PartialEq, Debug)]
pub struct Acct(pub u8);

/// Access key.
#[derive(Clone, PartialEq, Debug)]
pub struct Key(pub u8);

/// Accounts: the owner plus 3. `approve` distinguishes at most 3 account
/// values besides the owner (section 6.3).
pub const NA: u8 = 4;
/// Keys: at most 3 stored plus one absent value.
pub const NK: u8 = 4;

pub const OWNER: Acct = Acct(0);

/// Action alphabet: whitespace kills the `trim`-empty mutant, two ASCII
/// values give equality and inequality, one is a single multi-byte char.
/// All are 2 bytes long, so under Kani a symbolic choice among them is a
/// string of concrete length (a symbolic-length `String` is a `Vec` of
/// symbolic length, which CBMC cannot afford here). `""` is generated
/// separately (`Src::empty_action`).
pub const ACTIONS: [&str; 3] = ["ab", "  ", "\u{e9}"];
pub const ACTION_BYTES: [[u8; 2]; 3] = [*b"ab", *b"  ", [0xC3, 0xA9]];
// `spec::act_code` compares bytes against ACTION_BYTES: keep it ACTIONS'.
const _: () = {
    let mut i = 0;
    while i < ACTIONS.len() {
        let a = ACTIONS[i].as_bytes();
        assert!(a.len() == 2 && a[0] == ACTION_BYTES[i][0] && a[1] == ACTION_BYTES[i][1]);
        i += 1;
    }
};

#[cfg(kani)]
impl kani::Arbitrary for Acct {
    fn any() -> Self {
        Acct(kani::any_where(|v: &u8| *v < NA))
    }
}

#[cfg(kani)]
impl kani::Arbitrary for Key {
    fn any() -> Self {
        Key(kani::any_where(|v: &u8| *v < NK))
    }
}
