//! Spec functions for string properties used across verification proofs.
//!
//! These provide the formal vocabulary for reasoning about substring
//! containment, case-insensitive matching, and string transformations.
//!
//! Under standard cargo (without the `verus` feature), this module is empty.
//! The spec/proof functions are only available when compiled with the Verus toolchain.

// All verification logic lives inside the verus! macro, which requires
// the Verus toolchain. Under standard cargo, this module provides no items.
#[cfg(feature = "verus")]
mod verus_impl {
    use builtin::*;
    use builtin_macros::*;
    use vstd::prelude::*;
    use vstd::seq::*;

    verus! {

    /// Returns true if `haystack` contains `needle` as a contiguous subsequence.
    pub open spec fn contains_subseq(haystack: Seq<char>, needle: Seq<char>) -> bool {
        exists|i: int| 0 <= i && i + needle.len() <= haystack.len()
            && haystack.subrange(i, i + needle.len()) =~= needle
    }

    /// Returns the lowercase version of a character (ASCII only).
    pub open spec fn to_lower_char(c: char) -> char {
        if 'A' as u32 <= c as u32 && c as u32 <= 'Z' as u32 {
            char::from(c as u32 + 32)
        } else {
            c
        }
    }

    /// Returns a sequence with all ASCII characters lowercased.
    pub open spec fn to_lower_seq(s: Seq<char>) -> Seq<char> {
        s.map(|_i: int, c: char| to_lower_char(c))
    }

    /// Case-insensitive substring containment (ASCII).
    pub open spec fn contains_subseq_ci(haystack: Seq<char>, needle: Seq<char>) -> bool {
        contains_subseq(to_lower_seq(haystack), to_lower_seq(needle))
    }

    /// A replacement operation: every occurrence of `target` in `input` is replaced
    /// with `replacement`. Specified abstractly — the concrete implementation is trusted.
    pub open spec fn string_replace(input: Seq<char>, target: Seq<char>, replacement: Seq<char>) -> Seq<char>;

    /// Axiom: after replacement, the target no longer appears in the output
    /// (assuming target does not appear in replacement).
    pub proof fn string_replace_removes_target(
        input: Seq<char>,
        target: Seq<char>,
        replacement: Seq<char>,
    )
        requires
            target.len() > 0,
            !contains_subseq(replacement, target),
        ensures
            !contains_subseq(string_replace(input, target, replacement), target),
    {
        assume(false); // TODO: prove from axioms about string_replace
    }

    /// Counts the number of non-overlapping occurrences of `needle` in `haystack`.
    pub open spec fn count_occurrences(haystack: Seq<char>, needle: Seq<char>) -> nat
        decreases haystack.len(),
    {
        if needle.len() == 0 || haystack.len() < needle.len() {
            0
        } else if haystack.subrange(0, needle.len() as int) =~= needle {
            1 + count_occurrences(haystack.subrange(needle.len() as int, haystack.len() as int), needle)
        } else {
            count_occurrences(haystack.subrange(1, haystack.len() as int), needle)
        }
    }

    } // verus!
}

#[cfg(feature = "verus")]
pub use verus_impl::*;
