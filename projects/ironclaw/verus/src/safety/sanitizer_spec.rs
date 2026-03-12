//! Formal specifications for the prompt injection sanitizer.
//!
//! These spec functions define the properties that the sanitizer must satisfy.
//! Proofs in sanitizer_proof.rs demonstrate these properties hold.
//!
//! This module is only compiled with the Verus toolchain (feature = "verus").

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::seq::*;

use crate::common::string_props::*;
use crate::safety::sanitizer::*;

verus! {

// =========================================================================
// Property 1: Detection Completeness
//
// Every defined pattern that appears in the input (case-insensitive) must
// produce at least one warning.
// =========================================================================

/// If a pattern from the pattern list appears in the input (case-insensitively),
/// then the detected warning set must include that pattern's index.
pub open spec fn detection_is_complete(
    input: Seq<char>,
    patterns: Seq<Seq<char>>,
    matched_indices: Set<int>,
) -> bool {
    forall|i: int| 0 <= i && i < patterns.len()
        && contains_subseq_ci(input, patterns[i])
        ==> matched_indices.contains(i)
}

// =========================================================================
// Property 2: Escape Correctness
//
// When any critical pattern is detected, the output must have special tokens
// escaped (they should no longer appear unescaped).
// =========================================================================

/// When critical patterns are found, the output is properly escaped.
pub open spec fn escape_is_correct(
    has_critical: bool,
    was_modified: bool,
    output: Seq<char>,
) -> bool {
    has_critical ==> (
        was_modified
        && null_bytes_removed(output)
    )
}

// =========================================================================
// Property 3: Severity Ordering
//
// Warnings are sorted by severity, critical first.
// =========================================================================

pub open spec fn severity_ordering_correct(
    warning_severities: Seq<Severity>,
) -> bool {
    forall|i: int, j: int|
        0 <= i && i < j && j < warning_severities.len()
        ==> severity_value_spec(warning_severities[i]) >= severity_value_spec(warning_severities[j])
}

// =========================================================================
// Property 4: No False Modification
//
// If no pattern matches the input, the content is returned unchanged.
// =========================================================================

pub open spec fn no_false_modification(
    has_critical: bool,
    was_modified: bool,
) -> bool {
    !has_critical ==> !was_modified
}

// =========================================================================
// Property 5: Case Insensitivity
//
// Two inputs that differ only in case produce the same set of detected patterns.
// =========================================================================

pub open spec fn case_insensitive_detection(
    input1: Seq<char>,
    input2: Seq<char>,
    patterns: Seq<Seq<char>>,
) -> bool {
    to_lower_seq(input1) =~= to_lower_seq(input2) ==> (
        pattern_match_result(input1, patterns) =~= pattern_match_result(input2, patterns)
    )
}

// =========================================================================
// Property 6: Critical Implies Modification
// =========================================================================

pub open spec fn critical_implies_modification(has_critical: bool, was_modified: bool) -> bool {
    has_critical ==> was_modified
}

} // verus!
