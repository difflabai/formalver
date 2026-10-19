// Must FAIL to verify (strategy.md §7 hygiene gate): if Verus accepts this,
// the toolchain proves anything and every other result is void.
use vstd::prelude::*;

verus! {

proof fn false_lemma()
    ensures
        false,
{
}

fn main() {
}

} // verus!
