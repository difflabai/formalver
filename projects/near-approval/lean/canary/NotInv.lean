/-
Canary (run-lean.sh canary): this file must FAIL to compile. Not every
state satisfies `Inv` (a pending count that disagrees with the requests,
for one), so no automation may prove it; if it compiles, `Inv` has become
trivial.
-/
import ApprovalLean

open Approval in
theorem canary_every_state_inv (cfg : Cfg Nat) (s : State Nat Nat Nat) : Inv cfg s := by
  first | exact reach_inv (by grind) | grind | simp_all
