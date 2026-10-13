/-
Axiom audit (run-lean.sh audit): every headline theorem may depend only on
Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. A
`sorry` shows up here as `sorryAx`, a stray `axiom` by its name.
-/
import ApprovalLean

-- LEAN-IND
#print axioms Approval.inv_init
#print axioms Approval.inv_next
#print axioms Approval.inv_step
#print axioms Approval.reach_inv
#print axioms Approval.approvable_all
-- LEAN-STEP
#print axioms Approval.stepProps_next
#print axioms Approval.stepProps_step
-- LEAN-TR
#print axioms Approval.reach_run
#print axioms Approval.tr1_provenance
#print axioms Approval.tr2_decision_final
#print axioms Approval.tr3_void_terminal
#print axioms Approval.hist1_run
#print axioms Approval.hist3_run
#print axioms Approval.hist10_run
-- LEAN-GUARD
#print axioms Approval.err_eq_firstFail
#print axioms Approval.guards_order
#print axioms Approval.err_mem_guardOrder
#print axioms Approval.err_ne_logFull
-- LEAN-WIT
#print axioms Approval.Witness.witness_approved
#print axioms Approval.Witness.witness_rejected
#print axioms Approval.Witness.witness_void
#print axioms Approval.Witness.witness_revival
#print axioms Approval.Witness.witness_cap
#print axioms Approval.Witness.witness_cap_refused
