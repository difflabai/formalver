/-
Axiom audit (run.sh audit): every headline theorem may depend only on
Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. A
`sorry` shows up here as `sorryAx`, a stray `axiom` by its name, a
`native_decide` as `Lean.ofReduceBool`.
-/
import PoolLean

-- LEAN-IND (INV-WF, INV-LEDGER, INV-HARD, INV-DEP, INV-VER)
#print axioms Pool.inv_init
#print axioms Pool.inv_step
#print axioms Pool.reach_inv
-- LEAN-STEP (LIFE-1, TERM-1, AUTH-1, STALE-1, ADM-1, ADM-2, HARD-STEP, ASYNC-1, TX-0)
#print axioms Pool.stepProps
#print axioms Pool.stepProps_step
#print axioms Pool.exec_auth
#print axioms Pool.term1
#print axioms Pool.term1_cancel
#print axioms Pool.stale1_no_replay
#print axioms Pool.version_mono_run
-- DEP-1, OBS-1, PAUSE-1 (Calls.lean)
#print axioms Pool.dep1
#print axioms Pool.obs1
#print axioms Pool.pause1_blocks
#print axioms Pool.pause1_transparent
-- LEAN-LIVE1 (LIVE-1) and INV-HEALTHY
#print axioms Pool.live1
#print axioms Pool.live1_exec
#print axioms Pool.live1_reach
#print axioms Pool.healthy
-- LEAN-GUARD
#print axioms Pool.Guard.guards_order
#print axioms Pool.Guard.outcome_mem
-- LEAN-WIT
#print axioms Pool.Witness.wcfg_valid
#print axioms Pool.Witness.wedge_eq
#print axioms Pool.Witness.f1_results
#print axioms Pool.Witness.wedge_reach
#print axioms Pool.Witness.wedge_inv
#print axioms Pool.Witness.wedge_B
#print axioms Pool.Witness.f1_settle_true
#print axioms Pool.Witness.f1_settle_false
#print axioms Pool.Witness.f1_cancel_owner
#print axioms Pool.Witness.f1_observe
#print axioms Pool.Witness.f1_forever
#print axioms Pool.Witness.f1_never_terminal
#print axioms Pool.Witness.f1_observe_forever
#print axioms Pool.Witness.f1_settle_forever
#print axioms Pool.Witness.live1_premises
#print axioms Pool.Witness.live1_instance
#print axioms Pool.Witness.healthy_settle
#print axioms Pool.Witness.cancelled_reach
#print axioms Pool.Witness.stale_instance
#print axioms Pool.Witness.unknown_settle
