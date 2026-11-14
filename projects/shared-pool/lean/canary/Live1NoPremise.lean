/-
Canary (run.sh canary): this file must FAIL to compile. LIVE-1 without its
premise B = 0 is false (F-1: the wedge is a reachable `Inv` state in which
the executor's settle fails), so it must not be provable.
-/
import PoolLean

open Pool in
theorem canary_live1_unconditional {cfg : Cfg Nat} (hV : Valid cfg) {s : State} (I : Inv cfg s)
    (hv : s.version < U32_MAX) {id : Nat} (hk : id < s.records.length)
    (hst : inFlight s.records[id].status = true) :
    outcome cfg s (.settle (cfg.recipe s.records[id].recipe).executor id true) = none := by
  first | exact live1 hV I (by grind) hv hk hst | grind | simp_all
