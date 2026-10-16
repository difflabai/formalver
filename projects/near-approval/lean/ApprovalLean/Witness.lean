/-
LEAN-WIT (TR-5, non-vacuity): concrete reachable states where a request is
approved, rejected, void, revived-but-still-void, and where a key is at the
pending cap. `Inv` and the step properties are proved over a machine that
really does approve, reject, revoke and hit the cap, so none of them holds
vacuously. Each witness is a run from `init` checked by evaluation.

Universe: accounts, keys and payloads are `Nat`; account 0 is the owner.
-/
import ApprovalLean.Trace

namespace Approval.Witness

open Approval

abbrev N := Nat
def cfg : Cfg N := { owner := 0, maxPending := 1 }

/-- Agent key 1 of account 1, approver key 2 of account 2, one request. -/
def setup : List (Op N N N) :=
  [.add 0 1 1 .agent, .add 0 2 2 .approver, .request 1 1 1 (.pay 7)]

theorem reach (ops : List (Op N N N)) : Reach cfg (run cfg init ops) :=
  reach_run .init ops

theorem witness_approved : ∃ s : State N N N, Reach cfg s ∧ approved s 0 :=
  ⟨_, reach (setup ++ [.approve 2 2 2 0 (.pay 7)]), _, rfl, rfl⟩

theorem witness_rejected : ∃ s : State N N N, Reach cfg s ∧ rejected s 0 :=
  ⟨_, reach (setup ++ [.reject 2 2 2 0]), _, rfl, rfl, rfl⟩

theorem witness_void : ∃ s : State N N N, Reach cfg s ∧ void cfg s 0 :=
  ⟨_, reach (setup ++ [.revoke 0 1]), _, rfl, rfl, rfl⟩

/-- Revoked, re-added to the same account and role, and still void. -/
theorem witness_revival : ∃ s : State N N N, Reach cfg s ∧ void cfg s 0 ∧
    (prin cfg s 1).reg = true ∧ (prin cfg s 1).acct = 1 ∧ (prin cfg s 1).role = .agent :=
  ⟨_, reach (setup ++ [.revoke 0 1, .add 0 1 1 .agent]), ⟨_, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem witness_cap : ∃ s : State N N N, Reach cfg s ∧ (prin cfg s 1).reg = true ∧
    (prin cfg s 1).pending = cfg.maxPending :=
  ⟨_, reach setup, rfl, rfl⟩

/-- At the cap, a further request is refused with `TooManyPending`. -/
theorem witness_cap_refused :
    err cfg (run cfg init setup) (.request 1 1 1 (.pay 8)) = .tooManyPending := rfl

end Approval.Witness
