/-
approval-lean: runs the Lean machine against the other layers.

  approval-lean replay <traces.txt> [max_pending]
      REF-5L: replays MC-2 traces (kani/src/mc2.rs `core.txt`, or the
      Prolog model's `prolog.txt`) on `step`; every result and post-store
      must match. max_pending defaults to the core's 16.
  approval-lean graph <out.txt>
      MC-4: the labelled reachable graph of the MC_Graph universe
      (tla/MC_Graph.cfg), in graph_export.pl's S/R/E format, for
      tools/scripts/mc3.py to compare with TLC's.
  approval-lean guards
      LEAN-GUARD: `guardOrder` in prolog/extracted/tla_facts.pl's format.
-/
import ApprovalLean.Machine
import ApprovalLean.Guard
import ApprovalLean.Text
import Std.Data.HashSet

open Approval Approval.Text

instance : Inhabited S := ⟨init⟩

def stepE (cfg : Cfg String) (s : S) (op : O) : Err × S :=
  let e := err cfg s op
  (e, if e = .ok then effect cfg s op else s)

/-! ## replay -/

def replay (path : String) (maxPending : Nat) : IO UInt32 := do
  let cfg : Cfg String := { owner := "o", maxPending }
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let mut s : S := init
  let mut traces := 0
  let mut steps := 0
  let mut lineno := 0
  for ln in lines do
    lineno := lineno + 1
    if ln.isEmpty then continue
    if ln == "#" then
      s := init
      traces := traces + 1
      continue
    match ln.splitOn "\t" with
    | [c, res, post] =>
      let some op := parseCall c
        | IO.eprintln s!"REF-5L line {lineno}: cannot parse call {c}"; return 1
      let (e, s') := stepE cfg s op
      if errName e != res || store s' != post then
        IO.eprintln s!"REF-5L line {lineno}: {c}\n  trace: {res} -> {post}\n  lean:  {errName e} -> {store s'}"
        return 1
      s := s'
      steps := steps + 1
    | _ => IO.eprintln s!"REF-5L line {lineno}: expected 3 tab-separated fields"; return 1
  if traces == 0 then
    IO.eprintln s!"REF-5L: no traces in {path}"
    return 1
  IO.println s!"REF-5L: {traces} traces, {steps} steps replayed on the Lean machine, all equal"
  return 0

/-! ## graph -/

def accounts : List String := ["o", "a1", "a2"]
def keys : List String := ["k1", "k2"]
def acts : List (Action String) := [.pay "x", .empty, .tooLong]
def maxReq : Nat := 2
def maxReg : Nat := 3

/-- Every call in a store with `nr` requests, in mc3.py's `calls` order. -/
def calls (nr : Nat) : List O := Id.run do
  let mut out : Array O := #[]
  for c in accounts do
    for k in keys do
      for a in accounts do
        for r in [Role.agent, Role.approver] do
          out := out.push (.add c k a r)
  for c in accounts do
    for k in keys do
      out := out.push (.revoke c k)
  let tri := Id.run do
    let mut t : Array (String × String × String) := #[]
    for p in accounts do
      for sg in accounts do
        for k in keys do
          t := t.push (p, sg, k)
    return t
  for (p, sg, k) in tri do
    for x in acts do
      out := out.push (.request p sg k x)
  for (p, sg, k) in tri do
    for i in List.range (nr + 1) do
      for x in acts do
        out := out.push (.approve p sg k i x)
  for (p, sg, k) in tri do
    for i in List.range (nr + 1) do
      out := out.push (.reject p sg k i)
  return out.toList

/-- TLC's action bounds: an add only below `MaxReg` registrations, a request
only below `MaxReq` requests. -/
def inBounds (s : S) : O → Bool
  | .add .. => s.regs < maxReg
  | .request .. => s.nr < maxReq
  | _ => true

def graph (path : String) : IO UInt32 := do
  let cfg : Cfg String := { owner := "o", maxPending := 1 }
  let h ← IO.FS.Handle.mk path .write
  let mut seen : Std.HashSet String := {}
  let s0 : S := init
  seen := seen.insert (store s0)
  let mut queue : Array S := #[s0]
  let mut qi := 0
  let mut nEdges := 0
  while qi < queue.size do
    let s := queue[qi]!
    qi := qi + 1
    let st := store s
    h.putStrLn s!"S\t{st}"
    let mut results : Array String := #[]
    for op in calls s.nr do
      let e := err cfg s op
      results := results.push (errName e)
      if e = .ok && inBounds s op then
        let s' := effect cfg s op
        let st' := store s'
        h.putStrLn s!"E\t{st}\t{call op}\t{st'}"
        nEdges := nEdges + 1
        if !seen.contains st' then
          seen := seen.insert st'
          queue := queue.push s'
    h.putStrLn s!"R\t{st}\t{",".intercalate results.toList}"
  h.flush
  IO.println s!"MC-4: Lean graph: {queue.size} stores, {nEdges} edges"
  return 0

/-! ## guards -/

def opName : OpKind → String
  | .add => "add_principal"
  | .revoke => "revoke_key"
  | .request => "request_action"
  | .approve => "approve"
  | .reject => "reject"

def guardsCmd : IO UInt32 := do
  for k in [OpKind.add, .revoke, .request, .approve, .reject] do
    let errs := (guardOrder k).map fun e => s!"'{errName e}'"
    IO.println s!"tla_guard_order({opName k}, [{", ".intercalate errs}])."
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["replay", path] => replay path 16
  | ["replay", path, mp] =>
    match mp.toNat? with
    | some n => replay path n
    | none => IO.eprintln "max_pending must be a number"; return 2
  | ["graph", path] => graph path
  | ["guards"] => guardsCmd
  | _ =>
    IO.eprintln "usage: approval-lean replay <traces.txt> [max_pending] | graph <out.txt> | guards"
    return 2
