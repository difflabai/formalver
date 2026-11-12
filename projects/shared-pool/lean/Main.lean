/-
pool-lean: runs the Lean machine against the other layers.

  pool-lean replay <traces.txt>
      REF-5L: replays every trace of conformance/traces/core.txt (generated
      from the real pool-core) on `exec`; every result and every post-state
      (values, version, observed_at, paused, records) must be equal.
  pool-lean guards
      LEAN-GUARD: each call's guard order (`Guard.guardOrder`), one line per
      call kind.
-/
import PoolLean.Machine
import PoolLean.Text
import PoolLean.Guard

open Pool Pool.Text

def replay (path : String) : IO UInt32 := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let mut cfg : Option (Cfg String) := none
  let mut s : State := default
  let mut traces := 0
  let mut steps := 0
  let mut oks := 0
  let mut lineno := 0
  let mut open_ := false
  for ln in lines do
    lineno := lineno + 1
    if ln.isEmpty then continue
    let some t := parseLine ln
      | IO.eprintln s!"REF-5L line {lineno}: cannot parse {ln}"; return 1
    match t with
    | .app "trace" [_] =>
      if open_ then
        IO.eprintln s!"REF-5L line {lineno}: trace without end"; return 1
      open_ := true
      cfg := none
    | .app "config" _ =>
      let some c := config? t
        | IO.eprintln s!"REF-5L line {lineno}: bad config"; return 1
      cfg := some c
    | .app "init" [now, st] =>
      let (some c, some n, some o) := (cfg, now.nat?, state? st)
        | IO.eprintln s!"REF-5L line {lineno}: bad init"; return 1
      s := init c n
      if obs s != o then
        IO.eprintln s!"REF-5L line {lineno}: init\n  trace: {obsText o}\n  lean:  {obsText (obs s)}"
        return 1
    | .app "call" [o, r, st] =>
      let (some c, some op, some res, some post) := (cfg, op? o, res? r, state? st)
        | IO.eprintln s!"REF-5L line {lineno}: bad call"; return 1
      let (res', s') := exec c s op
      if res' != res || obs s' != post then
        IO.eprintln s!"REF-5L line {lineno}: {ln}\n  trace: {resText res} -> {obsText post}\n  lean:  {resText res'} -> {obsText (obs s')}"
        return 1
      if res' matches .ok | .okId _ then oks := oks + 1
      s := s'
      steps := steps + 1
    | .atom "end" =>
      if !open_ then
        IO.eprintln s!"REF-5L line {lineno}: end without trace"; return 1
      open_ := false
      traces := traces + 1
    | _ => IO.eprintln s!"REF-5L line {lineno}: unexpected {ln}"; return 1
  if traces == 0 || open_ then
    IO.eprintln s!"REF-5L: no complete traces in {path}"
    return 1
  IO.println s!"REF-5L: {traces} traces, {steps} calls ({oks} Ok) replayed on the Lean machine, every result and post-state equal"
  return 0

def guardsCmd : IO UInt32 := do
  for k in Guard.kinds do
    IO.println s!"lean_guard_order({Guard.kindName k}, [{", ".intercalate ((Guard.guardOrder k).map Guard.outName)}])."
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["replay", path] => replay path
  | ["guards"] => guardsCmd
  | _ =>
    IO.eprintln "usage: pool-lean replay <traces.txt> | guards"
    return 2
