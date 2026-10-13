#!/usr/bin/env bash
# Lean layer (strategy.md section 18): the TLA+ model transcribed to Lean 4,
# with Inv, StepProps and the run properties proved for states of every size.
#
#   build    lake build; no `sorry` warning, and the hygiene scan finds no
#            sorry, admit, axiom, native_decide, implemented_by, extern,
#            unsafe or opaque in the sources
#   audit    LEAN-*: the headline theorems (Audit.lean) depend only on
#            propext, Classical.choice and Quot.sound
#   canary   canary/*.lean must each FAIL to compile
#   guards   LEAN-GUARD: the Lean guardOrder equals TLA+'s GuardOrder, as
#            prolog/extracted/tla_facts.pl records it (C-2t)
#   replay   REF-5L: real-core traces (kani mc2_core_traces) replayed on the
#            Lean machine, every result and post-store equal
#   graph    MC-4: the Lean machine's reachable graph of the MC_Graph
#            universe equals TLC's (tools/scripts/mc3.py)
#   mutants  every lean/mutants/*.patch must be killed by build (a proof
#            breaks), replay or guards
#
# usage: tools/scripts/run-lean.sh <project> [check...]
#        (default: all of them)
# env:   LEAN_LOG_DIR (default: a temp dir), MC2_TRACES (default 2000),
#        MC2_LEN (default 120), TLA_HEAP (default 4g), TLA_CACHE
# needs: lake on PATH (elan reads lean/lean-toolchain); cargo for replay;
#        java for graph
set -uo pipefail

project=${1:?usage: run-lean.sh <project> [check...]}
shift
[ $# -gt 0 ] || set -- build audit canary guards replay graph mutants
root=$(cd "$(dirname "$0")/../.." && pwd)
proj="$root/projects/$project"
lean="$proj/lean"
logs=${LEAN_LOG_DIR:-$(mktemp -d)}
mkdir -p "$logs"
fail=0

report() { # name status message log
  if [ "$2" -eq 0 ]; then
    echo "PASS $1: $3"
  else
    echo "FAIL $1: $3 (log $4)"
    [ -n "${GITHUB_ACTIONS:-}" ] && echo "::error title=lean $1::$3"
    tail -30 "$4" 2>/dev/null | sed 's/^/  /'
    fail=1
  fi
}

# Forbidden in the sources. Comments (`--` lines and nested `/- -/`
# blocks, docstrings included) are stripped before matching.
scan() { # dir-or-file...
  python3 - "$@" <<'PY'
import pathlib, re, sys
bad = re.compile(r"\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque)\b")
files = []
for a in sys.argv[1:]:
    p = pathlib.Path(a)
    files += sorted(p.rglob("*.lean")) if p.is_dir() else [p]
for f in files:
    src, out, depth, i = f.read_text(), [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1; i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1; i += 2
        elif not depth and src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i] if not depth or src[i] == "\n" else " "); i += 1
    for n, line in enumerate("".join(out).split("\n"), 1):
        if bad.search(line):
            print(f"{f}:{n}: {line.strip()}")
PY
}

check_build() {
  local log="$logs/build.log"
  (cd "$lean" && lake build) >"$log" 2>&1
  local rc=$?
  if [ $rc -eq 0 ] && grep -q "declaration uses 'sorry'" "$log"; then rc=1; fi
  report build $rc "every theorem proved, no sorry" "$log"
  local hits="$logs/hygiene.log"
  scan "$lean/ApprovalLean" "$lean/Main.lean" "$lean/Audit.lean" "$lean/canary" >"$hits"
  [ ! -s "$hits" ]; report hygiene $? "no forbidden constructs in the sources" "$hits"
}

check_audit() {
  local log="$logs/audit.log"
  (cd "$lean" && lake env lean Audit.lean) >"$log" 2>&1
  local rc=$? n want
  want=$(grep -c '^#print axioms' "$lean/Audit.lean")
  n=$(grep -cE "depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms" "$log")
  [ $rc -eq 0 ] && [ "$n" -eq "$want" ]
  report audit $? "$n/$want theorems use only propext, Classical.choice, Quot.sound" "$log"
}

check_canary() {
  local f log
  for f in "$lean"/canary/*.lean; do
    log="$logs/canary-$(basename "$f" .lean).log"
    (cd "$lean" && lake env lean "$f") >"$log" 2>&1
    [ $? -ne 0 ] && grep -q 'error' "$log"
    report "canary $(basename "$f")" $? "fails to compile, as it must" "$log"
  done
}

check_guards() {
  local log="$logs/guards.log"
  (cd "$lean" && lake exe approval-lean guards) >"$logs/guards.txt" 2>"$log"
  tail -n +2 "$proj/prolog/extracted/tla_facts.pl" | diff - "$logs/guards.txt" >>"$log" 2>&1
  report guards $? "Lean guardOrder = TLA+ GuardOrder (tla_facts.pl)" "$log"
}

core_traces() { # writes kani/target/mc2/core.txt
  (cd "$proj/kani" && MC2_TRACES=${MC2_TRACES:-2000} MC2_LEN=${MC2_LEN:-120} \
    cargo test --release --locked --lib mc2::mc2_core_traces) >"$logs/traces-gen.log" 2>&1
}

check_replay() {
  local log="$logs/replay.log"
  core_traces || { report replay 1 "could not generate core traces" "$logs/traces-gen.log"; return; }
  (cd "$lean" && lake exe approval-lean replay "$proj/kani/target/mc2/core.txt") >"$log" 2>&1
  report replay $? "$(tail -1 "$log")" "$log"
}

check_graph() {
  local log="$logs/graph.log" out="$logs/mc4" jar
  mkdir -p "$out"
  . "$root/tools/versions.env"
  jar="$("$root/tools/scripts/get-tla-tools.sh")/tla2tools-$TLA2TOOLS.jar" ||
    { report graph 1 "no TLA+ tools" "$log"; return; }
  tlc() { # cfg log [args...]
    local cfg=$1 l=$2
    shift 2
    (cd "$proj/tla" && java -XX:+UseParallelGC -Xmx"${TLA_HEAP:-4g}" -cp "$jar" tlc2.TLC \
      -workers 1 -cleanup -metadir "$(mktemp -d)" "$@" -config "$cfg" MC_Graph.tla) >"$l" 2>&1 &&
      grep -q 'Model checking completed. No error has been found.' "$l"
  }
  {
    tlc MC_GraphTable.cfg "$out/table.out" &&
      tlc MC_Graph.cfg "$out/edges.log" -dump "$out/edges" &&
      (cd "$lean" && lake exe approval-lean graph "$out/lean.txt") &&
      python3 "$root/tools/scripts/mc3.py" "$out/edges.dump" "$out/table.out" "$out/lean.txt" Lean
  } >"$log" 2>&1
  report graph $? "$(grep -E 'graphs equal|disagree' "$log" | head -1)" "$log"
}

check_mutants() {
  local m name tmp verdict log survived=0
  [ -f "$proj/kani/target/mc2/core.txt" ] || core_traces ||
    { report mutants 1 "could not generate core traces" "$logs/traces-gen.log"; return; }
  for m in "$lean"/mutants/*.patch; do
    name=$(basename "$m" .patch)
    log="$logs/mutant-$name.log"
    tmp=$(mktemp -d)
    (cd "$lean" && tar cf - --exclude=.lake --exclude=mutants .) | (cd "$tmp" && tar xf -)
    if ! (cd "$tmp" && patch -s -p1 <"$m") >"$log" 2>&1; then
      report "mutant $name" 1 "patch does not apply" "$log"
      rm -rf "$tmp"
      continue
    fi
    verdict=survived
    if ! (cd "$tmp" && lake build) >>"$log" 2>&1 || grep -q "declaration uses 'sorry'" "$log"; then
      verdict="killed by build ($(grep -oE '^error: [A-Za-z/]+\.lean' "$log" | sed 's/^error: //' | sort -u | tr '\n' ' ' | sed 's/ $//'))"
    elif ! (cd "$tmp" && lake exe approval-lean replay "$proj/kani/target/mc2/core.txt") >>"$log" 2>&1; then
      verdict="killed by replay"
    elif ! (cd "$tmp" && lake exe approval-lean guards | diff <(tail -n +2 "$proj/prolog/extracted/tla_facts.pl") -) >>"$log" 2>&1; then
      verdict="killed by guards"
    fi
    if [ "$verdict" = survived ]; then
      survived=1
      report "mutant $name" 1 "survived" "$log"
    else
      echo "PASS mutant $name: $verdict"
    fi
    rm -rf "$tmp"
  done
  [ $survived -eq 0 ] || fail=1
}

for c in "$@"; do
  case $c in
    build | audit | canary | guards | replay | graph | mutants) "check_$c" ;;
    *) echo "unknown check $c" >&2; exit 2 ;;
  esac
done
exit $fail
