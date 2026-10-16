#!/usr/bin/env bash
# MC-3 (strategy.md section 17.5): TLC and the Prolog requirements model
# must produce the same labelled reachable graph for the MC_Graph universe.
#
#   1. TLC, MC_GraphTable.cfg: every store and the calls it rejects
#   2. TLC, MC_Graph.cfg with -dump: every successful call
#   3. Scryer, graph_export.pl: the same from step/4
#   4. mc3.py: the three sets must be equal
#
# usage: tools/scripts/run-mc3.sh <project>
# env:   MC3_DIR (default: a temp dir), TLA_HEAP (default 4g)
set -euo pipefail

project=${1:?usage: run-mc3.sh <project>}
root=$(cd "$(dirname "$0")/../.." && pwd)
proj="$root/projects/$project"
. "$root/tools/versions.env"
cache=$("$root/tools/scripts/get-tla-tools.sh")
jar="$cache/tla2tools-$TLA2TOOLS.jar"
out=${MC3_DIR:-$(mktemp -d)}
mkdir -p "$out"

# Each run gets its own java.io.tmpdir, as in run-tla.sh: TLC 1.7.4 unpacks
# its standard modules under fixed names there.
tlc() { # cfg log [tlc args...]
  local cfg=$1 log=$2 tmp rc=0
  shift 2
  tmp=$(mktemp -d)
  (cd "$proj/tla" && java -XX:+UseParallelGC -Xmx"${TLA_HEAP:-4g}" -Djava.io.tmpdir="$tmp" \
    -cp "$jar" tlc2.TLC -workers 1 -cleanup -metadir "$tmp/states" "$@" \
    -config "$cfg" MC_Graph.tla) >"$log" 2>&1 || rc=$?
  rm -rf "$tmp"
  [ $rc -eq 0 ] && grep -q 'Model checking completed. No error has been found.' "$log" ||
    { echo "TLC $cfg failed, log $log" >&2; tail -20 "$log" >&2; exit 1; }
}

start=$(date +%s)
tlc MC_GraphTable.cfg "$out/table.out"
tlc MC_Graph.cfg "$out/edges.log" -dump "$out/edges"
echo "TLC: $(( $(date +%s) - start )) s"

start=$(date +%s)
(cd "$proj/prolog/verification" &&
  scryer-prolog graph_export.pl -g "(export('$out/prolog.txt') -> halt(0) ; halt(1))" </dev/null)
echo "Prolog: $(( $(date +%s) - start )) s"

python3 "$root/tools/scripts/mc3.py" "$out/edges.dump" "$out/table.out" "$out/prolog.txt"
