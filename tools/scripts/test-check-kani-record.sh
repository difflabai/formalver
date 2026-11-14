#!/usr/bin/env bash
# Self-test for check-kani-record.py and kani/local/record.py: a synthetic
# finished local run of the kani-large and kani-mutants-large jobs (at HEAD)
# records and passes the check; an incomplete, failed or foreign run is
# refused and leaves the record alone; and each kind of stale, wrong or
# inconsistent record, and each workflow matrix that does not split the
# harnesses and mutants with the record, fails the check. Commits with
# other Kani inputs are made in a scratch object directory over the
# repository's (no object, ref or index of the repository is written).
#
# usage: tools/scripts/test-check-kani-record.sh
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
check="$here/check-kani-record.py"
record="$root/projects/shared-pool/kani/local/record.py"
wf="$root/.github/workflows/shared-pool.yml"
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
fail=0
unset GITHUB_ACTIONS  # plain error:/warning: lines, not workflow commands
py() { python3 -I "$@"; }

# fixture <run dir>: a finished run of every kani-large harness (ok, one
# SATISFIED cover each) and kani-mutants-large mutant (as its patch
# expects), with HEAD's provenance.
fixture() {
  py - "$1" "$check" "$root" <<'PY'
import json, os, re, subprocess, sys
d, check, root = sys.argv[1:4]
def out(*a):
    return subprocess.run(list(a), capture_output=True, text=True, check=True).stdout
def git(*a):
    return out("git", "-C", root, *a).strip()
ver = git("show", "HEAD:tools/versions.env")
K = re.search(r"^KANI=(\S+)", ver, re.M).group(1)
C = re.search(r"^CBMC=(\S+)", ver, re.M).group(1)
mdir = os.path.join(root, "projects/shared-pool/kani/mutants")
jobs = []
for line in out(sys.executable, "-I", check, "matrix", "kani-large").splitlines():
    g, gb, to = line.split("\t")
    for h in g.split():
        jobs.append(dict(name=h, kind="harness", peak=float(gb), est=100, timeout=int(to), args=["kani", h]))
for line in out(sys.executable, "-I", check, "matrix", "kani-mutants-large").splitlines():
    nn, gb, to = line.split("\t")
    jobs.append(dict(name="mutant-" + nn, kind="mutant", peak=float(gb), est=100, timeout=int(to),
                     args=["mutants", "--kani", nn + "-*"]))
os.makedirs(os.path.join(d, "logs"))
rows = []
for j in jobs:
    ld = os.path.join(d, "logs", j["name"])
    os.makedirs(ld)
    if j["kind"] == "harness":
        h = j["name"]
        with open(ld + "/stdout.txt", "w") as f:
            f.write("%-26s %-13s %8s  %s\n" % ("harness", "result", "seconds", "covers"))
            f.write("%-26s %-13s %8s  %s\n" % (h, "ok", 42, "1 of 1 cover properties satisfied"))
            f.write("covers: 1 recorded in %s/covers.tsv, family check deferred\n" % ld)
        with open(ld + "/covers.tsv", "w") as f:
            f.write("fam_%s\tcover of %s\tSATISFIED\n" % (h, h))
        open(ld + "/%s.log" % h, "w").write("VERIFICATION:- SUCCESSFUL\n")
        v = "ok"
    else:
        nn = j["name"].split("-", 1)[1]
        p = [f[:-6] for f in sorted(os.listdir(mdir)) if f.startswith(nn + "-") and f.endswith(".patch")][0]
        text = open(os.path.join(mdir, p + ".patch")).read()
        e, k = ("survive", "survived") if "# must-survive\n" in text else ("killed", "killed")
        h0 = re.search(r"^# (?:killed-by|checked-by): (\S+)", text, re.M).group(1)
        with open(ld + "/stdout.txt", "w") as f:
            f.write("%-42s %-8s %-8s %s\n" % ("mutant", "expect", "plain", "kani"))
            f.write("%-42s %-8s %-8s %s\n" % (p, e, k, k))
        open(ld + "/%s.plain.log" % p, "w").write("")
        open(ld + "/%s.%s.log" % (p, h0), "w").write("")
        v = "%s/%s/%s" % (e, k, k)
    rows.append([j["name"], j["kind"], "lane1", "2026-01-01T00:00:00Z", "100", "0", v, "5.0", "4.0", str(j["peak"]), "100"])
json.dump(jobs, open(d + "/jobs.json", "w"))
open(d + "/results.tsv", "w").write("".join("\t".join(r) + "\n" for r in rows))
open(d + "/progress.log", "w").write("00:00:00Z %d jobs; budget 50.0 GB\n00:59:00Z ALL DONE\n" % len(jobs))
open(d + "/env.txt", "w").write(
    "commit %s\nkani-tree %s\ncore-pin %s\nkani Kani Rust Verifier %s (cargo plugin)\nCBMC %s\ncbmc %s (cbmc-%s)\n"
    "host test host\nstarted 2026-01-01T00:00:00Z\n"
    % (git("rev-parse", "HEAD"), git("rev-parse", "HEAD:projects/shared-pool/kani"),
       git("rev-parse", "HEAD:projects/shared-pool/source-mirror"), K, C, C, C))
PY
}

# edit <file> <python statement on s, the file's text>
edit() {
  py -c "import re, sys; p = sys.argv[1]; s = open(p).read(); $2; open(p, 'w').write(s)" "$1"
}

# redigest <record dir>: provenance's digest of an edited jobs.tsv/covers.tsv.
redigest() {
  py -c "
import hashlib, re, sys
d = sys.argv[1]; h = hashlib.sha256()
for f in ('jobs.tsv', 'covers.tsv'): h.update(open(d + '/' + f, 'rb').read())
p = d + '/provenance.txt'; s = open(p).read()
open(p, 'w').write(re.sub(r'(?m)^digest\t.*$', 'digest\t' + h.hexdigest(), s))" "$1"
}

# expect <exit> <name> <output pattern or ""> <command...>
expect() {
  local want=$1 name=$2 pat=$3 got
  shift 3
  "$@" >"$t/out" 2>&1
  got=$?
  [ "$got" -gt 1 ] && got=2
  if [ "$got" != "$want" ]; then
    echo "FAIL: $name: exit $got, want $want"; sed 's/^/  /' "$t/out"; fail=1
  elif [ -n "$pat" ] && ! grep -qE -- "$pat" "$t/out"; then
    echo "FAIL: $name: output lacks /$pat/"; sed 's/^/  /' "$t/out"; fail=1
  fi
}

begin='<!-- kani-local-record: begin (kani/local/record.py writes this block; do not edit) -->'
end='<!-- kani-local-record: end -->'
# run_record <run dir> <record dir> [RESULTS.md, default: one with an old block]
run_record() {
  local r=${3:-$t/rr.md}
  [ -n "${3:-}" ] || printf 'before\n%s\nold table\n%s\nafter\n' "$begin" "$end" >"$r"
  KANI_RECORD_DIR="$2" KANI_RESULTS_MD="$r" "$record" "$1"
}
# run_check <record dir> [workflow] [RESULTS.md, default: the record's own
# table in a block] [args...]
run_check() {
  local d=$1 w=${2:-$wf} r=${3:-}
  shift 3 2>/dev/null || shift $#
  if [ -z "$r" ]; then
    r="$t/auto.md"
    { echo "$begin"; KANI_RECORD_DIR="$d" "$record" table 2>/dev/null; echo "$end"; } >"$r"
  fi
  KANI_RECORD_DIR="$d" KANI_RECORD_WORKFLOW="$w" KANI_RESULTS_MD="$r" "$check" "$@"
}

# --- record.py ---------------------------------------------------------------
fixture "$t/run"
mkdir -p "$t/rec"
printf 'before\n<!-- kani-local-record: begin (stale) -->\nold table\n<!-- kani-local-record: end -->\nafter\n' >"$t/results.md"
expect 0 "a complete run records" "recorded [0-9]+ harnesses and [0-9]+ mutants" run_record "$t/run" "$t/rec" "$t/results.md"
for f in provenance.txt jobs.tsv covers.tsv; do
  [ -s "$t/rec/$f" ] || { echo "FAIL: record.py wrote no $f"; fail=1; }
done
grep -q '^| `h_wedge` | ok |' "$t/results.md" && grep -q '^after$' "$t/results.md" && ! grep -q 'old table' "$t/results.md" ||
  { echo "FAIL: record.py did not rewrite the RESULTS.md block"; sed 's/^/  /' "$t/results.md"; fail=1; }
expect 0 "the new record passes" "local Kani record ok" run_check "$t/rec" "$wf" "$t/results.md"
cp -R "$t/rec" "$t/good"

refuse() { # refuse <name> <pattern> <python edit of the run> [file in the run]
  rm -rf "$t/bad" "$t/rec2"; cp -R "$t/run" "$t/bad"; cp -R "$t/good" "$t/rec2"
  edit "$t/bad/${4:-results.tsv}" "$3"
  expect 1 "$1" "$2" run_record "$t/bad" "$t/rec2"
  cmp -s "$t/good/jobs.tsv" "$t/rec2/jobs.tsv" || { echo "FAIL: $1: the record changed"; fail=1; }
}
refuse "incomplete run (a job still running)" "incomplete run: [0-9]+ of [0-9]+" "s = s.split('\n', 1)[1]"
refuse "no ALL DONE" "incomplete run" "s = s.replace('ALL DONE', 'start h_wedge')" progress.log
refuse "a harness out of time" "h_wedge: TIMEOUT, not ok" "s = re.sub(r'(?m)^(h_wedge\t.*\t0\t)ok\t', r'\1TIMEOUT\t', s)"
refuse "a harness's stdout disagrees" "h_wedge: FAILED in stdout.txt, not ok" "s = s.replace(' ok ', ' FAILED ')" logs/h_wedge/stdout.txt
refuse "run.sh exit 1" "h_wedge: run.sh exit 1" "s = re.sub(r'(?m)^(h_wedge\t(?:[^\t]*\t){4})0\t', r'\g<1>1\t', s)"
refuse "a mutant unexpected" "want killed/killed/killed" \
  "s = re.sub(r'(?m)^(25-\S+\s+killed\s+killed\s+)killed\s*$', r'\1survived  <-- UNEXPECTED', s)" logs/mutant-25/stdout.txt
refuse "foreign kani tree" "kani-tree" "s = re.sub(r'(?m)^kani-tree .*$', 'kani-tree ' + '0' * 40, s)" env.txt
refuse "other Kani version" "is not Kani" "s = re.sub(r'(?m)^kani .*$', 'kani Kani Rust Verifier 0.0.1 (cargo plugin)', s)" env.txt
refuse "other CBMC version" "is not CBMC" "s = re.sub(r'(?m)^cbmc .*$', 'cbmc 1.0.0 (cbmc-1.0.0)', s)" env.txt
refuse "unknown commit" "not in this repository" "s = re.sub(r'(?m)^commit .*$', 'commit ' + 'f' * 40, s)" env.txt
# A mutant whose Kani leg left no log is not recorded from its header.
rm -rf "$t/bad" "$t/rec2"; cp -R "$t/run" "$t/bad"; cp -R "$t/good" "$t/rec2"
find "$t/bad/logs/mutant-25" -name '25-*.h_*.log' -exec rm {} +
expect 1 "a mutant without its Kani log" "mutant-25 .*no log of its Kani leg" run_record "$t/bad" "$t/rec2"
cmp -s "$t/good/jobs.tsv" "$t/rec2/jobs.tsv" || { echo "FAIL: a mutant without its Kani log: the record changed"; fail=1; }
# RESULTS.md without the block: refused, nothing written.
printf 'no block here\n' >"$t/noblock.md"
expect 1 "RESULTS.md without a block" "has no local-record block" run_record "$t/run" "$t/rec2" "$t/noblock.md"
cmp -s "$t/good/jobs.tsv" "$t/rec2/jobs.tsv" && [ "$(cat "$t/noblock.md")" = "no block here" ] ||
  { echo "FAIL: RESULTS.md without a block: the record or RESULTS.md changed"; fail=1; }
# Complete and ok, but not the workflow's large jobs: the check refuses it.
rm -rf "$t/bad" "$t/rec2"; cp -R "$t/run" "$t/bad"; cp -R "$t/good" "$t/rec2"
edit "$t/bad/results.tsv" "s = re.sub(r'(?m)^h_wedge\t.*\n', '', s)"
edit "$t/bad/jobs.json" "import json; s = json.dumps([j for j in json.loads(s) if j['name'] != 'h_wedge'])"
expect 1 "a run without one large harness" "h_wedge" run_record "$t/bad" "$t/rec2"
cmp -s "$t/good/jobs.tsv" "$t/rec2/jobs.tsv" || { echo "FAIL: a run without h_wedge: the record changed"; fail=1; }
expect 1 "a missing run directory" "no env.txt" run_record "$t/nowhere" "$t/rec2"

# --- check-kani-record.py ----------------------------------------------------
bad() { rm -rf "$t/r"; cp -R "$t/good" "$t/r"; }
expect 1 "no record" "no local Kani record" run_check "$t/empty"

# Commits with other Kani inputs, in the scratch object directory: HEAD plus
# kani/.cargo/config.toml (a new file, which can set rustflags), HEAD plus a
# .cargo/config.toml at the repository's root (above kani/, which cargo also
# reads), HEAD with kani/run.sh changed, and HEAD with only the Markdown and
# kani/local changed. at <commit> <command...>: the check compares with that
# commit.
objs="$t/objects"; mkdir -p "$objs"
alt="$(cd "$root" && cd "$(git rev-parse --git-common-dir)" && pwd)/objects"
sgit() {
  GIT_OBJECT_DIRECTORY="$objs" GIT_ALTERNATE_OBJECT_DIRECTORIES="$alt" GIT_INDEX_FILE="$t/index" \
    GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@example.invalid GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@example.invalid \
    git -C "$root" "$@"
}
commit_with() { # commit_with <path> <content> [<path> <content>...]: its id
  local b
  sgit read-tree HEAD || return 1
  while [ $# -ge 2 ]; do
    b=$(printf '%s\n' "$2" | sgit hash-object -w --stdin) && sgit update-index --add --cacheinfo "100644,$b,$1" || return 1
    shift 2
  done
  sgit commit-tree "$(sgit write-tree)" -p HEAD -m test
}
at() { local rev=$1; shift; KANI_RECORD_REV=$rev GIT_OBJECT_DIRECTORY=$objs GIT_ALTERNATE_OBJECT_DIRECTORIES=$alt "$@"; }
k=projects/shared-pool/kani
c_cfg=$(commit_with "$k/.cargo/config.toml" '[build]
rustflags = ["-C", "overflow-checks=off"]')
c_root=$(commit_with ".cargo/config.toml" '[profile.dev]
overflow-checks = false')
c_run=$(commit_with "$k/run.sh" "$(git -C "$root" show "HEAD:$k/run.sh")
# changed")
c_doc=$(commit_with "$k/RESULTS.md" "$(git -C "$root" show "HEAD:$k/RESULTS.md")
more prose" "$k/local/provenance.txt" "another record")
if [ -z "$c_cfg" ] || [ -z "$c_root" ] || [ -z "$c_run" ] || [ -z "$c_doc" ] ||
   [ -n "$(git -C "$root" cat-file -t "$c_cfg" 2>/dev/null)" ]; then
  echo "FAIL: could not make the scratch commits (or they reached the repository's objects)"; fail=1
fi
cfg_changed='kani/\(all but local, \*\.md\) changed \(projects/shared-pool/kani/\.cargo/config\.toml\)'
expect 1 "a new file under kani/ (.cargo/config.toml): stale" "$cfg_changed; nothing in this run verifies.*re-run the local Kani record" \
  at "$c_cfg" run_check "$t/good"
expect 0 "stale with --stale-ok (kani-large and kani-mutants-large run)" "warning: .*$cfg_changed.*re-run the local Kani record" \
  at "$c_cfg" run_check "$t/good" "" "" --stale-ok
expect 0 "stale with --stale-ok-harnesses --stale-ok-mutants" "warning: .*$cfg_changed" \
  at "$c_cfg" run_check "$t/good" "" "" --stale-ok-harnesses --stale-ok-mutants
expect 1 "stale with --stale-ok-harnesses only (no kani-mutants-large)" "verifies its [0-9]+ mutants \(no kani-mutants-large jobs\);.*a manual run with .kani. and .mutants. verifies them" \
  at "$c_cfg" run_check "$t/good" "" "" --stale-ok-harnesses
expect 1 "stale with --stale-ok-mutants only (no kani-large)" "verifies its [0-9]+ harnesses \(no kani-large jobs\);" \
  at "$c_cfg" run_check "$t/good" "" "" --stale-ok-mutants
expect 1 "a .cargo/config.toml at the root (above kani/): stale" '\.cargo/config\[\.toml\] above kani/ \(the root, projects, projects/shared-pool\) changed \(\.cargo/config\.toml\)' \
  at "$c_root" run_check "$t/good"
[ "$(at "$c_root" "$check" cargo-configs "$c_root")" = .cargo/config.toml ] && [ -z "$("$check" cargo-configs HEAD)" ] ||
  { echo "FAIL: cargo-configs: not the commit's .cargo/config[.toml] above kani/"; fail=1; }
expect 1 "kani/run.sh changed: stale" "kani/run.sh, projects/shared-pool/kani/\(all but local, \*\.md\) changed \(projects/shared-pool/kani/run\.sh\)" \
  at "$c_run" run_check "$t/good"
expect 0 "only the Markdown and kani/local changed: current" "local Kani record ok: .*fingerprint [0-9a-f]{12};" \
  at "$c_doc" run_check "$t/good"
expect 2 "an unknown flag" "" run_check "$t/good" "" "" --stale-ok-everything

# Provenance that is not its commit's: HEAD's input lines and fingerprint
# under another commit, and input lines changed with a recomputed
# fingerprint. A commit this clone lacks (a shallow checkout) is skipped.
bad; edit "$t/r/provenance.txt" "s = re.sub(r'(?m)^commit\t.*$', 'commit\t$c_cfg', s)"
expect 1 "another commit's provenance" "the fingerprint is not commit [0-9a-f]{12}'s" at HEAD run_check "$t/r"
bad; edit "$t/r/provenance.txt" "s = re.sub(r'(?m)^(input\tprojects/shared-pool/kani/run.sh\t).*$', r'\g<1>' + '1' * 40, s)"
py -c "
import hashlib, re, sys
p = sys.argv[1]; s = open(p).read()
lines = re.findall(r'(?m)^input\t(.*)$', s)
fp = hashlib.sha256(''.join(l + '\n' for l in lines).encode()).hexdigest()
open(p, 'w').write(re.sub(r'(?m)^fingerprint\t.*$', 'fingerprint\t' + fp, s))" "$t/r/provenance.txt"
expect 1 "input lines changed and re-hashed by hand" "the fingerprint is not commit [0-9a-f]{12}'s" run_check "$t/r"
bad; edit "$t/r/provenance.txt" "s = re.sub(r'(?m)^commit\t.*$', 'commit\t' + 'e' * 40, s)"
expect 0 "a commit this clone lacks (shallow checkout)" "local Kani record ok: commit eeeeeeeeeeee" run_check "$t/r"
bad; edit "$t/r/provenance.txt" "s = re.sub(r'(?m)^commit\t.*$', 'commit\tHEAD', s)"
expect 1 "a commit that is not a full id" "commit 'HEAD' is not a full commit id" run_check "$t/r"
bad; edit "$t/r/provenance.txt" "s = re.sub(r'(?m)^(input\ttools/versions.env:CBMC\t).*$', r'\g<1>9.9.9', s)"
expect 1 "fingerprint edited by hand" "not the hash of its input lines" run_check "$t/r"
bad; edit "$t/r/jobs.tsv" "s = s.replace('\th_wedge\tok\t', '\th_wedge\tFAILED\t')"
expect 1 "results edited by hand" "not what record.py wrote" run_check "$t/r"
redigest "$t/r"
expect 1 "a recorded harness not ok" "recorded harness h_wedge: FAILED, not ok" run_check "$t/r"
bad; edit "$t/r/jobs.tsv" "s = re.sub(r'(?m)^(mutant\t25-\S+\t)killed/killed/killed', r'\1killed/killed/survived', s)"
redigest "$t/r"
expect 1 "a recorded mutant not as expected" "recorded mutant 25-.*killed/killed/survived, not killed/killed/killed" run_check "$t/r"
bad; edit "$t/r/jobs.tsv" "s = re.sub(r'(?m)^harness\th_wedge\t.*\n', '', s)"; redigest "$t/r"
expect 1 "a large harness missing from the record" "only in kani-large: h_wedge" run_check "$t/r"
bad; edit "$t/r/covers.tsv" "s = s + 'fam\tcover\tSATISFIED\th_nobody\n'"; redigest "$t/r"
expect 1 "a cover of no recorded harness" "h_nobody, which is not a recorded harness" run_check "$t/r"

w() { cp "$wf" "$t/wf.yml"; edit "$t/wf.yml" "$1"; }
w "s = s.replace('\"h_canary h_full_256 ', '\"h_canary h_wedge h_full_256 ', 1)"
expect 1 "a recorded harness also in a kani group" "in a kani group and in the local record: h_wedge" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('\"h_canary h_full_256 ', '\"h_full_256 ', 1)"
expect 1 "a harness in no group nor the record" "in no kani group and not in the local record: h_canary" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('\"h_canary h_full_256 ', '\"h_canary h_canary h_full_256 ', 1)"
expect 1 "a harness in two kani groups" "in two kani groups: h_canary" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('\"h_canary h_full_256 ', '\"h_canary h_nonesuch h_full_256 ', 1)"
expect 1 "not a harness of run.sh" "not harnesses of run.sh list: h_nonesuch" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('h_wedge_healthy\", gb: 11,', 'h_wedge_healthy\", gb: 14,', 1)"
expect 1 "a kani group above 13 GB" "peaked at 14 GB, above 13 GB" run_check "$t/good" "$t/wf.yml"
w "s = re.sub(r'(?m)^ *- \{ group: \"h_wedge\", gb: 39, timeout: 1800 \}\n', '', s)"
expect 1 "kani-large without a recorded group" "only recorded: h_wedge" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('- { mutant: \"02\", gb: 5, timeout: 1800 }', '- { mutant: \"02\", gb: 5, timeout: 1800 }\n          - { mutant: \"25\", gb: 19, timeout: 5100 }', 1)"
expect 1 "a recorded mutant also in kani-mutants" "mutants in kani-mutants and in the local record: 25-" run_check "$t/good" "$t/wf.yml"
w "s = re.sub(r'(?m)^ *- \{ mutant: \"02\", gb: 5, timeout: 1800 \}\n', '', s, count=1)"
expect 1 "a mutant in neither" "in neither kani-mutants nor the local record: 02-" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('- { mutant: \"02\", gb: 5, timeout: 1800 }', '- { mutant: \"99\", gb: 5, timeout: 1800 }', 1)"
expect 1 "a mutant entry with no patch" "entry 99: matches 0 mutants" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('- { mutant: \"02\", gb: 5, timeout: 1800 }', '- { mutant: \"02\", gb: 5 }', 1)"
expect 1 "a matrix entry in another form" "a matrix entry must read" run_check "$t/good" "$t/wf.yml"
w "s = s.replace('  kani-large:', '  kani-huge:', 1)"
expect 1 "no kani-large job" "no matrix entries for the kani-large job" run_check "$t/good" "$t/wf.yml"

expect 0 "RESULTS.md block current" "" run_check "$t/good" "$wf" "$t/results.md"
cp "$t/results.md" "$t/stale.md"; edit "$t/stale.md" "s = s.replace('| \`h_wedge\` | ok |', '| \`h_wedge\` | ok?? |')"
expect 1 "RESULTS.md block stale" "not the record's table" run_check "$t/good" "$wf" "$t/stale.md"
expect 1 "RESULTS.md without the block" "has no local-record block" run_check "$t/good" "$wf" "$t/noblock.md"
expect 1 "no RESULTS.md" "none.md does not exist" run_check "$t/good" "$wf" "$t/none.md"

# Subcommands the covers job uses.
want=$("$check" matrix kani-large | cut -f1 | tr ' ' '\n' | sort)
got=$(KANI_RECORD_DIR="$t/good" "$check" harnesses | sort)
[ "$got" = "$want" ] || { echo "FAIL: harnesses: not kani-large's harnesses"; fail=1; }
KANI_RECORD_DIR="$t/good" "$check" covers >"$t/covers.tsv"
awk -F'\t' 'NF != 3 {bad=1} END {exit bad}' "$t/covers.tsv" && [ "$(wc -l <"$t/covers.tsv")" -eq "$(echo "$want" | wc -l)" ] &&
  "$here/check-covers.sh" "$t/covers.tsv" >/dev/null ||
  { echo "FAIL: covers: not run.sh's covers.tsv format, or check-covers.sh rejects it"; fail=1; }

# The fingerprint: each named input's git object id, the kani/ tree less
# local/ and the Markdown, the .cargo/config[.toml] files above kani/ (none,
# then one), and versions.env's KANI and CBMC, in a repository with only
# those paths. One input changed changes its line(s) and the fingerprint
# only; a new file under kani/ changes the kani/ line; the Markdown and
# kani/local change nothing.
g="$t/repo"
mkdir -p "$g/projects/shared-pool/kani/src" "$g/projects/shared-pool/kani/mutants" "$g/projects/shared-pool/conformance/traces" "$g/tools"
( cd "$g" && git init -q && git config user.email t@example.invalid && git config user.name t &&
  echo a >projects/shared-pool/kani/src/lib.rs && echo m >projects/shared-pool/kani/mutants/01-x.patch &&
  echo r >projects/shared-pool/kani/run.sh && echo c >projects/shared-pool/kani/Cargo.toml &&
  echo l >projects/shared-pool/kani/Cargo.lock && echo /target >projects/shared-pool/kani/.gitignore && echo t >projects/shared-pool/conformance/traces/core.txt &&
  echo results >projects/shared-pool/kani/RESULTS.md &&
  printf 'RUST_TOOLCHAIN=1\nKANI=0.68.0\nCBMC=6.11.0\n' >tools/versions.env &&
  git add -A && git update-index --add --cacheinfo "160000,$(printf '%040d' 1),projects/shared-pool/source-mirror" &&
  git commit -qm one && echo r2 >projects/shared-pool/kani/run.sh && git commit -qm two projects/shared-pool/kani/run.sh &&
  sed -i.bak 's/^KANI=.*/KANI=0.69.0/' tools/versions.env && rm tools/versions.env.bak && git commit -qm three tools/versions.env &&
  mkdir projects/shared-pool/kani/.cargo && echo '[build]' >projects/shared-pool/kani/.cargo/config.toml &&
  git add projects/shared-pool/kani/.cargo && git commit -qm four &&
  echo more >>projects/shared-pool/kani/RESULTS.md && mkdir projects/shared-pool/kani/local &&
  echo record >projects/shared-pool/kani/local/provenance.txt && git add projects/shared-pool/kani && git commit -qm five &&
  mkdir projects/shared-pool/.cargo && echo '[build]' >projects/shared-pool/.cargo/config &&
  git add projects/shared-pool/.cargo && git commit -qm six ) ||
  { echo "FAIL: could not build the fingerprint repository"; fail=1; }
fp() { KANI_RECORD_ROOT="$g" "$check" fingerprint "$1"; }
changed() { diff <(fp "$1") <(fp "$2") | grep '^>' | cut -f1 | tr '\n' ' '; }
all='projects/shared-pool/kani/(all but local, *.md)'
cargo='.cargo/config[.toml] above kani/ (the root, projects, projects/shared-pool)'
tab=$(printf '\t')
if [ "$(changed HEAD~5 HEAD~4)" != "> projects/shared-pool/kani/run.sh > $all > fingerprint " ] ||
   [ "$(changed HEAD~4 HEAD~3)" != "> tools/versions.env:KANI > fingerprint " ] ||
   [ "$(changed HEAD~3 HEAD~2)" != "> $all > fingerprint " ] || [ -n "$(changed HEAD~2 HEAD~1)" ] ||
   [ "$(changed HEAD~1 HEAD)" != "> $cargo > fingerprint " ] ||
   [ "$(fp HEAD~5 | grep -c .)" != 13 ] || ! fp HEAD~1 | grep -qxF "$cargo${tab}none" ||
   ! fp HEAD | grep -qx "projects/shared-pool/source-mirror$tab$(printf '%040d' 1)"; then
  echo "FAIL: fingerprint: one changed input must change its line(s) and the fingerprint only"
  for n in 5 4 3 2 1; do echo "  HEAD~$n to HEAD~$((n - 1)): $(changed "HEAD~$n" "HEAD~$((n - 1))")"; done
  fp HEAD~5 | sed 's/^/  /'; fail=1
fi
expect 1 "fingerprint of a missing input" "is not in the repository" env KANI_RECORD_ROOT="$t" "$check" fingerprint HEAD

[ "$fail" = 0 ] && echo "check-kani-record: all cases pass"
exit "$fail"
