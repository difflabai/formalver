#!/usr/bin/env bash
# Self-test for check-kani-record.py, kani/local/record.py and
# run-local.py's environment and cargo configuration checks: a synthetic
# finished local run of the kani-large and kani-mutants-large jobs (at HEAD)
# records and passes the check; an incomplete, failed, foreign or
# measurement run is refused and leaves the record alone; and each kind of
# stale, wrong or inconsistent record, each workflow matrix that does not
# split the harnesses and mutants with the record, and each large timeout
# below the limit the record ran it under, fails the check. Commits with
# other Kani inputs are made in a scratch object directory over the
# repository's (no object, ref or index of the repository is written).
# Also kani/local/run-local.py's job lists (the record's, and --all's
# measurement of every harness and mutant), --all's refusals and its
# heavy-job lock (a scratch one), without running a job.
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
# A measurement (run-local.py --all) is not a record's run.
rm -rf "$t/bad" "$t/rec2"; cp -R "$t/run" "$t/bad"; cp -R "$t/good" "$t/rec2"
echo 'mode measurement (run-local.py --all: every harness of run.sh list and every mutant; not a record)' >>"$t/bad/env.txt"
expect 1 "a measurement (run-local.py --all)" "is a measurement \(run-local\.py --all" run_record "$t/bad" "$t/rec2"
cmp -s "$t/good/jobs.tsv" "$t/rec2/jobs.tsv" || { echo "FAIL: a measurement: the record changed"; fail=1; }

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
# Timeouts: a large entry's may not drop below the limit_s its recorded
# run used (the record shows a pass within that, not within less); a
# higher one is fine; under the job's --stale-ok flag (the job runs) a
# lower one is a warning.
w "s = s.replace('{ group: \"h_wedge\", gb: 39, timeout: 1800 }', '{ group: \"h_wedge\", gb: 39, timeout: 600 }', 1)"
expect 1 "a kani-large timeout below the recorded limit" \
  "error: kani-large entry 'h_wedge': timeout 600 is below the 1800 s the local record ran h_wedge under; the record does not show that it passes in 600 s: raise it back to 1800 or more, or re-run the local Kani record" \
  run_check "$t/good" "$t/wf.yml"
expect 0 "... with --stale-ok-harnesses: a warning" \
  "warning: kani-large entry 'h_wedge': timeout 600 is below the 1800 s .*this run's kani-large job verifies it in 600 s" \
  run_check "$t/good" "$t/wf.yml" "" --stale-ok-harnesses
w "s = s.replace('\"h_init h_validate\", gb: 27, timeout: 2400 }', '\"h_init h_validate\", gb: 27, timeout: 2399 }', 1)"
expect 1 "a two-harness kani-large group 1 s below the recorded limit" \
  "kani-large entry 'h_init h_validate': timeout 2399 is below the 2400 s the local record ran h_init, h_validate under; the record does not show that they pass" \
  run_check "$t/good" "$t/wf.yml"
w "s = s.replace('{ mutant: \"25\", gb: 19, timeout: 5100 }', '{ mutant: \"25\", gb: 19, timeout: 1800 }', 1)"
expect 1 "a kani-mutants-large timeout below the recorded limit" \
  "error: kani-mutants-large entry '25': timeout 1800 is below the 5100 s the local record ran 25-[a-z-]+ under" \
  run_check "$t/good" "$t/wf.yml"
expect 1 "... with --stale-ok-harnesses only (no kani-mutants-large)" "error: kani-mutants-large entry '25': timeout 1800" \
  run_check "$t/good" "$t/wf.yml" "" --stale-ok-harnesses
expect 0 "... with --stale-ok-mutants: a warning" "warning: kani-mutants-large entry '25': timeout 1800 .*verifies it in 1800 s" \
  run_check "$t/good" "$t/wf.yml" "" --stale-ok-mutants
w "s = s.replace('{ group: \"h_wedge\", gb: 39, timeout: 1800 }', '{ group: \"h_wedge\", gb: 39, timeout: 3600 }', 1).replace('{ mutant: \"25\", gb: 19, timeout: 5100 }', '{ mutant: \"25\", gb: 19, timeout: 7200 }', 1)"
expect 0 "large timeouts raised above the recorded limits" "local Kani record ok" run_check "$t/good" "$t/wf.yml"
grep -q '^warning: kani-' "$t/out" && { echo "FAIL: large timeouts raised: a timeout warning"; sed 's/^/  /' "$t/out"; fail=1; }
bad; edit "$t/r/jobs.tsv" "s = re.sub(r'(?m)^(harness\th_wedge\t(?:[^\t]*\t){5})1800\t', r'\g<1>30m\t', s)"; redigest "$t/r"
expect 1 "a recorded limit_s that is not whole seconds" "recorded harness h_wedge: limit_s '30m' is not a whole number of seconds" \
  run_check "$t/r"

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

# --- run-local.py's refusals (--dry-run checks as a run does) ---------------
# The environment, and the cargo configuration outside the lanes (CARGO_HOME
# here, and a .cargo/ above the run directory), parsed as TOML: every
# spelling of rustflags, rustc or a wrapper, a profile, or an include is
# refused, and so is a file that does not parse; other settings are not.
runlocal="$root/projects/shared-pool/kani/local/run-local.py"
mkdir -p "$t/ch" "$t/tmpdir" "$t/above/.cargo"
dry() { # dry <run dir> [VAR=value...]: a dry run in a clean environment
  local out=$1; shift
  env -i PATH="$PATH" HOME="$HOME" CARGO_HOME="$t/ch" TMPDIR="$t/tmpdir" "$@" python3 -I "$runlocal" --dry-run --out "$out"
}
ok_dry='^commit [0-9a-f]{12}; [0-9]+ jobs'
cfg() { printf '%s\n' "$2" >"$t/ch/$1"; }
expect 0 "run-local.py: no cargo configuration" "$ok_dry" dry "$t/lr"
while IFS='|' read -r name keys text; do
  cfg config.toml "$(printf '%b' "$text")"
  expect 1 "run-local.py: $name" "ch/config\.toml \($keys\) set rustflags, rustc or a wrapper, a profile or an include" \
    dry "$t/lr"
done <<'CASES'
a quoted key in [build]|build\.rustflags|[build]\n"rustflags" = ["-C", "overflow-checks=off"]
a dotted key|build\.rustflags|build.rustflags = ["-C", "overflow-checks=off"]
an inline table|build\.rustflags|build = { rustflags = ["-C", "overflow-checks=off"] }
a target's rustflags|target\."cfg\(unix\)"\.rustflags|[target.'cfg(unix)']\nrustflags = ["-C", "overflow-checks=off"]
a quoted rustc-wrapper|build\.rustc-wrapper|[build]\n'rustc-wrapper' = "sccache"
build.rustc|build\.rustc|[build]\nrustc = "/somewhere/rustc"
a dotted profile key|profile|profile.dev.opt-level = 0
a profile table|profile|[profile.release]\noverflow-checks = false
an include|include|include = "other.toml"
CASES
cfg config.toml '[build'
expect 1 "run-local.py: a cargo configuration that does not parse" "unparsable cargo configuration .*ch/config\.toml" dry "$t/lr"
cfg config.toml '[net]
offline = true
[build]
jobs = 2
[env]
RUST_LOG = "rustflags"'
expect 0 "run-local.py: other cargo settings" "$ok_dry" dry "$t/lr"
rm "$t/ch/config.toml"; cfg config '[build]
"rustflags" = ["-C", "overflow-checks=off"]'
expect 1 "run-local.py: CARGO_HOME/config (no .toml)" "ch/config \(build\.rustflags\) set" dry "$t/lr"
rm "$t/ch/config"; printf '[profile.dev]\noverflow-checks = false\n' >"$t/above/.cargo/config.toml"
expect 1 "run-local.py: a .cargo/config.toml above the run directory" "above/\.cargo/config\.toml \(profile\) set" \
  dry "$t/above/lr"
expect 0 "run-local.py: ... not above another run directory" "$ok_dry" dry "$t/lr"
expect 1 "run-local.py: RUSTFLAGS in the environment" "RUSTFLAGS set in the environment" dry "$t/lr" RUSTFLAGS=-Coverflow-checks=off

# --- run-local.py's jobs and --all -------------------------------------------
# The record's jobs are the large matrix entries. --all, a measurement,
# runs every harness of run.sh list and every mutant, each once, with an
# estimate and its source; it is not a record, writes outside the
# repository, and holds the machine's heavy-job lock while it runs (here a
# lock in $t: KANI_CBMC=/usr/bin/false fails the tool check after it is
# taken, so no job starts). A run in the background is a plain command, so
# that $! is run-local.py's pid (a shell function would run in a subshell,
# which the test's signal would stop instead).
kd="$root/projects/shared-pool/kani"
names() { awk '/^  [^ ]/ {print $1}' "$t/out" | sort; }
clean_env=(env -i PATH="$PATH" HOME="$HOME" TMPDIR="$t" SP_HEAVY_LOCK="$t/lock" KANI_CBMC=/usr/bin/false)
clean() { "${clean_env[@]}" "$@"; }
expect 0 "run-local.py --dry-run" "jobs \(KANI_TIMEOUT" py "$runlocal" --dry-run
want=$( { "$check" matrix kani-large | cut -f1 | tr ' ' '\n'; "$check" matrix kani-mutants-large | cut -f1 | sed 's/^/mutant-/'; } | sort)
[ "$(names)" = "$want" ] || { echo "FAIL: run-local.py --dry-run: not the kani-large harnesses and kani-mutants-large mutants"; fail=1; }
expect 0 "run-local.py --all --dry-run" "measurement \(--all, not a record\)" py "$runlocal" --all --dry-run
want=$( { bash "$kd/run.sh" list; for p in "$kd"/mutants/*.patch; do p=${p##*/}; echo "mutant-${p%%-*}"; done; } | sort)
if [ "$(names)" != "$want" ] || [ -n "$(names | uniq -d)" ]; then
  echo "FAIL: run-local.py --all --dry-run: not each harness of run.sh list and each mutant exactly once"
  diff <(names) <(echo "$want") | sed 's/^/  /'; fail=1
fi
grep -E '^  [^ ]' "$t/out" | grep -vE ' s  (W7|v1\.0\.0 RESULTS\.md|RESULTS\.md at|killed-by|checked-by|unknown)' | grep -q . &&
  { echo "FAIL: run-local.py --all --dry-run: an estimate without its source"; fail=1; }
expect 2 "run-local.py --all --record" "a measurement, not a record: --record is refused" py "$runlocal" --all --record
expect 2 "run-local.py --only without --all" "--only needs --all" py "$runlocal" --only h_wedge --dry-run
expect 2 "run-local.py --all --only, not a job" "not a job of --all: h_nonesuch" py "$runlocal" --all --only h_wedge,h_nonesuch --dry-run
expect 0 "run-local.py --all --only" "2 jobs, 1 harnesses of run.sh list and 1 mutants" py "$runlocal" --all --only h_wedge,01 --dry-run
[ "$(names | tr '\n' ' ')" = "h_wedge mutant-01 " ] || { echo "FAIL: run-local.py --all --only h_wedge,01: $(names | tr '\n' ' ')"; fail=1; }
expect 1 "run-local.py --all, output in the repository" "is in the repository; a measurement is not a record" \
  clean python3 -I "$runlocal" --all --only h_full_256 --out "$kd/target/measure"
expect 1 "run-local.py --all, a failure with the lock held" "holding $t/lock" \
  clean python3 -I "$runlocal" --all --only h_full_256 --out "$t/measure"
grep -q "released $t/lock" "$t/out" && [ ! -e "$t/lock" ] && [ ! -e "$t/measure" ] ||
  { echo "FAIL: run-local.py --all: the lock not released on failure (or the run started)"; sed 's/^/  /' "$t/out"; fail=1; }
# Another process's lock: --all waits for it, and leaves it when stopped.
mkdir "$t/lock"
"${clean_env[@]}" python3 -I "$runlocal" --all --only h_full_256 --out "$t/measure" >"$t/wait.out" 2>&1 &
pid=$!
for _ in $(seq 40); do grep -q "waiting for $t/lock" "$t/wait.out" && break; sleep 0.25; done
kill -TERM "$pid" 2>/dev/null; wait "$pid"; rc=$?
[ "$rc" = 143 ] && grep -q "waiting for $t/lock" "$t/wait.out" && grep -q "stopped by signal 15" "$t/wait.out" &&
  [ -d "$t/lock" ] && ! grep -q "holding" "$t/wait.out" ||
  { echo "FAIL: run-local.py --all: did not wait for another's lock, or removed it (exit $rc)"; sed 's/^/  /' "$t/wait.out"; fail=1; }
rmdir "$t/lock"

# --all's scheduling: a job estimated at ALONE_GB or more starts only when
# no job runs, and none starts beside it, nor beside a running job whose
# sampled tree reached ALONE_GB; other jobs share the budget. The record
# (alone None) keeps the budget rule alone. The dry run says so.
expect 0 "run-local.py --all: a job of ALONE_GB or more runs alone" "^ok$" py - "$runlocal" <<'PY'
import importlib.util, sys
sys.dont_write_bytecode = True  # no __pycache__ in kani/local
spec = importlib.util.spec_from_file_location("run_local", sys.argv[1])
rl = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rl)
A = rl.ALONE_GB
def job(gb, secs=0):
    return {"peak": gb, "est": secs}
bad = [c for c, want in [
    ((job(40), [], 50, A), True),            # alone, it fits
    ((job(40), [3], 50, A), False),          # not beside a running job
    ((job(A), [3], 50, A), False),
    ((job(3), [40], 50, A), False),          # nothing beside it
    ((job(3), [A], 50, A), False),           # nor beside a tree that reached A
    ((job(A - 0.1), [3], 50, A), True),      # below A: the budget
    ((job(10), [39.9 - 10], 50, A), True),
    ((job(10), [30, 10.1], 50, A), False),
    ((job(10), [40], 50, None), True),       # the record: the budget only
    ((job(10.1), [40], 50, None), False),
] if rl.fits(*c) != want]
# 40 GB for 100 s, then the two small jobs together: 110 s (100 s beside it).
jobs = [job(40, 100), job(3, 10), job(3, 10)]
sim = (rl.simulate(jobs, 2, 50, A), rl.simulate(jobs, 2, 50, None))
print("ok" if not bad and sim == (110, 100) and A == 35 else "wrong: fits %s, simulate %s, ALONE_GB %s" % (bad, sim, A))
PY
expect 0 "run-local.py --all --dry-run: the alone line" "^alone \(estimated at 35 GB or more; no job beside them\): [0-9]+ jobs" \
  py "$runlocal" --all --dry-run

# A run whose jobs run, without Kani: stand-ins for cargo (cargo kani),
# rustc and CBMC, first on PATH and in run.sh's $HOME/.cargo/bin. Each job
# leaves a process in its group and one in a session of its own (run.sh
# says cargo-kani once started CBMC so; the group kill misses it). Stopped
# by SIGTERM, or failing on an exception (here progress.log turned into a
# directory), while a job runs, the run kills both and then releases the
# lock. Needs the source-mirror at the core pin for the lanes: CI's
# checkout has no submodule, so this is skipped there.
core=$(git -C "$root" rev-parse HEAD:projects/shared-pool/source-mirror)
if git -C "$root/projects/shared-pool/source-mirror" cat-file -e "$core^{commit}" 2>/dev/null; then
  fh="$t/fakehome"; fb="$t/fakehome/.cargo/bin"; pids="$t/pids"
  mkdir -p "$fb" "$pids"
  ver() { git -C "$root" show HEAD:tools/versions.env | sed -n "s/^$1=//p"; }
  printf '#!/bin/sh\necho "%s (stand-in)"\n' "$(ver CBMC)" >"$fb/cbmc"
  printf '#!/bin/sh\necho "rustc %s (stand-in)"\n' "$(ver RUST_TOOLCHAIN)" >"$fb/rustc"
  { echo '#!/usr/bin/env bash'
    echo "kv='$(ver KANI)' pids='$pids'"
    cat <<'SH'
case " $* " in
  *" --version "*) echo "cargo-kani $kv"; exit 0 ;;
  *" --only-codegen "*) exit 0 ;;
esac
prev=
for x in "$@"; do [ "$prev" = --harness ] && h=${x#*::}; prev=$x; done
if [ "$h" = h_step_ack_tx ] && [ -e "$pids/crash" ]; then
  # Once the other job runs: the scheduler's next log line raises.
  until [ -s "$pids/h_step_pause_tx.own" ]; do sleep 0.1; done
  out=$(dirname "$(dirname "$KANI_LOG_DIR")")
  rm "$out/progress.log"; mkdir "$out/progress.log"
  exit 1
fi
sleep 120 &
echo $! >"$pids/$h.group"
# Its pid file is written once it is in a session of its own.
python3 -c 'import os, sys, time; os.setsid(); open(sys.argv[1], "w").write(str(os.getpid())); time.sleep(120)' \
  "$pids/$h.own" &
wait
SH
  } >"$fb/cargo"
  chmod +x "$fb/cargo" "$fb/rustc" "$fb/cbmc"
  fake_env=(env -i PATH="$fb:$PATH" HOME="$fh" TMPDIR="$t" SP_HEAVY_LOCK="$t/lock" KANI_CBMC="$fb/cbmc")
  alive() { local s; s=$(ps -o stat= -p "$1" 2>/dev/null | tr -d ' '); [ -n "$s" ] && [ "${s#Z}" = "$s" ]; }
  # killed <harness>: its two processes are gone (within 5 s: reaped).
  killed() {
    local f p
    for f in group own; do
      [ -s "$pids/$1.$f" ] || return 1
      p=$(cat "$pids/$1.$f")
      for _ in $(seq 20); do alive "$p" || continue 2; sleep 0.25; done
      return 1
    done
  }
  # sweep: whatever a failed case left of the stand-ins' sleepers.
  sweep() {
    local f p
    for f in "$pids"/*.group "$pids"/*.own; do
      [ -s "$f" ] || continue
      p=$(cat "$f")
      ps -o command= -p "$p" 2>/dev/null | grep -q sleep && kill -KILL "$p" 2>/dev/null
    done
    rm -f "$pids"/*
  }
  "${fake_env[@]}" python3 -I "$runlocal" --all --only h_step_ack_tx --lanes 1 --out "$t/m1" >"$t/m1.out" 2>&1 &
  pid=$!
  for _ in $(seq 240); do [ -s "$pids/h_step_ack_tx.own" ] && break; kill -0 "$pid" 2>/dev/null || break; sleep 0.25; done
  kill -TERM "$pid" 2>/dev/null; wait "$pid"; rc=$?
  if [ "$rc" != 1 ] || ! grep -q "stopped by signal 15; not complete" "$t/m1.out" ||
     ! grep -q "released $t/lock" "$t/m1.out" || [ -e "$t/lock" ] || ! killed h_step_ack_tx; then
    echo "FAIL: run-local.py --all: SIGTERM with a job running: exit $rc, its processes or the lock left"
    sed 's/^/  /' "$t/m1.out"; ls "$pids" | sed 's/^/  pids: /'; fail=1
  fi
  sweep; rmdir "$t/lock" 2>/dev/null
  touch "$pids/crash"
  "${fake_env[@]}" python3 -I "$runlocal" --all --only h_step_ack_tx,h_step_pause_tx --lanes 2 --out "$t/m2" \
    >"$t/m2.out" 2>&1 &
  pid=$!
  for _ in $(seq 240); do kill -0 "$pid" 2>/dev/null || break; sleep 0.25; done
  kill -0 "$pid" 2>/dev/null && kill -TERM "$pid"
  wait "$pid"; rc=$?
  if [ "$rc" != 1 ] || ! grep -q "^Traceback" "$t/m2.out" || ! grep -q "released $t/lock" "$t/m2.out" ||
     [ -e "$t/lock" ] || ! killed h_step_pause_tx; then
    echo "FAIL: run-local.py --all: an exception with a job running: exit $rc, its processes or the lock left"
    sed 's/^/  /' "$t/m2.out"; ls "$pids" | sed 's/^/  pids: /'; fail=1
  fi
  sweep; rmdir "$t/lock" 2>/dev/null
else
  echo "skip: run-local.py --all with running jobs (no source-mirror at $core, as in CI's checkout)"
fi

[ "$fail" = 0 ] && echo "check-kani-record: all cases pass"
exit "$fail"
