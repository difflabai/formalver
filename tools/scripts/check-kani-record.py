#!/usr/bin/env python3
"""shared-pool's local Kani record (projects/shared-pool/kani/local): CI's check.

The Kani harnesses and mutants whose measured peak is above what a hosted
runner holds in memory (the kani-large and kani-mutants-large jobs of
.github/workflows/shared-pool.yml) run on a local machine
(kani/local/run-local.py), and kani/local/record.py records the run. Without
KANI_RUNNER, CI runs only the rest (the kani and kani-mutants jobs) and
checks the record instead of re-running the large part:

  check-kani-record.py [--stale-ok]
      fails unless
      - the record's fingerprint of the Kani inputs (INPUT_PATHS' git object
        ids at HEAD, versions.env's KANI and CBMC) is this commit's
        ("re-run the local Kani record: ..."; --stale-ok: a warning, for a
        run whose kani-large jobs verified the large part on KANI_RUNNER);
      - every recorded harness is ok and every recorded mutant as its patch
        expects (killed/killed/killed; survive/survived/survived for a
        `# must-survive` patch), its results and covers unedited (digest);
      - the recorded harnesses plus the kani job's groups are `run.sh list`,
        each exactly once, and the kani-large groups are the recorded
        harnesses; the same for mutants/*.patch with the recorded mutants,
        kani-mutants and kani-mutants-large;
      - every kani and kani-mutants entry peaked at IN_MEMORY_GB or less;
      - RESULTS.md's local-record block, if it has one, is
        `record.py table`.
  check-kani-record.py fingerprint [REV]   the inputs and fingerprint at REV
                                           (default HEAD), as record.py
                                           writes them
  check-kani-record.py matrix JOB          JOB's matrix entries in the
                                           workflow (name, gb, timeout)
  check-kani-record.py harnesses           the recorded harnesses
  check-kani-record.py covers              the recorded covers, in run.sh's
                                           covers.tsv format (for
                                           check-covers.sh)

The fingerprint reads git objects only, so it works in a shallow checkout
without the source-mirror submodule (the gitlink is the core's commit).
Lists (run.sh list, mutants/*.patch, the workflow) are read from the work
tree; in CI that is HEAD.

env: KANI_RECORD_DIR (default projects/shared-pool/kani/local),
     KANI_RECORD_WORKFLOW (default .github/workflows/shared-pool.yml),
     KANI_RESULTS_MD (default projects/shared-pool/kani/RESULTS.md),
     KANI_RECORD_ROOT (the repository; default this script's).
Exit 0 iff every check passes; 2 on a usage error.
"""
import hashlib
import os
import re
import subprocess
import sys

ROOT = os.environ.get("KANI_RECORD_ROOT") or os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
SP = "projects/shared-pool"
RECORD = os.environ.get("KANI_RECORD_DIR") or os.path.join(ROOT, SP, "kani/local")
WORKFLOW = os.environ.get("KANI_RECORD_WORKFLOW") or os.path.join(ROOT, ".github/workflows/shared-pool.yml")
RESULTS_MD = os.environ.get("KANI_RESULTS_MD") or os.path.join(ROOT, SP, "kani/RESULTS.md")
RECORD_PY = os.path.join(ROOT, SP, "kani/local/record.py")

# What a Kani verdict depends on: the harnesses and their runner, the
# mutants, the pinned core (a gitlink: its commit id), the conformance traces
# plain mode replays (a mutant's plain verdict), and the tool versions; and
# kani/.gitignore, to be safe (the archive run-local.py runs from has it).
# Not the record itself (kani/local) or the Markdown; of versions.env, only
# KANI and CBMC (the rest pins other layers' tools).
INPUT_PATHS = [
    SP + "/kani/src",
    SP + "/kani/Cargo.toml",
    SP + "/kani/Cargo.lock",
    SP + "/kani/mutants",
    SP + "/kani/run.sh",
    SP + "/kani/.gitignore",
    SP + "/source-mirror",
    SP + "/conformance/traces/core.txt",
]
INPUT_VERSIONS = ["KANI", "CBMC"]  # tools/versions.env
# The kani and kani-mutants jobs run on ubuntu-latest (16 GB, 15.6 usable):
# their entries must have peaked at this or less (kani/RESULTS.md).
IN_MEMORY_GB = 13
JOBS_COLUMNS = ["kind", "name", "result", "seconds", "job_seconds", "cbmc_peak_gb",
                "tree_peak_gb", "limit_s", "covers", "kani_harnesses", "started_utc"]
COVERS_COLUMNS = ["family", "cover", "status", "harness"]
BEGIN = "<!-- kani-local-record: begin"
END = "<!-- kani-local-record: end -->"
RERUN = ("re-run the local Kani record: projects/shared-pool/kani/local/run-local.py --record "
         "(about 4 hours on a 64 GB machine; projects/shared-pool/kani/local/README.md), and commit kani/local")


class Fail(Exception):
    pass


def run(args, cwd=None):
    r = subprocess.run(args, capture_output=True, text=True, cwd=cwd)
    if r.returncode != 0:
        raise Fail("%s: exit %d: %s" % (" ".join(args), r.returncode, (r.stderr or r.stdout).strip()))
    return r.stdout


def fingerprint(rev="HEAD"):
    """[(name, value)], sha256 hex of their lines."""
    lines = []
    for p in INPUT_PATHS:
        r = subprocess.run(["git", "-C", ROOT, "rev-parse", "--verify", "-q", "%s:%s" % (rev, p)],
                           capture_output=True, text=True)
        if r.returncode != 0:
            raise Fail("%s:%s is not in the repository" % (rev, p))
        lines.append((p, r.stdout.strip()))
    env = run(["git", "-C", ROOT, "show", "%s:tools/versions.env" % rev])
    for k in INPUT_VERSIONS:
        m = re.search(r"^%s=(\S+)\s*$" % k, env, re.M)
        if not m:
            raise Fail("%s:tools/versions.env has no %s" % (rev, k))
        lines.append(("tools/versions.env:" + k, m.group(1)))
    return lines, digest_lines(lines)


def digest_lines(lines):
    return hashlib.sha256("".join("%s\t%s\n" % nv for nv in lines).encode()).hexdigest()


def digest_files(*paths):
    h = hashlib.sha256()
    for p in paths:
        with open(p, "rb") as f:
            h.update(f.read())
    return h.hexdigest()


ENTRY = re.compile(r'^\s*- \{ (group|mutant): "([^"]+)", gb: (\d+), timeout: (\d+) \}\s*$')


def matrices(path=None):
    """{job: [{kind, name, gb, timeout}]} from the workflow's matrix entries."""
    path = path or WORKFLOW
    out, in_jobs, job = {}, False, None
    with open(path) as f:
        for i, line in enumerate(f, 1):
            if line.rstrip() == "jobs:":
                in_jobs = True
                continue
            if not in_jobs:
                continue
            m = re.match(r"^  ([A-Za-z0-9_-]+):\s*$", line)
            if m:
                job = m.group(1)
                continue
            if job and re.match(r"^\s*- \{ *(group|mutant):", line):
                e = ENTRY.match(line)
                if not e:
                    raise Fail('%s:%d: a matrix entry must read - { group|mutant: "...", gb: N, timeout: N }'
                               % (path, i))
                out.setdefault(job, []).append(dict(kind=e.group(1), name=e.group(2),
                                                    gb=int(e.group(3)), timeout=int(e.group(4))))
    return out


def read_tsv(path, columns):
    with open(path) as f:
        rows = [l.rstrip("\n").split("\t") for l in f if l.strip()]
    if not rows or rows[0] != columns:
        raise Fail("%s: the header must be %s" % (path, "\\t".join(columns)))
    out = []
    for n, r in enumerate(rows[1:], 2):
        if len(r) != len(columns):
            raise Fail("%s:%d: %d fields, want %d" % (path, n, len(r), len(columns)))
        out.append(dict(zip(columns, r)))
    return out


def read_record(d=None):
    """provenance {key: value}, inputs [(name, value)], jobs, covers."""
    d = d or RECORD
    prov_path = os.path.join(d, "provenance.txt")
    if not os.path.exists(prov_path):
        raise Fail("no local Kani record in %s (provenance.txt): %s" % (os.path.relpath(d, ROOT), RERUN))
    prov, inputs = {}, []
    with open(prov_path) as f:
        for n, line in enumerate(f, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            parts = line.split("\t")
            if parts[0] == "input" and len(parts) == 3:
                inputs.append((parts[1], parts[2]))
            elif len(parts) == 2:
                prov[parts[0]] = parts[1]
            else:
                raise Fail("%s:%d: want key<TAB>value or input<TAB>name<TAB>value" % (prov_path, n))
    jobs = read_tsv(os.path.join(d, "jobs.tsv"), JOBS_COLUMNS)
    covers = read_tsv(os.path.join(d, "covers.tsv"), COVERS_COLUMNS)
    return prov, inputs, jobs, covers


def harness_list():
    out = run(["bash", os.path.join(ROOT, SP, "kani/run.sh"), "list"])
    return [h for h in out.split() if h]


def mutant_patches():
    d = os.path.join(ROOT, SP, "kani/mutants")
    return sorted(f[:-len(".patch")] for f in os.listdir(d) if f.endswith(".patch"))


def mutant_expected(name):
    """(expect, plain, kani) that run.sh prints for a mutant as its patch requires."""
    with open(os.path.join(ROOT, SP, "kani/mutants", name + ".patch")) as f:
        survive = any(l.rstrip("\n") == "# must-survive" for l in f)
    return ("survive", "survived", "survived") if survive else ("killed", "killed", "killed")


def dups(xs):
    seen, out = set(), []
    for x in xs:
        if x in seen and x not in out:
            out.append(x)
        seen.add(x)
    return out


def words(xs):
    return " ".join(sorted(xs))


def check(stale_ok):
    errs, warns, notes = [], [], []
    prov, inputs, jobs, covers = read_record()
    rec_h = [j["name"] for j in jobs if j["kind"] == "harness"]
    rec_m = [j["name"] for j in jobs if j["kind"] == "mutant"]

    # The record is what record.py wrote: its inputs hash to its
    # fingerprint, its results and covers to its digest.
    if prov.get("fingerprint") != digest_lines(inputs):
        errs.append("provenance.txt: the fingerprint is not the hash of its input lines (edited by hand?): "
                    "write the record with kani/local/record.py")
    if prov.get("digest") != digest_files(os.path.join(RECORD, "jobs.tsv"), os.path.join(RECORD, "covers.tsv")):
        errs.append("jobs.tsv or covers.tsv is not what record.py wrote (digest in provenance.txt): "
                    "write the record with kani/local/record.py")

    # Fingerprint: the record's inputs are this commit's.
    head, head_fp = fingerprint("HEAD")
    if prov.get("fingerprint") != head_fp:
        have = dict(inputs)
        changed = [n for n, v in head if have.get(n) != v] or ["the input list"]
        msg = ("the local Kani record (commit %s) is for other Kani inputs than this commit's: %s changed; %s"
               % (prov.get("commit", "?")[:12], ", ".join(changed), RERUN))
        (warns if stale_ok else errs).append(msg)
    dirty = subprocess.run(["git", "-C", ROOT, "diff", "--quiet", "HEAD", "--"] + INPUT_PATHS + ["tools/versions.env"],
                           capture_output=True)
    if dirty.returncode == 1:
        warns.append("uncommitted changes to the Kani inputs: the fingerprint is HEAD's and does not see them")

    # Results: every harness ok, every mutant as its patch expects.
    patches = mutant_patches()
    for j in jobs:
        if j["kind"] == "harness":
            want = "ok-FAILED" if j["name"] == "h_canary" else "ok"
            if j["result"] != want:
                errs.append("recorded harness %s: %s, not %s" % (j["name"], j["result"], want))
        elif j["kind"] == "mutant":
            if j["name"] not in patches:
                errs.append("recorded mutant %s: no mutants/%s.patch" % (j["name"], j["name"]))
                continue
            want = "/".join(mutant_expected(j["name"]))
            if j["result"] != want:
                errs.append("recorded mutant %s: expect/plain/kani %s, not %s" % (j["name"], j["result"], want))
        else:
            errs.append("jobs.tsv: kind %r of %s is neither harness nor mutant" % (j["kind"], j["name"]))
    for c in covers:
        if c["harness"] not in rec_h:
            errs.append("covers.tsv: a cover of %s, which is not a recorded harness" % c["harness"])

    # Harnesses: the kani groups and the record split run.sh list.
    wf = matrices()
    for job in ("kani", "kani-large", "kani-mutants", "kani-mutants-large"):
        if job not in wf:
            errs.append("%s: no matrix entries for the %s job" % (os.path.relpath(WORKFLOW, ROOT), job))
    want = harness_list()
    ci_h = [h for e in wf.get("kani", []) for h in e["name"].split()]
    large_h = [h for e in wf.get("kani-large", []) for h in e["name"].split()]
    for what, xs in (("in two kani groups", ci_h), ("recorded twice", rec_h), ("in two kani-large groups", large_h)):
        if dups(xs):
            errs.append("harnesses %s: %s" % (what, words(dups(xs))))
    both = set(ci_h) & set(rec_h)
    missing = set(want) - set(ci_h) - set(rec_h)
    extra = (set(ci_h) | set(rec_h)) - set(want)
    if both:
        errs.append("harnesses in a kani group and in the local record: %s" % words(both))
    if missing:
        errs.append("harnesses of run.sh list in no kani group and not in the local record: %s" % words(missing))
    if extra:
        errs.append("not harnesses of run.sh list: %s" % words(extra))
    if set(large_h) != set(rec_h):
        errs.append("the kani-large groups must be the recorded harnesses: only in kani-large: %s; only recorded: %s"
                    % (words(set(large_h) - set(rec_h)) or "-", words(set(rec_h) - set(large_h)) or "-"))

    # Mutants: kani-mutants and the record split mutants/*.patch.
    def resolve(job):
        out = []
        for e in wf.get(job, []):
            ms = [p for p in patches if p.startswith(e["name"] + "-")]
            if len(ms) != 1:
                errs.append("%s entry %s: matches %d mutants/*.patch, want 1" % (job, e["name"], len(ms)))
            out += ms
        return out
    ci_m, large_m = resolve("kani-mutants"), resolve("kani-mutants-large")
    for what, xs in (("in kani-mutants twice", ci_m), ("recorded twice", rec_m), ("in kani-mutants-large twice", large_m)):
        if dups(xs):
            errs.append("mutants %s: %s" % (what, words(dups(xs))))
    both = set(ci_m) & set(rec_m)
    missing = set(patches) - set(ci_m) - set(rec_m)
    if both:
        errs.append("mutants in kani-mutants and in the local record: %s" % words(both))
    if missing:
        errs.append("mutants/*.patch in neither kani-mutants nor the local record: %s" % words(missing))
    if set(large_m) != set(rec_m):
        errs.append("kani-mutants-large must be the recorded mutants: only in kani-mutants-large: %s; only recorded: %s"
                    % (words(set(large_m) - set(rec_m)) or "-", words(set(rec_m) - set(large_m)) or "-"))

    # The hosted jobs' entries fit the hosted runner in memory.
    for job in ("kani", "kani-mutants"):
        for e in wf.get(job, []):
            if e["gb"] > IN_MEMORY_GB:
                errs.append("%s entry %r peaked at %d GB, above %d GB: it does not fit ubuntu-latest in memory; "
                            "move it to %s-large and the local record" % (job, e["name"], e["gb"], IN_MEMORY_GB, job))

    # RESULTS.md's block, if any, is the record's table.
    if os.path.exists(RESULTS_MD):
        with open(RESULTS_MD) as f:
            text = f.read()
        if BEGIN in text:
            m = re.search(re.escape(BEGIN) + r"[^\n]*\n(.*?)^" + re.escape(END), text, re.S | re.M)
            if not m:
                errs.append("%s: a local-record block opens but does not close (%s)" % (RESULTS_MD, END))
            else:
                table = run([sys.executable, "-I", RECORD_PY, "table"])
                if m.group(1).strip() != table.strip():
                    errs.append("%s: the local-record block is not the record's table: "
                                "kani/local/record.py table, between the markers" % os.path.relpath(RESULTS_MD, ROOT))
        else:
            notes.append("%s has no local-record block" % os.path.relpath(RESULTS_MD, ROOT))

    gh = bool(os.environ.get("GITHUB_ACTIONS"))
    for w in warns:
        print(("::warning title=local Kani record::" if gh else "warning: ") + w)
    for e in errs:
        print(("::error title=local Kani record::" if gh else "error: ") + e)
    if errs:
        return 1
    ok_m = len(rec_m)
    print("local Kani record ok: commit %s, %s; %d harnesses ok, %d mutants as expected; with the kani groups "
          "%d harnesses of run.sh list once each, with kani-mutants %d mutants once each%s"
          % (prov.get("commit", "?")[:12], "fingerprint " + head_fp[:12] if prov.get("fingerprint") == head_fp
             else "STALE (warning above)", len(rec_h), ok_m, len(want), len(patches),
             "".join("; " + n for n in notes)))
    return 0


def main(argv):
    args = argv[1:]
    is_check = not args or args == ["--stale-ok"] or args == ["check"]
    try:
        if is_check:
            return check("--stale-ok" in args)
        if args[0] == "fingerprint" and len(args) <= 2:
            lines, fp = fingerprint(args[1] if len(args) == 2 else "HEAD")
            for n, v in lines:
                print("%s\t%s" % (n, v))
            print("fingerprint\t%s" % fp)
            return 0
        if args[0] == "matrix" and len(args) == 2:
            wf = matrices()
            if args[1] not in wf:
                raise Fail("%s: no matrix entries for the %s job" % (WORKFLOW, args[1]))
            for e in wf[args[1]]:
                print("%s\t%d\t%d" % (e["name"], e["gb"], e["timeout"]))
            return 0
        if args == ["harnesses"]:
            for j in read_record()[2]:
                if j["kind"] == "harness":
                    print(j["name"])
            return 0
        if args == ["covers"]:
            for c in read_record()[3]:
                print("%s\t%s\t%s" % (c["family"], c["cover"], c["status"]))
            return 0
    except Fail as e:
        # The check's errors go with its report; a subcommand's stdout is data.
        print(("::error title=local Kani record::" if os.environ.get("GITHUB_ACTIONS") else "error: ") + str(e),
              file=sys.stdout if is_check else sys.stderr)
        return 1
    print(__doc__.split("\n\n")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
