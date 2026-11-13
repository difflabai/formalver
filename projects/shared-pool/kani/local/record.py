#!/usr/bin/env python3
"""shared-pool's local Kani record: write it from a finished local run, or print its tables.

usage: record.py RUN_DIR   check a run of run-local.py (complete; every job
                           exit 0; every harness ok; every mutant as its patch
                           expects, with the log of its Kani leg; the run's
                           commit has HEAD's Kani inputs and Kani/CBMC
                           versions) and write provenance.txt, jobs.tsv and
                           covers.tsv into this directory, and the new table
                           into kani/RESULTS.md's local-record block. Refuses
                           (exit 1, the record and RESULTS.md untouched)
                           otherwise, if RESULTS.md has no such block, or if
                           tools/scripts/check-kani-record.py fails on the new
                           record.
       record.py table     print the record's Markdown: provenance, the
                           harness table and the mutant table (RESULTS.md's
                           local-record block)

The run directory is what run-local.py writes (env.txt, jobs.json,
progress.log, results.tsv, logs/<job>/: stdout.txt, covers.tsv, the Kani
logs). env: KANI_RECORD_DIR (default: this directory), KANI_RESULTS_MD
(default: kani/RESULTS.md).
"""
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
KANI = os.path.join(ROOT, "projects/shared-pool/kani")
CHECK = os.path.join(ROOT, "tools/scripts/check-kani-record.py")
RECORD = os.environ.get("KANI_RECORD_DIR") or HERE
RESULTS_MD = os.environ.get("KANI_RESULTS_MD") or os.path.join(KANI, "RESULTS.md")
JOBS_COLUMNS = ["kind", "name", "result", "seconds", "job_seconds", "cbmc_peak_gb",
                "tree_peak_gb", "limit_s", "covers", "kani_harnesses", "started_utc"]
COVERS_COLUMNS = ["family", "cover", "status", "harness"]
BEGIN = "<!-- kani-local-record: begin (kani/local/record.py writes this block; do not edit) -->"
END = "<!-- kani-local-record: end -->"
RESULTS_TSV = ["job", "kind", "lane", "start_utc", "secs", "rc", "verdict", "peak_tree_gb",
               "peak_cbmc_gb", "est_peak_gb", "est_secs"]


class Refuse(Exception):
    pass


def out(*args, **kw):
    r = subprocess.run(list(args), capture_output=True, text=True, **kw)
    if r.returncode != 0:
        raise Refuse("%s: exit %d: %s" % (" ".join(args), r.returncode, (r.stderr or r.stdout).strip()))
    return r.stdout


def git(*args):
    return out("git", "-C", ROOT, *args).strip()


def fingerprint(rev):
    """[(name, value)], fingerprint: check-kani-record.py's, the one source."""
    lines = out(sys.executable, "-I", CHECK, "fingerprint", rev).splitlines()
    pairs = [tuple(l.split("\t", 1)) for l in lines]
    return pairs[:-1], pairs[-1][1]


def read_env(path):
    env = {}
    with open(path) as f:
        for line in f:
            k, _, v = line.strip().partition(" ")
            if k:
                env[k] = v.strip()
    return env


def parse_iso(s):
    return datetime.datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ")


def mutant_header(name):
    """(expected (expect, plain, kani), [Kani harnesses in header order])."""
    with open(os.path.join(KANI, "mutants", name + ".patch")) as f:
        text = f.read()
    survive = re.search(r"^# must-survive$", text, re.M) is not None
    hs = []
    for m in re.finditer(r"^# (?:killed-by|checked-by): (.*)$", text, re.M):
        hs += m.group(1).split()
    exp = ("survive", "survived", "survived") if survive else ("killed", "killed", "killed")
    return exp, hs


def read_run(run):
    """Validate the run directory; return (env, rows for jobs.tsv, covers rows)."""
    for f in ("env.txt", "jobs.json", "results.tsv", "progress.log"):
        if not os.path.exists(os.path.join(run, f)):
            raise Refuse("%s: no %s (not a run-local.py output directory)" % (run, f))
    env = read_env(os.path.join(run, "env.txt"))
    with open(os.path.join(run, "jobs.json")) as f:
        jobs = json.load(f)
    results = {}
    with open(os.path.join(run, "results.tsv")) as f:
        for n, line in enumerate(f, 1):
            if not line.strip():
                continue
            r = line.rstrip("\n").split("\t")
            if len(r) != len(RESULTS_TSV):
                raise Refuse("results.tsv:%d: %d fields, want %d" % (n, len(r), len(RESULTS_TSV)))
            r = dict(zip(RESULTS_TSV, r))
            if r["job"] in results:
                raise Refuse("results.tsv: %s finished twice" % r["job"])
            results[r["job"]] = r
    with open(os.path.join(run, "progress.log")) as f:
        log = [l.strip() for l in f if l.strip()]
    names = [j["name"] for j in jobs]
    unknown = sorted(set(results) - set(names))
    if unknown:
        raise Refuse("results.tsv: jobs not in jobs.json: %s" % " ".join(unknown))
    if not (log and log[-1].endswith("ALL DONE")) or len(results) != len(names):
        pending = [n for n in names if n not in results]
        raise Refuse("incomplete run: %d of %d jobs finished%s; not recorded (wait for ALL DONE in progress.log)"
                     % (len(results), len(names), "" if not pending else ", waiting for " + " ".join(pending[:8])
                        + (" ..." if len(pending) > 8 else "")))

    problems, rows, covers = [], [], []
    for j in jobs:
        name, r = j["name"], results[j["name"]]
        d = os.path.join(run, "logs", name)
        try:
            with open(os.path.join(d, "stdout.txt")) as f:
                so = f.read()
        except OSError:
            so = ""
        if r["rc"] != "0":
            problems.append("%s: run.sh exit %s (%s)" % (name, r["rc"], r["verdict"]))
        if j["kind"] == "harness":
            want = "ok-FAILED" if name == "h_canary" else "ok"
            m = re.search(r"^%s\s+(\S+)\s+(\d+)\s+(.*)$" % re.escape(name), so, re.M)
            if r["verdict"] != want or not m or m.group(1) != want:
                got = (r["verdict"] if r["verdict"] != want else
                       "%s in stdout.txt" % m.group(1) if m else "no result line in stdout.txt")
                problems.append("%s: %s, not %s" % (name, got, want))
                continue
            if "family check deferred" not in so:
                problems.append("%s: not run with KANI_DEFER_COVERS=1 (no covers.tsv)" % name)
                continue
            cov = m.group(3).strip()
            cov = re.sub(r" cover properties satisfied$", "", cov)
            try:
                with open(os.path.join(d, "covers.tsv")) as f:
                    for line in f:
                        if line.strip():
                            c = line.rstrip("\n").split("\t")
                            if len(c) != 3:
                                raise Refuse("%s/covers.tsv: %r is not family<TAB>cover<TAB>status" % (d, line))
                            covers.append(c + [name])
            except OSError:
                problems.append("%s: no covers.tsv" % name)
                continue
            rows.append(dict(kind="harness", name=name, result=want, seconds=m.group(2), job_seconds=r["secs"],
                             cbmc_peak_gb=r["peak_cbmc_gb"], tree_peak_gb=r["peak_tree_gb"],
                             limit_s=str(j["timeout"]), covers=cov, kani_harnesses="-",
                             started_utc=r["start_utc"]))
        elif j["kind"] == "mutant":
            nn = name.split("-", 1)[1]
            lines = re.findall(r"^(%s-\S+)\s+(\S+)\s+(\S+)\s+(\S+)(.*)$" % re.escape(nn), so, re.M)
            if len(lines) != 1:
                problems.append("%s: %d result lines for mutants/%s-*.patch in stdout.txt, want 1"
                                % (name, len(lines), nn))
                continue
            full, e, p, k, rest = lines[0]
            if not os.path.exists(os.path.join(KANI, "mutants", full + ".patch")):
                problems.append("%s: no mutants/%s.patch" % (name, full))
                continue
            exp, header = mutant_header(full)
            got = "%s/%s/%s" % (e, p, k)
            if (e, p, k) != exp or "UNEXPECTED" in rest or r["verdict"] != got:
                problems.append("%s (%s): expect/plain/kani %s%s, want %s"
                                % (name, full, got, " UNEXPECTED" if "UNEXPECTED" in rest else "", "/".join(exp)))
                continue
            # Its Kani leg ran: run.sh keeps a log per harness (KEEP_LOGS).
            ran = [h for h in header if os.path.exists(os.path.join(d, "%s.%s.log" % (full, h)))]
            if not ran:
                problems.append("%s (%s): no log of its Kani leg in logs/%s (%s)"
                                % (name, full, name, ", ".join("%s.%s.log" % (full, h) for h in header)
                                   or "its patch names no killed-by or checked-by harness"))
                continue
            rows.append(dict(kind="mutant", name=full, result=got, seconds=r["secs"], job_seconds=r["secs"],
                             cbmc_peak_gb=r["peak_cbmc_gb"], tree_peak_gb=r["peak_tree_gb"],
                             limit_s=str(j["timeout"]), covers="-", kani_harnesses=",".join(ran),
                             started_utc=r["start_utc"]))
        else:
            problems.append("%s: kind %r" % (name, j["kind"]))
    if problems:
        raise Refuse("failed or unexpected jobs, not recorded:\n  " + "\n  ".join(problems))

    # Order: harnesses as run.sh lists them, then mutants by name.
    order = {h: i for i, h in enumerate(out("bash", os.path.join(KANI, "run.sh"), "list").split())}
    rows.sort(key=lambda x: (x["kind"] != "harness", order.get(x["name"], len(order)), x["name"]))
    pos = {x["name"]: i for i, x in enumerate(rows)}
    covers.sort(key=lambda c: pos[c[3]])  # stable: each harness's covers in its log's order

    # Finished: env.txt's, or the last job's end.
    if "finished" not in env:
        ends = [parse_iso(r["start_utc"]) + datetime.timedelta(seconds=int(r["secs"])) for r in results.values()]
        env["finished"] = max(ends).strftime("%Y-%m-%dT%H:%M:%SZ")
    m = re.search(r"budget ([\d.]+) GB", log[0])
    env.setdefault("budget-gb", "%g" % float(m.group(1)) if m else "?")
    env.setdefault("lanes", str(len({r["lane"] for r in results.values()})))
    return env, rows, covers


def provenance(env, rows):
    """Check the run's commit and tools against HEAD; return the provenance key/values (inputs separate)."""
    commit = env.get("commit", "")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise Refuse("env.txt: commit %r is not a full commit id" % commit)
    if subprocess.run(["git", "-C", ROOT, "cat-file", "-e", commit + "^{commit}"], capture_output=True).returncode:
        raise Refuse("env.txt: commit %s is not in this repository" % commit)
    problems = []
    kt = git("rev-parse", commit + ":projects/shared-pool/kani")
    cp = git("rev-parse", commit + ":projects/shared-pool/source-mirror")
    if env.get("kani-tree") != kt:
        problems.append("env.txt kani-tree %s is not %s:projects/shared-pool/kani (%s)"
                        % (env.get("kani-tree"), commit[:12], kt))
    if env.get("core-pin") != cp:
        problems.append("env.txt core-pin %s is not %s's source-mirror gitlink (%s)"
                        % (env.get("core-pin"), commit[:12], cp))
    inputs, fp = fingerprint(commit)
    head, head_fp = fingerprint("HEAD")
    v = dict(inputs)
    kani_v, cbmc_v = v["tools/versions.env:KANI"], v["tools/versions.env:CBMC"]
    if not re.search(r"(^|\s)%s(\s|$)" % re.escape(kani_v), env.get("kani", "")):
        problems.append("env.txt kani %r is not Kani %s (versions.env)" % (env.get("kani"), kani_v))
    cbmc = env.get("cbmc") or env.get("CBMC", "")
    if cbmc.split()[:1] != [cbmc_v]:
        problems.append("env.txt cbmc %r is not CBMC %s (versions.env)" % (cbmc, cbmc_v))
    if fp != head_fp:
        hv = dict(head)
        problems.append("the run's commit %s has other Kani inputs than HEAD (%s): run run-local.py at HEAD"
                        % (commit[:12], ", ".join(n for n, x in inputs if hv.get(n) != x)))
    for k in ("host", "started"):
        if not env.get(k):
            problems.append("env.txt has no %s" % k)
    if problems:
        raise Refuse("the run's provenance does not hold:\n  " + "\n  ".join(problems))
    nh = sum(1 for r in rows if r["kind"] == "harness")
    meta = [
        ("commit", commit),
        ("kani_tree", kt),
    ]
    tail = [
        ("kani", env.get("kani", "")),
        ("cbmc", cbmc),
        ("rustc", env.get("rustc") or "not recorded (the host's default toolchain, for the mutants' plain mode)"),
        ("host", env["host"]),
        ("started", env["started"]),
        ("finished", env["finished"]),
        ("parallel", "%s jobs at a time, their measured peaks summing to at most %s GB"
         % (env.get("lanes"), env.get("budget-gb"))),
        ("kani_max_gb", env.get("kani-max-gb") or "40 (run.sh's default)"),
        ("kani_env", env.get("kani-env") or "not recorded (the run's other KANI_* variables)"),
        ("cargo_config", env.get("cargo-config") or "not recorded (cargo configuration outside the Kani tree)"),
        ("runner", env.get("runner") or "sched.py, the prototype of kani/local/run-local.py (same jobs, lanes "
                                         "and sampling)"),
        ("jobs", "%d harnesses, %d mutants" % (nh, len(rows) - nh)),
    ]
    return meta, inputs, fp, tail


def tsv(columns, rows):
    return "\t".join(columns) + "\n" + "".join("\t".join(r) + "\n" for r in rows)


def write_record(d, meta, inputs, fp, tail, rows, covers):
    with open(os.path.join(d, "jobs.tsv"), "w") as f:
        f.write(tsv(JOBS_COLUMNS, [[r[c] for c in JOBS_COLUMNS] for r in rows]))
    with open(os.path.join(d, "covers.tsv"), "w") as f:
        f.write(tsv(COVERS_COLUMNS, covers))
    h = hashlib.sha256()
    for name in ("jobs.tsv", "covers.tsv"):
        with open(os.path.join(d, name), "rb") as f:
            h.update(f.read())
    digest = h.hexdigest()
    with open(os.path.join(d, "provenance.txt"), "w") as f:
        f.write("# shared-pool's local Kani record: the run's provenance. Written by\n"
                "# projects/shared-pool/kani/local/record.py from a run of run-local.py; do\n"
                "# not edit. tools/scripts/check-kani-record.py checks it in CI: the input\n"
                "# lines (git object ids, tool versions) hash to fingerprint, which must be\n"
                "# HEAD's; digest is the sha256 of jobs.tsv and covers.tsv.\n")
        for k, v in meta:
            f.write("%s\t%s\n" % (k, v))
        for n, v in inputs:
            f.write("input\t%s\t%s\n" % (n, v))
        f.write("fingerprint\t%s\ndigest\t%s\n" % (fp, digest))
        for k, v in tail:
            f.write("%s\t%s\n" % (k, v))


def read_record(d):
    prov, inputs = {}, []
    with open(os.path.join(d, "provenance.txt")) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            p = line.rstrip("\n").split("\t")
            if p[0] == "input":
                inputs.append((p[1], p[2]))
            else:
                prov[p[0]] = p[1]
    with open(os.path.join(d, "jobs.tsv")) as f:
        lines = [l.rstrip("\n").split("\t") for l in f if l.strip()]
    return prov, dict(inputs), [dict(zip(lines[0], l)) for l in lines[1:]]


def table(d):
    prov, inputs, jobs = read_record(d)
    hs = [j for j in jobs if j["kind"] == "harness"]
    ms = [j for j in jobs if j["kind"] == "mutant"]
    s = []
    s.append("Local record (`kani/local/`, %d harnesses and %d mutants): commit `%s`, Kani inputs fingerprint "
             "`%s` (CI recomputes it, `tools/scripts/check-kani-record.py`); Kani %s, CBMC %s; %s; %s to %s, %s. "
             "Time is wall clock per harness including compilation (a mutant: its whole run, plain mode "
             "included); peak is CBMC's resident memory, sampled every 3 s; limit is the job's KANI_TIMEOUT."
             % (len(hs), len(ms), prov["commit"][:7], prov["fingerprint"][:12],
                inputs.get("tools/versions.env:KANI"), inputs.get("tools/versions.env:CBMC"), prov["host"],
                prov["started"], prov["finished"], prov["parallel"]))
    s.append("")
    s.append("| Harness | Result | Time (s) | Peak (GB) | Limit (s) | Covers SATISFIED (this harness) |")
    s.append("|---|---|---:|---:|---:|---|")
    for j in hs:
        s.append("| `%s` | %s | %s | %s | %s | %s |" % (j["name"], j["result"], j["seconds"], j["cbmc_peak_gb"],
                                                      j["limit_s"], j["covers"]))
    if ms:
        s.append("")
        s.append("| Mutant | Expected | Plain | Kani (harness) | Time (s) | Peak (GB) | Limit (s) |")
        s.append("|---|---|---|---|---:|---:|---:|")
        for j in ms:
            e, p, k = j["result"].split("/")
            hn = ", ".join("`%s`" % h for h in j["kani_harnesses"].split(",") if h)
            s.append("| `%s` | %s | %s | %s (%s) | %s | %s | %s |" % (j["name"], e, p, k, hn, j["seconds"],
                                                                     j["cbmc_peak_gb"], j["limit_s"]))
    return "\n".join(s) + "\n"


def results_with_block(tbl):
    """RESULTS.md's text with the block rewritten, or None if it has no block."""
    if not os.path.exists(RESULTS_MD):
        return None
    with open(RESULTS_MD) as f:
        text = f.read()
    m = re.search(r"^<!-- kani-local-record: begin[^\n]*\n.*?^" + re.escape(END) + r"$", text, re.S | re.M)
    if not m:
        return None
    return text[:m.start()] + BEGIN + "\n" + tbl + END + text[m.end():]


def write(run):
    run = os.path.abspath(run)
    env, rows, covers = read_run(run)
    meta, inputs, fp, tail = provenance(env, rows)
    tmp = tempfile.mkdtemp(prefix="kani-record.")
    try:
        write_record(tmp, meta, inputs, fp, tail, rows, covers)
        tbl = table(tmp)
        new_results = results_with_block(tbl)
        if new_results is None:
            raise Refuse("%s has no local-record block (the check requires one): put\n  %s\n  %s\n"
                         "into it, and record.py fills it" % (os.path.relpath(RESULTS_MD), BEGIN, END))
        with open(os.path.join(tmp, "RESULTS.md"), "w") as f:
            f.write(new_results)
        check_env = dict(os.environ, KANI_RECORD_DIR=tmp, KANI_RESULTS_MD=os.path.join(tmp, "RESULTS.md"))
        # The check's RESULTS.md block compares with `record.py table` of
        # KANI_RECORD_DIR, which this process's children inherit.
        r = subprocess.run([sys.executable, "-I", CHECK], env=check_env, capture_output=True, text=True)
        if r.returncode != 0:
            raise Refuse("the new record fails tools/scripts/check-kani-record.py:\n" + r.stdout + r.stderr)
        os.makedirs(RECORD, exist_ok=True)
        for f in ("jobs.tsv", "covers.tsv", "provenance.txt"):
            shutil.copyfile(os.path.join(tmp, f), os.path.join(RECORD, f))
        with open(RESULTS_MD, "w") as f:
            f.write(new_results)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    nh = sum(1 for r in rows if r["kind"] == "harness")
    print("recorded %d harnesses and %d mutants of %s (commit %s, fingerprint %s) in %s"
          % (nh, len(rows) - nh, run, meta[0][1][:12], fp[:12], os.path.relpath(RECORD)))
    print(r.stdout.strip())
    print("rewrote the local-record block of %s" % os.path.relpath(RESULTS_MD))
    return 0


def main(argv):
    try:
        if len(argv) == 2 and argv[1] == "table":
            sys.stdout.write(table(RECORD))
            return 0
        if len(argv) == 2 and not argv[1].startswith("-"):
            return write(argv[1])
    except Refuse as e:
        print("record.py: refused: %s" % e, file=sys.stderr)
        return 1
    print(__doc__.split("\n\n")[1], file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
