#!/usr/bin/env python3
"""Run shared-pool's large Kani harnesses and mutants on this machine (and record them).

The jobs are the kani-large groups' harnesses and the kani-mutants-large
mutants of .github/workflows/shared-pool.yml (measured peaks above 13 GB,
which ubuntu-latest cannot hold in memory), each with its matrix timeout as
KANI_TIMEOUT. Each job is kani/run.sh (`kani <harness>` or
`mutants --kani 'NN-*'`) from an exact copy of the commit's Kani inputs
(git archive of projects/shared-pool/kani, conformance/traces/core.txt and
the repository's .cargo/config[.toml] above kani/ if it has any, and of
the source-mirror submodule at the commit's gitlink), one copy per lane,
with its own KANI_LOG_DIR and KEEP_LOGS and KANI_DEFER_COVERS=1. At
most --lanes jobs run at once, and only while their measured peaks
(kani/RESULTS.md) sum to at most --budget-gb; the longest start first.
Memory is sampled every 3 s: the run.sh process tree and its largest cbmc
process. run.sh is used as it is; KANI_MAX_GB stays its default (40) unless
set in the environment. The mutant jobs run with RUSTUP_TOOLCHAIN set to
tools/versions.env's RUST_TOOLCHAIN (their plain mode), as CI's
kani-mutants jobs do; the harness jobs without it, as CI's kani jobs.

The fingerprint does not see the environment, so the run refuses to start
when a variable that changes what run.sh runs or how cargo builds is set
(KANI, KANI_FLAGS, KANI_MOD, RUSTFLAGS, CARGO_ENCODED_RUSTFLAGS,
RUSTUP_TOOLCHAIN, RUSTC, RUSTC_WRAPPER, RUSTC_WORKSPACE_WRAPPER,
CARGO_BUILD_*, CARGO_PROFILE_*, CARGO_TARGET_*_RUSTFLAGS), or when a cargo
configuration file outside the lanes (CARGO_HOME's, or a .cargo/ above the
run directory or TMPDIR) sets rustflags, rustc or a wrapper (at any depth,
such as target.<triple>.rustflags), a profile, or an include. The files
are parsed as TOML, as cargo reads them, so every spelling of those keys
(quoted, dotted, an inline table) counts, and one that does not parse is
refused too. That includes the work tree's own (such as
kani/.cargo/config.toml) when the run directory is inside the repository,
the default: cargo would read it on top of the lane's copy of the
commit's. Then pass --out outside the repository. env.txt records the
other KANI_* variables and those files.

usage: run-local.py [--out DIR] [--rev REV] [--lanes N] [--budget-gb GB]
                    [--record] [--dry-run]
  --out DIR      output (default kani/target/local-run/run-<UTC time>)
  --rev REV      the commit to run (default HEAD)
  --record       when every job passed, run record.py DIR (writes kani/local;
                 then commit it)
  --dry-run      check the environment and cargo configuration as a run
                 does, print the jobs and exit

Output, as record.py reads it: env.txt (commit, kani-tree, core-pin, tool
versions, host, lanes, budget, start and end), jobs.json, progress.log
(ends with ALL DONE), results.tsv (job kind lane start_utc secs rc verdict
peak_tree_gb peak_cbmc_gb est_peak_gb est_secs; a harness's verdict is
run.sh's result, a mutant's expect/plain/kani with "!" if run.sh flagged it
UNEXPECTED), logs/<job>/ (stdout.txt, covers.tsv, the Kani and plain logs).
About 4 hours for the 36 harnesses and 16 mutants on a 10-core, 64 GB Mac
with the defaults. Needs Python 3.11 or later (tomllib, for the cargo
configuration), Kani and its CBMC at tools/versions.env's versions
(cargo install --locked kani-verifier --version <KANI>; cargo kani setup),
the Rust toolchain RUST_TOOLCHAIN (rustup toolchain install <RUST_TOOLCHAIN>
--profile minimal) and the source-mirror submodule (git submodule update
--init projects/shared-pool/source-mirror).
"""
import argparse
import datetime
import json
import os
import platform
import re
import signal
import subprocess
import sys
import time

try:
    import tomllib
except ImportError:  # Python < 3.11: build_keys refuses (fails closed)
    tomllib = None

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
SP = "projects/shared-pool"
CHECK = os.path.join(ROOT, "tools/scripts/check-kani-record.py")
RECORD = os.path.join(HERE, "record.py")
# Variables that change what run.sh runs (KANI, KANI_FLAGS, KANI_MOD) or how
# cargo and rustc build (a verdict), which the fingerprint does not see.
REFUSED_ENV = re.compile(r"^(KANI|KANI_FLAGS|KANI_MOD|RUSTFLAGS|CARGO_ENCODED_RUSTFLAGS|RUSTUP_TOOLCHAIN|RUSTC"
                         r"|RUSTC_WRAPPER|RUSTC_WORKSPACE_WRAPPER|CARGO_BUILD_\w+|CARGO_PROFILE_\w+"
                         r"|CARGO_TARGET_\w+_RUSTFLAGS)$")
# Set per job by this script.
OWN_ENV = {"KANI_LOG_DIR", "KANI_DEFER_COVERS", "KANI_TIMEOUT", "KANI_CBMC", "KEEP_LOGS"}
# Cargo configuration keys that change how cargo builds: these at any depth
# (build.rustflags, target.<triple>.rustflags, ...), and at the top level
# profile (any profile's settings) and include (another file, which the
# check would not read).
BUILD_KEYS = {"rustflags", "rustc", "rustc-wrapper", "rustc-workspace-wrapper"}
TOP_BUILD_KEYS = {"profile", "include"}


def sh(*args, **kw):
    r = subprocess.run(list(args), capture_output=True, text=True, **kw)
    if r.returncode != 0:
        sys.exit("run-local.py: %s: exit %d: %s" % (" ".join(args), r.returncode, (r.stderr or r.stdout).strip()))
    return r.stdout


def build_keys(text):
    """The key paths (such as build.rustflags) in a cargo configuration file's text that change how cargo builds.

    The text is parsed as TOML, as cargo parses it, so a quoted, dotted or
    inline-table spelling of a key is the same path. Raises ValueError
    (tomllib.TOMLDecodeError) when the text is not TOML.
    """
    if tomllib is None:
        sys.exit("run-local.py needs Python 3.11+ (tomllib) to check cargo configuration (%s is %s)"
                 % (sys.executable, platform.python_version()))
    found = []

    def name(path):
        return ".".join(k if re.fullmatch(r"[A-Za-z0-9_-]+", k) else json.dumps(k) for k in path)

    def walk(v, path):
        if isinstance(v, dict):
            for k, x in v.items():
                if k in BUILD_KEYS or (not path and k in TOP_BUILD_KEYS):
                    found.append(name(path + [k]))
                else:
                    walk(x, path + [k])
        elif isinstance(v, list):
            for x in v:
                walk(x, path)
    walk(tomllib.loads(text), [])
    return found


def now():
    return datetime.datetime.now(datetime.timezone.utc)


def iso(t):
    return t.strftime("%Y-%m-%dT%H:%M:%SZ")


def host():
    if sys.platform == "darwin":
        cpu = sh("sysctl", "-n", "machdep.cpu.brand_string").strip()
        n = sh("sysctl", "-n", "hw.ncpu").strip()
        gb = int(sh("sysctl", "-n", "hw.memsize")) // 2 ** 30
        return "%s %s cores %d GB, macOS %s" % (cpu, n, gb, platform.mac_ver()[0])
    cpu = "?"
    try:
        with open("/proc/cpuinfo") as f:
            cpu = next((l.split(":", 1)[1].strip() for l in f if l.startswith("model name")), "?")
        with open("/proc/meminfo") as f:
            gb = int(next(l.split()[1] for l in f if l.startswith("MemTotal:"))) // 2 ** 20
    except OSError:
        gb = 0
    return "%s %d cores %d GB, %s %s" % (cpu, os.cpu_count() or 0, gb, platform.system(), platform.release())


def jobs_from_workflow():
    """kani-large's harnesses and kani-mutants-large's mutants, with measured estimates."""
    meas = {}
    try:
        with open(os.path.join(ROOT, SP, "kani/RESULTS.md")) as f:
            for m in re.finditer(r"^\| `(h_\w+)` \| (\S+) \| (\d+) \| ([\d.]+) \|", f.read(), re.M):
                meas.setdefault(m.group(1), (int(m.group(3)), float(m.group(4))))
    except OSError:
        pass
    jobs = []
    for line in sh(sys.executable, "-I", CHECK, "matrix", "kani-large").splitlines():
        group, gb, to = line.split("\t")
        for h in group.split():
            secs, peak = meas.get(h, (int(to) // 3, float(gb)))
            jobs.append(dict(name=h, kind="harness", peak=peak, est=secs, timeout=int(to), args=["kani", h]))
    for line in sh(sys.executable, "-I", CHECK, "matrix", "kani-mutants-large").splitlines():
        mu, gb, to = line.split("\t")
        jobs.append(dict(name="mutant-" + mu, kind="mutant", peak=float(gb), est=int(to) / 3, timeout=int(to),
                         args=["mutants", "--kani", mu + "-*"]))
    # Longest first; the scheduler takes the first job that fits the budget.
    jobs.sort(key=lambda j: -j["est"])
    return jobs


def cargo_configs(*dirs):
    """The cargo configuration files above dirs (their .cargo/config[.toml]) and in CARGO_HOME."""
    out = []
    for d in dirs:
        d = os.path.abspath(d)
        while True:
            out += [os.path.join(d, ".cargo", n) for n in ("config", "config.toml")]
            if os.path.dirname(d) == d:
                break
            d = os.path.dirname(d)
    home = os.environ.get("CARGO_HOME") or os.path.expanduser("~/.cargo")
    out += [os.path.join(home, n) for n in ("config", "config.toml")]
    seen = []
    for p in out:
        if os.path.isfile(p) and p not in seen:
            seen.append(p)
    return seen


def make_lane(lane, commit, core, cargo_above):
    """An exact copy of the commit's Kani inputs at lane/ (cargo_above: its .cargo/config[.toml] above kani/)."""
    os.makedirs(lane)
    a = subprocess.Popen(["git", "-C", ROOT, "archive", "--format=tar", commit, SP + "/kani",
                          SP + "/conformance/traces/core.txt"] + cargo_above, stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "-C", lane], stdin=a.stdout, check=True)
    if a.wait() != 0:
        sys.exit("run-local.py: git archive %s failed" % commit)
    sm = os.path.join(lane, SP, "source-mirror")
    os.makedirs(sm)
    a = subprocess.Popen(["git", "-C", os.path.join(ROOT, SP, "source-mirror"), "archive", "--format=tar", core],
                         stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "-C", sm], stdin=a.stdout, check=True)
    if a.wait() != 0:
        sys.exit("run-local.py: git archive of the source-mirror at %s failed" % core)


def tree_rss(root):
    """(tree KB, largest cbmc KB) for the process tree rooted at pid root."""
    try:
        out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,rss=,comm="], capture_output=True, text=True).stdout
    except OSError:
        return 0, 0
    kids, rss, comm = {}, {}, {}
    for line in out.splitlines():
        p = line.split(None, 3)
        if len(p) < 4:
            continue
        pid, ppid, r = int(p[0]), int(p[1]), int(p[2])
        kids.setdefault(ppid, []).append(pid)
        rss[pid], comm[pid] = r, p[3]
    tot, cb, stack = 0, 0, [root]
    while stack:
        p = stack.pop()
        tot += rss.get(p, 0)
        if os.path.basename(comm.get(p, "")).startswith("cbmc"):
            cb = max(cb, rss.get(p, 0))
        stack.extend(kids.get(p, []))
    return tot, cb


def verdict(job, so):
    if job["kind"] == "harness":
        m = re.search(r"^%s\s+(\S+)\s+(\d+)" % re.escape(job["name"]), so, re.M)
        return m.group(1) if m else "NO-RESULT"
    nn = job["name"].split("-", 1)[1]
    m = re.search(r"^(%s-\S*)\s+(\S+)\s+(\S+)\s+(\S+)(.*)$" % re.escape(nn), so, re.M)
    if not m:
        return "NO-RESULT"
    return "%s/%s/%s%s" % (m.group(2), m.group(3), m.group(4), "!" if "UNEXPECTED" in m.group(5) else "")


def passed(job, v):
    if job["kind"] == "harness":
        return v == ("ok-FAILED" if job["name"] == "h_canary" else "ok")
    return v in ("killed/killed/killed", "survive/survived/survived")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out")
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--lanes", type=int, default=2)
    ap.add_argument("--budget-gb", type=float, default=50.0)
    ap.add_argument("--record", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    commit = sh("git", "-C", ROOT, "rev-parse", "--verify", a.rev + "^{commit}").strip()
    kani_tree = sh("git", "-C", ROOT, "rev-parse", commit + ":" + SP + "/kani").strip()
    core = sh("git", "-C", ROOT, "rev-parse", commit + ":" + SP + "/source-mirror").strip()
    versions = sh("git", "-C", ROOT, "show", commit + ":tools/versions.env")
    kani_v = re.search(r"^KANI=(\S+)", versions, re.M).group(1)
    cbmc_v = re.search(r"^CBMC=(\S+)", versions, re.M).group(1)
    rust_v = re.search(r"^RUST_TOOLCHAIN=(\S+)", versions, re.M).group(1)
    jobs = jobs_from_workflow()
    if not jobs:
        sys.exit("run-local.py: no kani-large or kani-mutants-large entries in the workflow")
    # The environment and cargo configuration: nothing the fingerprint does
    # not see may change a verdict. A dry run checks them too.
    refused = sorted(k for k, v in os.environ.items() if REFUSED_ENV.match(k) and v != "")
    if refused:
        sys.exit("run-local.py: %s set in the environment, which changes what run.sh runs or how cargo builds; "
                 "the record's fingerprint does not see the environment: unset it and start again"
                 % ", ".join(refused))
    started = now()
    out = os.path.abspath(a.out or os.path.join(ROOT, SP, "kani/target/local-run",
                                                "run-" + started.strftime("%Y%m%dT%H%MZ")))
    if os.path.exists(out):
        sys.exit("run-local.py: %s exists" % out)
    configs = cargo_configs(out, os.environ.get("TMPDIR") or "/tmp")
    bad, unparsable = [], []
    for p in configs:
        try:
            with open(p, "rb") as f:
                keys = build_keys(f.read().decode("utf-8"))
        except ValueError as e:  # not TOML (or not UTF-8): cargo would not read it either
            unparsable.append("%s (%s)" % (p, e))
            continue
        if keys:
            bad.append((p, keys))
    if unparsable:
        sys.exit("run-local.py: unparsable cargo configuration %s: cannot tell whether it sets rustflags, rustc or a "
                 "wrapper, a profile or an include: move it aside and start again" % "; ".join(unparsable))

    def named(ps):
        return ", ".join("%s (%s)" % (path, ", ".join(ks)) for path, ks in ps)
    in_repo = [(path, ks) for path, ks in bad if path.startswith(ROOT + os.sep)]
    if in_repo:
        # The lanes have the commit's copies (fingerprinted); cargo would
        # read the work tree's above them as well.
        sys.exit("run-local.py: %s set rustflags, rustc or a wrapper, a profile or an include, and are in the work "
                 "tree above the run directory %s, so cargo would read them in every lane; the lanes have %s's own "
                 "cargo configuration (the fingerprinted one) from git archive: pass --out outside the repository "
                 "and start again" % (named(in_repo), out, commit[:12]))
    if bad:
        sys.exit("run-local.py: %s set rustflags, rustc or a wrapper, a profile or an include, for the run's builds; "
                 "the record's fingerprint does not see them: move them aside and start again" % named(bad))
    if a.dry_run:
        print("commit %s; %d jobs (KANI_TIMEOUT, measured peak GB, estimated s):" % (commit[:12], len(jobs)))
        for j in jobs:
            print("  %-28s %-8s %5d s  %5.1f GB  %5.0f s  run.sh %s" % (j["name"], j["kind"], j["timeout"], j["peak"],
                                                                     j["est"], " ".join(j["args"])))
        return 0
    if sh("git", "-C", ROOT, "diff", "--name-only", commit, "--",
          *sh(sys.executable, "-I", CHECK, "pathspecs").splitlines()).strip():
        print("run-local.py: note: the work tree's Kani inputs differ from %s; the run uses %s's" % (commit[:12],
              commit[:12]), file=sys.stderr)

    cargo_above = sh(sys.executable, "-I", CHECK, "cargo-configs", commit).splitlines()
    kani_env = " ".join("%s=%s" % (k, os.environ[k]) for k in sorted(os.environ)
                        if k.startswith("KANI_") and k not in OWN_ENV) or "none"

    # Tools: the pinned Kani and its own CBMC (run.sh reads loop ids with it).
    kani_line = sh("cargo", "kani", "--version").splitlines()[0].strip()
    if not re.search(r"(^|\s)%s(\s|$)" % re.escape(kani_v), kani_line):
        sys.exit("run-local.py: %r is not Kani %s (tools/versions.env)" % (kani_line, kani_v))
    cbmc = os.environ.get("KANI_CBMC") or os.path.join(os.environ.get("KANI_HOME") or os.path.expanduser("~/.kani"),
                                                       "kani-" + kani_v, "bin", "cbmc")
    cbmc_line = sh(cbmc, "--version").strip()
    if cbmc_line.split()[:1] != [cbmc_v]:
        sys.exit("run-local.py: %s is %r, not CBMC %s" % (cbmc, cbmc_line, cbmc_v))
    # The mutants' plain mode: RUST_TOOLCHAIN, as CI's kani-mutants jobs.
    r = subprocess.run(["rustc", "--version"], capture_output=True, text=True,
                       env=dict(os.environ, RUSTUP_TOOLCHAIN=rust_v))
    rustc = r.stdout.strip()
    if r.returncode != 0 or not rustc.startswith("rustc %s " % rust_v):
        sys.exit("run-local.py: the mutant jobs' plain mode needs Rust %s (tools/versions.env RUST_TOOLCHAIN), as "
                 "in CI: rustup toolchain install %s --profile minimal (rustc: %s)"
                 % (rust_v, rust_v, (rustc or r.stderr.strip())[:200]))
    smr = os.path.join(ROOT, SP, "source-mirror")
    if subprocess.run(["git", "-C", smr, "cat-file", "-e", core + "^{commit}"], capture_output=True).returncode:
        sys.exit("run-local.py: the source-mirror submodule lacks %s: git submodule update --init %s/source-mirror"
                 % (core, SP))

    os.makedirs(os.path.join(out, "logs"))
    lanes = ["lane%d" % i for i in range(1, a.lanes + 1)]
    for lane in lanes:
        make_lane(os.path.join(out, "lanes", lane), commit, core, cargo_above)
    with open(os.path.join(out, "env.txt"), "w") as f:
        f.write("commit %s\nkani-tree %s\ncore-pin %s\nkani %s\nCBMC %s\ncbmc %s\nrustc %s\nhost %s\n"
                "lanes %d\nbudget-gb %g\nkani-max-gb %s\nkani-env %s\ncargo-config %s\n"
                "runner projects/shared-pool/kani/local/run-local.py\nstarted %s\n"
                % (commit, kani_tree, core, kani_line, cbmc_v, cbmc_line,
                   rustc + " (RUSTUP_TOOLCHAIN of the mutant jobs' plain mode, as in CI)", host(), a.lanes,
                   a.budget_gb, os.environ.get("KANI_MAX_GB") or "40 (run.sh's default)", kani_env,
                   " ".join(configs) or "none", iso(started)))
    with open(os.path.join(out, "jobs.json"), "w") as f:
        json.dump(jobs, f, indent=1)

    def log(msg):
        line = now().strftime("%H:%M:%SZ ") + msg
        with open(os.path.join(out, "progress.log"), "a") as f:
            f.write(line + "\n")
        print(line, flush=True)

    running, pending, ok = {}, list(jobs), True

    def stop(signum, _frame):
        for j in running.values():
            try:
                os.killpg(j["proc"].pid, signal.SIGKILL)
            except OSError:
                pass
        log("stopped by signal %d; not complete" % signum)
        sys.exit(1)

    signal.signal(signal.SIGINT, stop)
    signal.signal(signal.SIGTERM, stop)
    log("%d jobs: %d harnesses, %d mutants; budget %g GB; output %s"
        % (len(jobs), sum(j["kind"] == "harness" for j in jobs), sum(j["kind"] == "mutant" for j in jobs),
           a.budget_gb, out))
    results = open(os.path.join(out, "results.tsv"), "a")
    while pending or running:
        for lane in lanes:
            if lane in running or not pending:
                continue
            used = sum(j["peak"] for j in running.values())
            # Alone, a job always fits (h_wedge's peak may be most of the budget).
            pick = next((j for j in pending if not running or used + j["peak"] <= a.budget_gb), None)
            if pick is None:
                break
            pending.remove(pick)
            d = os.path.join(out, "logs", pick["name"])
            os.makedirs(d, exist_ok=True)
            env = dict(os.environ, KANI_LOG_DIR=d, KANI_DEFER_COVERS="1", KANI_TIMEOUT=str(pick["timeout"]),
                       KEEP_LOGS=d, KANI_CBMC=cbmc)
            if pick["kind"] == "mutant":
                env["RUSTUP_TOOLCHAIN"] = rust_v
            lane_dir = os.path.join(out, "lanes", lane)
            so = open(os.path.join(d, "stdout.txt"), "w")
            pick["proc"] = subprocess.Popen(["bash", os.path.join(lane_dir, SP, "kani/run.sh")] + pick["args"],
                                            env=env, stdout=so, stderr=subprocess.STDOUT, cwd=lane_dir,
                                            start_new_session=True)
            pick["t0"], pick["start"] = time.monotonic(), iso(now())
            pick["ptree"], pick["pcbmc"] = 0, 0
            running[lane] = pick
            log("start %s on %s (peak %s GB, est %.0f s, limit %d s)" % (pick["name"], lane, pick["peak"],
                                                                         pick["est"], pick["timeout"]))
        time.sleep(3)
        for lane, j in list(running.items()):
            t, c = tree_rss(j["proc"].pid)
            j["ptree"], j["pcbmc"] = max(j["ptree"], t), max(j["pcbmc"], c)
            rc = j["proc"].poll()
            if rc is None:
                continue
            secs = time.monotonic() - j["t0"]
            with open(os.path.join(out, "logs", j["name"], "stdout.txt")) as f:
                v = verdict(j, f.read())
            ok = ok and rc == 0 and passed(j, v)
            row = [j["name"], j["kind"], lane, j["start"], "%.0f" % secs, str(rc), v, "%.1f" % (j["ptree"] / 1048576),
                   "%.1f" % (j["pcbmc"] / 1048576), "%s" % j["peak"], "%.0f" % j["est"]]
            results.write("\t".join(row) + "\n")
            results.flush()
            log("done  %s rc=%d %s %.0f s peak %.1f GB cbmc / %.1f GB tree"
                % (j["name"], rc, v, secs, j["pcbmc"] / 1048576, j["ptree"] / 1048576))
            del running[lane]
    results.close()
    with open(os.path.join(out, "env.txt"), "a") as f:
        f.write("finished %s\n" % iso(now()))
    log("ALL DONE")
    print("run-local.py: %s; record it with: %s %s" % ("every job passed" if ok else "SOME JOBS FAILED (results.tsv)",
                                                       os.path.relpath(RECORD), out))
    if a.record and ok:
        return subprocess.run([sys.executable, "-I", RECORD, out]).returncode
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
