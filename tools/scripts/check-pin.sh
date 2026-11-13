#!/usr/bin/env bash
# Checks that a project's source mirror is the commit status.toml pins and
# that every file listed in [source_hashes] still has its recorded sha256.
#
# If [project] names a verified_release_commit (a release that is not the pin
# itself), also checks that each of [project] identical_paths (relative to
# upstream_path) is byte-identical at the pin and at that commit: the same
# git tree or blob entry (mode, type and object id) at both. The commit is
# fetched by SHA from the mirror's origin if the clone lacks it (a CI
# submodule checkout has depth 1); a commit that cannot be fetched fails.
#
# usage: tools/scripts/check-pin.sh <project>
# Needs the submodule checked out and python3 >= 3.11 (tomllib).
set -euo pipefail

project=${1:?usage: check-pin.sh <project>}
root=$(cd "$(dirname "$0")/../.." && pwd)
dir="$root/projects/$project"

python3 -I - "$root" "$dir" <<'PY'
import hashlib, posixpath, re, subprocess, sys, tomllib, pathlib
root, d = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
st = tomllib.loads((d / "status.toml").read_text())
pin = st["project"]["pinned_commit"]
base = d / "source-mirror" / st["project"].get("upstream_path", "")
fail = 0

rel = (d / "source-mirror").relative_to(root)
gitlink = subprocess.run(["git", "-C", str(root), "ls-tree", "HEAD", str(rel)],
                         capture_output=True, text=True, check=True).stdout.split()
gitlink = gitlink[2] if len(gitlink) > 2 else "<none>"
if gitlink != pin:
    print(f"gitlink {gitlink} != pinned_commit {pin}"); fail = 1
head = subprocess.run(["git", "-C", str(d / "source-mirror"), "rev-parse", "HEAD"],
                      capture_output=True, text=True).stdout.strip()
if head != pin:
    print(f"checked-out mirror {head or '<not checked out>'} != pinned_commit {pin}"); fail = 1

for name, want in st.get("source_hashes", {}).items():
    p = base / name
    got = hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else "<missing>"
    if got != want:
        print(f"hash drift: {name}: {got} != {want}"); fail = 1

# ASM-COMPILE: the deployed build must keep overflow checks in release.
if st["project"].get("release_overflow_checks"):
    cargo = base / "Cargo.toml"
    prof = tomllib.loads(cargo.read_text()).get("profile", {}).get("release", {}) if cargo.is_file() else {}
    if prof.get("overflow-checks") is not True:
        print(f"ASM-COMPILE: {cargo.relative_to(root)} [profile.release] does not set overflow-checks = true"); fail = 1

# The verified release, when it is not the pin: its code at identical_paths
# must be the pin's, byte for byte.
proj = st["project"]
rel_commit = proj.get("verified_release_commit", "")
if rel_commit:
    mirror = d / "source-mirror"
    label = proj.get("verified_release", rel_commit[:7])
    paths = proj.get("identical_paths", [])
    def git(*args):
        return subprocess.run(["git", "-C", str(mirror), *args], capture_output=True, text=True)
    def entry(commit, path):
        # "<mode> <type> <object>" of the path in the commit, or None.
        out = git("ls-tree", commit, "--", path).stdout.splitlines()
        return out[0].split("\t")[0] if len(out) == 1 and out[0].endswith("\t" + path) else None
    if not re.fullmatch(r"[0-9a-f]{40}", rel_commit):
        print(f"verified_release_commit {rel_commit!r} is not a 40-character sha"); fail = 1
    elif not paths:
        print("verified_release_commit is set but identical_paths is empty"); fail = 1
    else:
        have = git("cat-file", "-e", rel_commit + "^{commit}").returncode == 0
        if not have:
            f = git("fetch", "--quiet", "--no-tags", "--depth", "1", "origin", rel_commit)
            have = f.returncode == 0 and git("cat-file", "-e", rel_commit + "^{commit}").returncode == 0
            if not have:
                print(f"cannot fetch verified_release_commit {rel_commit} ({label}): {f.stderr.strip()}"); fail = 1
        if have:
            up = proj.get("upstream_path", "")
            bad = []
            for p in paths:
                gp = posixpath.join(up, p.rstrip("/")) if up else p.rstrip("/")
                a, b = entry(pin, gp), entry(rel_commit, gp)
                if a is None or b is None:
                    where = " and ".join(w for w, e in (("the pin", a), (label, b)) if e is None)
                    print(f"verified release: {gp} is missing at {where}"); bad.append(gp)
                elif a != b:
                    print(f"verified release: {gp} differs between the pin and {label} ({a} != {b})"); bad.append(gp)
            if bad:
                stat = git("diff", "--stat", pin, rel_commit, "--", *bad).stdout.rstrip()
                if stat:
                    print(stat)
                fail = 1
            else:
                print(f"verified release {label} ({rel_commit[:7]}): {', '.join(paths)} byte-identical to the pin")

print("pin ok" if not fail else "pin check FAILED")
sys.exit(fail)
PY
