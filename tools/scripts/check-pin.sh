#!/usr/bin/env bash
# Checks that a project's source mirror is the commit status.toml pins and
# that every file listed in [source_hashes] still has its recorded sha256.
#
# usage: tools/scripts/check-pin.sh <project>
# Needs the submodule checked out and python3 >= 3.11 (tomllib).
set -euo pipefail

project=${1:?usage: check-pin.sh <project>}
root=$(cd "$(dirname "$0")/../.." && pwd)
dir="$root/projects/$project"

python3 -I - "$root" "$dir" <<'PY'
import hashlib, subprocess, sys, tomllib, pathlib
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

print("pin ok" if not fail else "pin check FAILED")
sys.exit(fail)
PY
