#!/usr/bin/env bash
# status-lint (strategy.md sections 12 and 14). Fails when status.toml claims
# more than the repository backs:
#   - `evidence` not allowed for the property's `layer`;
#   - a property past `unverified` whose artifact doesn't mention it: Rust
#     layers need a `// PROP: <ID>` tag in the layer's crate, other layers the
#     ID somewhere in the layer's directory;
#   - a status above the layer's ceiling (Kani: verified-with-assumptions;
#     only Verus path A may claim `verified` with evidence `proof`);
#   - a K or V property at verified* without `[review] spec_reviewer`.
# In-progress K/V properties are allowed without sign-off: they record that
# the proofs pass in CI while the human spec review is still pending.
#
# Whether a verified* property's harness passed "in this run" is the job of
# the jobs that run it (kani, covers, prolog, ...): this script only checks
# that the claim has an artifact behind it.
#
# usage: tools/scripts/check-status.sh <project>
#        STATUS_TOML=<file> ...   (lint another status file against the project's
#                                  artifacts; test-check-status.sh uses it)
set -euo pipefail

project=${1:?usage: check-status.sh <project>}
root=$(cd "$(dirname "$0")/../.." && pwd)

python3 -I - "$root" "$root/projects/$project" <<'PY'
import os, pathlib, re, sys, tomllib

root, d = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
st = tomllib.loads(pathlib.Path(os.environ.get("STATUS_TOML") or d / "status.toml").read_text())

ALLOWED = {
    "kani": {"bounded-proof"},
    "plain": {"test"},
    "verus": {"proof", "model-proof"},
    "lean": {"model-proof", "model-check"},
    "prolog": {"check", "model-check", "test"},
    "tla": {"model-check", "bounded-proof"},
    "unit": {"test"},
    "difftest": {"test"},
    "sandbox": {"test", "check"},
    "wasm-check": {"check"},
    "deploy-check": {"check"},
    "review": {"review"},
}
# Where each layer's artifacts live (relative to the project), and whether the
# layer tags its properties with `// PROP:`.
DIRS = {
    "kani": (["kani/src"], True),
    "plain": (["kani/src"], True),
    "verus": (["verus"], True),
    "lean": (["lean"], False),
    "prolog": (["prolog"], False),
    "tla": (["tla", "kani/src"], False),
    "unit": (["near-tests"], True),
    "difftest": (["near-tests"], True),
    "sandbox": (["sandbox"], True),
    "wasm-check": (["near-tests", "wasm-surface.expected", "../../tools/scripts/wasm-surface.sh"], False),
    "deploy-check": (["deploy-checks"], False),
    "review": ([], False),
}
SKIP_DIRS = {"target", ".lake", "build", "node_modules", ".git"}
TEXT = {".rs", ".tla", ".cfg", ".lean", ".pl", ".py", ".sh", ".toml", ".md", ".expected", ".txt", ".patch"}
RANK = {"unverified": 0, "stale": 0, "in-progress": 1, "verified-with-assumptions": 2, "verified": 3}

cache = {}
def corpus(layer):
    if layer not in cache:
        texts = []
        for rel in DIRS.get(layer, ([], False))[0]:
            p = (d / rel).resolve()
            files = [p] if p.is_file() else (
                f for f in p.rglob("*") if f.is_file() and not (SKIP_DIRS & set(f.relative_to(p).parts))
            ) if p.is_dir() else []
            for f in files:
                if f.suffix in TEXT or f.name.endswith(".expected"):
                    try:
                        texts.append(f.read_text(errors="replace"))
                    except OSError:
                        pass
        text = "\n".join(texts)
        tags = set()
        for line in re.findall(r"PROP:([^\n]*)", text):
            tags.update(re.findall(r"[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+", line))
        cache[layer] = (text, tags)
    return cache[layer]

reviewer = st.get("review", {}).get("spec_reviewer", "").strip()
errors, seen = [], 0

def check(pid, p):
    global seen
    seen += 1
    layer, ev, status = p.get("layer"), p.get("evidence"), p["status"]
    if status not in RANK:
        errors.append(f"{pid}: unknown status {status!r}")
        return
    if layer not in ALLOWED:
        errors.append(f"{pid}: unknown layer {layer!r}")
        return
    if ev is not None and ev not in ALLOWED[layer]:
        errors.append(f"{pid}: evidence {ev!r} not allowed for layer {layer!r} (strategy.md section 12)")
    if RANK[status] == 0:
        return
    dirs, tagged = DIRS[layer]
    if dirs:
        text, tags = corpus(layer)
        if tagged and pid not in tags:
            errors.append(f"{pid}: {status} but no `// PROP: {pid}` tag in {', '.join(dirs)}")
        elif not tagged and not re.search(r"(?<![A-Za-z0-9-])" + re.escape(pid) + r"(?![A-Za-z0-9])", text):
            errors.append(f"{pid}: {status} but {pid} appears nowhere in {', '.join(dirs)}")
    if layer == "kani" and RANK[status] > RANK["verified-with-assumptions"]:
        errors.append(f"{pid}: Kani results are at most verified-with-assumptions")
    if status == "verified" and ev == "proof" and (p.get("assumptions") or []):
        errors.append(f"{pid}: verified with assumptions listed; use verified-with-assumptions")
    if layer in ("kani", "verus") and RANK[status] >= RANK["verified-with-assumptions"] and not reviewer:
        errors.append(f"{pid}: {status} needs [review] spec_reviewer (strategy.md section 12)")

for mod in st.get("modules", {}).values():
    for pid, p in mod.get("properties", {}).items():
        if isinstance(p, dict) and "status" in p:
            check(pid, p)

for e in errors:
    print(f"::error::status-lint: {e}" if os.environ.get("GITHUB_ACTIONS") else f"status-lint: {e}")
print(f"status-lint: {seen} properties, {len(errors)} problem(s)")
sys.exit(1 if errors else 0)
PY
