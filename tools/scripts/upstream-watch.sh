#!/usr/bin/env bash
# Reports watched upstream paths that changed since their `seen` commit
# (tools/upstream-watch.toml). Prints a Markdown report on stdout and exits
# 0 when nothing changed, 1 when something did, 2 on error.
#
# usage: tools/scripts/upstream-watch.sh
set -uo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

python3 -I - "$root/tools/upstream-watch.toml" "$work" <<'PY'
import subprocess, sys, tomllib
cfg = tomllib.load(open(sys.argv[1], "rb"))
work = sys.argv[2]
changed, out = False, []

def git(*a, cwd=None):
    return subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=True, check=True).stdout

for w in cfg["watch"]:
    d = f"{work}/{w['name']}"
    try:
        git("init", "-q", d)
        git("remote", "add", "origin", w["repo"], cwd=d)
        git("fetch", "-q", "--filter=blob:none", "origin", "HEAD", cwd=d)
        head = git("rev-parse", "FETCH_HEAD", cwd=d).strip()
        if head == w["seen"]:
            continue
        git("fetch", "-q", "--filter=blob:none", "origin", w["seen"], cwd=d)
        stat = git("diff", "--stat", w["seen"], head, "--", *w["paths"], cwd=d).strip()
        log = git("log", "--format=- %h %s (%cs)", f"{w['seen']}..{head}", "--", *w["paths"], cwd=d).strip()
    except subprocess.CalledProcessError as e:
        print(f"error checking {w['name']}: {e.stderr.strip()}", file=sys.stderr)
        sys.exit(2)
    if not stat:
        continue
    changed = True
    out.append(f"## {w['name']}: `{w['seen'][:12]}` → `{head[:12]}`\n\n{w['why']}\n\n"
               f"Repo: {w['repo']}\n\nCommits touching watched paths:\n\n{log}\n\n"
               f"```\n{stat}\n```\n\nAfter review, set `seen = \"{head}\"` in `tools/upstream-watch.toml`.\n")
print("\n".join(out) if out else "No watched upstream path changed.")
sys.exit(1 if changed else 0)
PY
