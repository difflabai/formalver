#!/usr/bin/env python3
"""Lockfile rule (strategy.md section 9): every package that appears in both
the sandbox Cargo.lock and the mirror's contracts/approval/Cargo.lock must
have the same version(s) and checksum(s). Exit 1 on any difference."""
import sys, tomllib, pathlib

here = pathlib.Path(__file__).resolve().parent.parent
mine = tomllib.loads((here / "Cargo.lock").read_text())["package"]
theirs = tomllib.loads(
    (here.parent / "source-mirror/contracts/approval/Cargo.lock").read_text()
)["package"]

def index(pkgs):
    out = {}
    for p in pkgs:
        if "source" not in p:  # workspace members
            continue
        out.setdefault(p["name"], {})[p["version"]] = p.get("checksum")
    return out

a, b = index(mine), index(theirs)
bad = []
for name in sorted(a.keys() & b.keys()):
    for ver, sum_ in a[name].items():
        if ver not in b[name]:
            bad.append(f"{name} {ver}: mirror has {sorted(b[name])}")
        elif b[name][ver] != sum_:
            bad.append(f"{name} {ver}: checksum differs")
for line in bad:
    print("lockfile mismatch:", line)
print(f"check-lock: {len(a.keys() & b.keys())} shared packages, {len(bad)} mismatches")
sys.exit(1 if bad else 0)
