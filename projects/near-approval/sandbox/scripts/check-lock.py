#!/usr/bin/env python3
"""Lockfile rule (strategy.md section 9): every package that appears in both
the sandbox Cargo.lock and the mirror's contracts/approval/Cargo.lock must
have the same version(s) and checksum(s). Exit 1 on any difference.

The sandbox lockfile may lead the pin on AHEAD_OF_PIN. Those crates are the
host TLS stack (ureq, used to fetch near-sandbox), not the contract wasm.
Re-pinning would change the contract artifact. Delete an entry once the
mirror has that version. The script fails if you leave it."""
import sys, tomllib, pathlib

# rustls-webpki 0.103.16 rejects the compromised intermediate keys.
# webpki-roots 1.0.11 drops the emSign roots (RUSTSEC-2026-0382). The pin
# still has 0.103.15 and 1.0.9.
# rustls 0.23.46 patches RUSTSEC-2026-0346, -0347, -0348 and -0349. The pin
# still has 0.23.45.
AHEAD_OF_PIN = {
    "rustls": {"0.23.46"},
    "rustls-webpki": {"0.103.16"},
    "webpki-roots": {"1.0.11"},
}

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
ahead = []
for name in sorted(a.keys() & b.keys()):
    for ver, sum_ in a[name].items():
        if ver not in b[name]:
            if ver in AHEAD_OF_PIN.get(name, ()):
                ahead.append(f"{name} {ver}: mirror has {sorted(b[name])}")
            else:
                bad.append(f"{name} {ver}: mirror has {sorted(b[name])}")
        elif b[name][ver] != sum_:
            bad.append(f"{name} {ver}: checksum differs")
for name, vers in sorted(AHEAD_OF_PIN.items()):
    if name in b and vers <= set(b[name]):
        bad.append(f"drop AHEAD_OF_PIN[{name!r}], mirror has caught up")
for line in ahead:
    print("lockfile ahead of pin:", line)
for line in bad:
    print("lockfile mismatch:", line)
print(f"check-lock: {len(a.keys() & b.keys())} shared packages, {len(bad)} mismatches")
sys.exit(1 if bad else 0)
