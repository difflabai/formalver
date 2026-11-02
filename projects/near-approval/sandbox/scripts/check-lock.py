#!/usr/bin/env python3
"""Check shared sandbox/mirror dependency versions, sources and checksums.

Explicit host-TLS backports allow the sandbox to lead the reviewed pin.
When upstream catches up, normal equality applies; an unused exception is
not an error. Other version drift and checksum/source mismatches fail closed.
"""
import argparse
import json
import pathlib
import sys
import tomllib

# Only these exact sandbox/mirror pairs are approved. These are host-side
# TLS updates, not a change to the reviewed contract pin or wasm artifact.
# rustls 0.23.46 patches RUSTSEC-2026-0346 through -0349 (PR #26).
# rustls-webpki 0.103.16 and webpki-roots 1.0.11 carry the earlier eMudhra
# distrust update (RUSTSEC-2026-0382). Equality needs no backport exception.
HOST_TLS_BACKPORTS = {
    "rustls": ("0.23.46", {"0.23.45"}),
    "rustls-webpki": ("0.103.16", {"0.103.15"}),
    "webpki-roots": ("1.0.11", {"1.0.9"}),
}


def index(packages):
    out = {}
    for package in packages:
        if "source" not in package:  # workspace members
            continue
        versions = out.setdefault(package["name"], {})
        version = package["version"]
        if version in versions:
            raise ValueError(f"ambiguous package {package['name']} {version}")
        versions[version] = (package["source"], package.get("checksum"))
    return out


def compare(mine, theirs):
    a, b = index(mine), index(theirs)
    bad, ahead = [], []
    for name in sorted(a.keys() & b.keys()):
        for version, (source, checksum) in a[name].items():
            if version in b[name]:
                other_source, other_checksum = b[name][version]
                if source != other_source:
                    bad.append(f"{name} {version}: source differs")
                elif checksum != other_checksum:
                    bad.append(f"{name} {version}: checksum differs")
                continue
            allowed_version, old_versions = HOST_TLS_BACKPORTS.get(name, (None, set()))
            # Exceptions do not permit a different source or arbitrary newer
            # upstream versions. Equality above always checks checksums.
            if (version == allowed_version and set(b[name]) <= old_versions
                    and all(other_source == source for other_source, _ in b[name].values())):
                ahead.append(f"{name} {version}: approved host-TLS backport; mirror has {sorted(b[name])}")
            else:
                bad.append(f"{name} {version}: mirror has {sorted(b[name])}")
    return {"shared_packages": len(a.keys() & b.keys()), "mismatches": bad, "backports": ahead}


def main():
    here = pathlib.Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sandbox-lock", type=pathlib.Path, default=here / "Cargo.lock")
    parser.add_argument("--mirror-lock", type=pathlib.Path,
                        default=here.parent / "source-mirror/contracts/approval/Cargo.lock")
    parser.add_argument("--source-ref", default="")
    parser.add_argument("--json", type=pathlib.Path, help="write a diagnostic report, including on input errors")
    args = parser.parse_args()
    report = {"sandbox_lock": str(args.sandbox_lock), "mirror_lock": str(args.mirror_lock),
              "source_ref": args.source_ref}
    try:
        mine = tomllib.loads(args.sandbox_lock.read_text())["package"]
        theirs = tomllib.loads(args.mirror_lock.read_text())["package"]
        report.update(compare(mine, theirs))
        code = 1 if report["mismatches"] else 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        report["error"] = str(error)
        print(f"check-lock: cannot compare lockfiles: {error}", file=sys.stderr)
        code = 2
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    if "error" not in report:
        for line in report["backports"]:
            print("lockfile ahead of pin:", line)
        for line in report["mismatches"]:
            print("lockfile mismatch:", line)
        print(f"check-lock: {report['shared_packages']} shared packages, {len(report['mismatches'])} mismatches")
        if code:
            print("Update the sandbox lockfile against the selected mirror revision; do not remove --locked.")
    return code


if __name__ == "__main__":
    sys.exit(main())
