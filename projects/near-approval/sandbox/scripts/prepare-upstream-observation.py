#!/usr/bin/env python3
"""Adapt only RT-CODEHASH's artifact identity for an unreviewed upstream run.

The runtime test still checks deployed bytes and on-chain code_hash. Export
surface and behavioral observations keep their reviewed expected values.
Pinned runs never call this script and retain the independent pinned hash.
"""
import argparse
import hashlib
import json
import pathlib
import re


def artifact_identity(data):
    digest = hashlib.sha256(data).digest()
    number = int.from_bytes(digest, "big")
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    encoded = ""
    while number:
        number, remainder = divmod(number, 58)
        encoded = alphabet[remainder] + encoded
    encoded = "1" * (len(digest) - len(digest.lstrip(b"\0"))) + encoded
    return {"bytes": len(data), "wasm_sha256": digest.hex(), "code_hash": encoded}


def prepare(wasm, source_ref, results, report):
    if not re.fullmatch(r"[0-9a-f]{40}", source_ref):
        raise ValueError("upstream source_ref must be a full commit SHA")
    path = results / "RT-CODEHASH.json"
    expected = json.loads(path.read_text())
    identity = artifact_identity(wasm.read_bytes())
    original = {key: expected[key] for key in identity}
    expected.update(identity)
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps({"source_ref": source_ref, "reviewed_artifact": original,
                                 "upstream_artifact": identity}, indent=2) + "\n")
    path.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
    return identity["wasm_sha256"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wasm", type=pathlib.Path, required=True)
    parser.add_argument("--source-ref", required=True)
    parser.add_argument("--results", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parent.parent / "results")
    parser.add_argument("--report", type=pathlib.Path, required=True)
    args = parser.parse_args()
    print(prepare(args.wasm, args.source_ref, args.results, args.report))


if __name__ == "__main__":
    main()
