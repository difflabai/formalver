#!/usr/bin/env python3
"""Regression coverage for reviewed pins and floating scheduled upstreams."""
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
SCRIPT = pathlib.Path(__file__).with_name("check-lock.py")
spec = importlib.util.spec_from_file_location("check_lock", SCRIPT)
check_lock = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_lock)
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"
identity_spec = importlib.util.spec_from_file_location(
    "upstream_observation", SCRIPT.with_name("prepare-upstream-observation.py"))
identity = importlib.util.module_from_spec(identity_spec)
identity_spec.loader.exec_module(identity)


def package(name, version, checksum="same", source=REGISTRY):
    return {"name": name, "version": version, "checksum": checksum, "source": source}


class LockfileTests(unittest.TestCase):
    def test_upstream_adaptation_changes_only_artifact_identity(self):
        with tempfile.TemporaryDirectory() as folder:
            path = pathlib.Path(folder)
            wasm = path / "contract.wasm"
            wasm.write_bytes(b"\0asm\x01\0\0\0")
            expected = {"bytes": 1, "wasm_sha256": "old", "code_hash": "old",
                        "function_exports": ["approve"], "reproducible": True}
            observation = path / "RT-CODEHASH.json"
            observation.write_text(json.dumps(expected))
            behavior = path / "RT-REVERT.json"
            behavior.write_text('{"behavior": "must not change"}')
            sha = identity.prepare(wasm, "a" * 40, path, path / "report.json")
            adjusted = json.loads(observation.read_text())
            self.assertEqual(adjusted["wasm_sha256"], sha)
            for key in ["function_exports", "reproducible"]:
                self.assertEqual(adjusted[key], expected[key])
            self.assertEqual(behavior.read_text(), '{"behavior": "must not change"}')
            with self.assertRaises(ValueError):
                identity.prepare(wasm, "not-a-sha", path, path / "report.json")

    def test_reported_failure_and_upstream_catch_up(self):
        ours = [package("rustls", "0.23.46"), package("rustls-webpki", "0.103.16"),
                package("webpki-roots", "1.0.11")]
        self.assertEqual(check_lock.compare(ours, ours)["mismatches"], [])
        self.assertEqual(check_lock.compare(ours, ours)["backports"], [])
        stale = [package("rustls", "0.23.45"), *ours[1:]]
        self.assertEqual(len(check_lock.compare(stale, ours)["mismatches"]), 1)

    def test_exact_backports_still_match_reviewed_pin(self):
        for name, (version, old_versions) in check_lock.HOST_TLS_BACKPORTS.items():
            with self.subTest(name=name):
                result = check_lock.compare([package(name, version)],
                                            [package(name, old) for old in old_versions])
                self.assertEqual(result["mismatches"], [])
                self.assertEqual(len(result["backports"]), 1)

    def test_future_tls_drift_is_rejected(self):
        result = check_lock.compare([package("rustls", "0.23.46")], [package("rustls", "0.23.47")])
        self.assertEqual(len(result["mismatches"]), 1)

    def test_checksum_and_source_mismatches_fail_even_for_backports(self):
        for name, (version, old_versions) in check_lock.HOST_TLS_BACKPORTS.items():
            with self.subTest(name=name):
                for other in [package(name, version, checksum="different"),
                              package(name, version, source="registry+https://other.invalid"),
                              package(name, next(iter(old_versions)), source="registry+https://other.invalid")]:
                    self.assertTrue(check_lock.compare([package(name, version)], [other])["mismatches"])

    def test_non_tls_drift_is_rejected(self):
        self.assertTrue(check_lock.compare([package("near-sdk", "5.29.1")],
                                           [package("near-sdk", "5.30.0")])["mismatches"])

    def test_multiple_versions_are_checked_individually(self):
        ours = [package("example", "1.0.0"), package("example", "2.0.0")]
        self.assertEqual(len(check_lock.compare(ours, ours[:1])["mismatches"]), 1)

    def test_json_report_and_missing_input_fail_closed(self):
        with tempfile.TemporaryDirectory() as folder:
            path = pathlib.Path(folder)
            lock = path / "Cargo.lock"
            lock.write_text('version = 4\n[[package]]\nname = "example"\nversion = "1.0.0"\n'
                            f'source = "{REGISTRY}"\nchecksum = "same"\n')
            report = path / "report.json"
            command = [sys.executable, str(SCRIPT), "--sandbox-lock", str(lock), "--mirror-lock",
                       str(lock), "--json", str(report), "--source-ref", "test-upstream"]
            good = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(good.returncode, 0, good.stderr)
            self.assertEqual(json.loads(report.read_text())["source_ref"], "test-upstream")
            lock.unlink()
            bad = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(bad.returncode, 2)
            self.assertIn("error", json.loads(report.read_text()))


if __name__ == "__main__":
    unittest.main()
