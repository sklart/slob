"""Regression checks for the SLOB corpus shared with the Java reader."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import unittest

import slob


ROOT = Path(__file__).resolve().parents[1] / "fixtures"


class CompatibilityCorpusTest(unittest.TestCase):
    def test_valid_fixtures_match_manifests(self):
        for manifest_path in sorted(ROOT.glob("*.json")):
            with self.subTest(fixture=manifest_path.stem):
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                with slob.open(str(manifest_path.with_suffix(".slob"))) as reader:
                    refs = []
                    payload_sha256 = {}
                    content_types = []
                    for blob in reader:
                        refs.append({"key": blob.key, "id": blob.id, "fragment": blob.fragment})
                        payload_sha256[str(blob.id)] = hashlib.sha256(blob.content).hexdigest()
                        if blob.content_type not in content_types:
                            content_types.append(blob.content_type)
                    self.assertEqual(manifest["compression"], reader.compression)
                    self.assertEqual(manifest["blob_count"], reader.blob_count)
                    self.assertEqual(manifest["refs"], refs)
                    self.assertEqual(manifest["keys"], [ref["key"] for ref in refs])
                    self.assertEqual(manifest["content_types"], content_types)
                    self.assertEqual(manifest["payload_sha256"], payload_sha256)

    def test_corrupted_fixtures_fail_with_expected_type(self):
        expected = {
            "corrupted-lzma2.slob": "LZMAError",
            "corrupted-zlib.slob": "error",
            "invalid-bin-index.slob": "IndexError",
            "invalid-content-type.slob": "IndexError",
            "invalid-item-index.slob": "IndexError",
            "invalid-magic.slob": "UnknownFileFormat",
            "truncated-header.slob": "ValueError",
            "truncated-ref-table.slob": "IncorrectFileSize",
            "truncated-store.slob": "IncorrectFileSize",
            "unknown-compression.slob": "UnknownCompression",
        }
        for name, error_name in expected.items():
            with self.subTest(fixture=name):
                with self.assertRaises(Exception) as context:
                    with slob.open(str(ROOT / "corrupted" / name)) as reader:
                        for blob in reader:
                            blob.content_type
                            blob.content
                self.assertEqual(error_name, type(context.exception).__name__)

    def test_verify_and_info_cli(self):
        script = ROOT.parent / "slob.py"
        valid = subprocess.run(
            [sys.executable, str(script), "verify", str(ROOT / "lzma2.slob"), "--full", "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(0, valid.returncode, valid.stderr)
        self.assertTrue(json.loads(valid.stdout)["valid"])

        invalid = subprocess.run(
            [sys.executable, str(script), "verify",
             str(ROOT / "corrupted" / "invalid-bin-index.slob"), "--json"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(1, invalid.returncode)
        self.assertEqual("IndexError", json.loads(invalid.stdout)["error"]["type"])

        info = subprocess.run(
            [sys.executable, str(script), "info", str(ROOT / "uncompressed.slob")],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(0, info.returncode, info.stderr)
        self.assertIn("CONTENT TYPES", info.stdout)


if __name__ == "__main__":
    unittest.main()
