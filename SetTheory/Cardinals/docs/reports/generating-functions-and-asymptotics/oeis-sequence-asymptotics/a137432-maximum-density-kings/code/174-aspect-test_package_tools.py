#!/usr/bin/env python3
"""Adversarial integrity tests; fixtures contain no report or external sources."""
from pathlib import Path
import tempfile
import sys
import unittest
import warnings
import zipfile

sys.dont_write_bytecode = True

from package_tools import (PAYLOAD_FILES, PackageError, create_zip, extract_zip,
                           json_bytes, make_manifest, require, verify_directory)


class PackageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="Report174-tool-test-")
        self.base = Path(self.temporary.name)
        self.root = self.base/"fixture"
        self.root.mkdir()
        for name in PAYLOAD_FILES:
            path = self.root/name
            path.parent.mkdir(exist_ok=True, parents=True)
            path.write_text("TEST FIXTURE ONLY: "+name+"\n", encoding="utf-8")
        (self.root/"manifest.json").write_bytes(json_bytes(make_manifest(self.root)))

    def tearDown(self):
        self.temporary.cleanup()

    def test_roundtrip_determinism(self):
        one, two = self.base/"one.zip", self.base/"two.zip"
        create_zip(self.root, one)
        create_zip(self.root, two)
        self.assertEqual(one.read_bytes(), two.read_bytes())
        target = extract_zip(one, self.base/"extracted")
        self.assertEqual(verify_directory(self.root), verify_directory(target))

    def test_modified_file_rejected(self):
        path = self.root/PAYLOAD_FILES[0]
        data = path.read_bytes()
        path.write_bytes(bytes([data[0]^1])+data[1:])
        with self.assertRaises(PackageError):
            verify_directory(self.root)

    def test_unexpected_file_rejected(self):
        (self.root/"unlisted.txt").write_text("not allowed")
        with self.assertRaises(PackageError):
            verify_directory(self.root)

    def test_missing_file_rejected(self):
        (self.root/PAYLOAD_FILES[0]).unlink()
        with self.assertRaises(PackageError):
            verify_directory(self.root)

    def test_symlink_rejected(self):
        path = self.root/PAYLOAD_FILES[0]
        original = path.read_bytes()
        path.unlink()
        target = self.base/"target"
        target.write_bytes(original)
        path.symlink_to(target)
        with self.assertRaises(PackageError):
            verify_directory(self.root)

    def test_no_clobber(self):
        archive = self.base/"one.zip"
        create_zip(self.root, archive)
        before = archive.read_bytes()
        with self.assertRaises(FileExistsError):
            create_zip(self.root, archive)
        self.assertEqual(before, archive.read_bytes())
        destination = self.base/"exists"
        destination.mkdir()
        with self.assertRaises(PackageError):
            extract_zip(archive, destination)

    def test_build_no_clobber(self):
        from build_package import build
        before = {str(p.relative_to(self.root)): p.read_bytes()
                  for p in self.root.rglob("*") if p.is_file()}
        with self.assertRaises(PackageError):
            build(self.root, self.root)
        with self.assertRaises(PackageError):
            build(self.root, self.base)
        after = {str(p.relative_to(self.root)): p.read_bytes()
                 for p in self.root.rglob("*") if p.is_file()}
        self.assertEqual(before, after)

    def test_traversal_rejected(self):
        path = self.base/"unsafe.zip"
        with zipfile.ZipFile(path, "w") as archive:
            archive.writestr("../escape.txt", "forbidden")
        with self.assertRaises(PackageError):
            extract_zip(path, self.base/"rejected")
        self.assertFalse((self.base/"escape.txt").exists())

    def test_duplicate_rejected(self):
        path = self.base/"duplicates.zip"
        create_zip(self.root, path)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with zipfile.ZipFile(path, "a") as archive:
                archive.writestr("Report174/README.md", "duplicate")
        with self.assertRaises(PackageError):
            extract_zip(path, self.base/"rejected")

    def test_guard_active(self):
        with self.assertRaises(PackageError):
            require(False, "guard must run under -O")


if __name__ == "__main__":
    unittest.main(verbosity=2)
