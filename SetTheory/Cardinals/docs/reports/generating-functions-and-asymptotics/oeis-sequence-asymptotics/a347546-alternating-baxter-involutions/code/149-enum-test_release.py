"""Adversarial and deterministic tests for the Report149 release tools."""
import hashlib
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile
import make_zip
from release_tools import fresh_directory, fresh_file, regular_bytes


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='report149-')
        self.root = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def test_file_exclusive(self):
        target = self.root / 'new'
        with fresh_file(target) as stream:
            stream.write(b'first')
        with self.assertRaises(FileExistsError):
            with fresh_file(target):
                self.fail('Existing file accepted')
        self.assertEqual(target.read_bytes(), b'first')

    def test_file_symlink_refused(self):
        original = self.root / 'original'
        original.write_bytes(b'unchanged')
        link = self.root / 'link'
        link.symlink_to(original)
        with self.assertRaises(OSError):
            with fresh_file(link):
                self.fail('Symlink accepted')
        self.assertEqual(original.read_bytes(), b'unchanged')

    def test_parent_symlink_refused(self):
        folder = self.root / 'folder'
        folder.mkdir()
        link = self.root / 'link'
        link.symlink_to(folder, target_is_directory=True)
        with self.assertRaises(OSError):
            with fresh_file(link / 'new'):
                self.fail('Symlink parent accepted')
        self.assertFalse((folder / 'new').exists())

    def test_directory_exclusive(self):
        target = self.root / 'new'
        with fresh_directory(target):
            self.assertTrue(target.is_dir())
        with self.assertRaises(FileExistsError):
            with fresh_directory(target):
                self.fail('Existing directory accepted')

    def test_directory_symlink_refused(self):
        original = self.root / 'original'
        original.mkdir()
        link = self.root / 'link'
        link.symlink_to(original, target_is_directory=True)
        with self.assertRaises(OSError):
            with fresh_directory(link):
                self.fail('Symlink directory accepted')

    def test_traversal_refused(self):
        with self.assertRaises(ValueError):
            with fresh_file(self.root / 'a' / '..' / 'b'):
                self.fail('Traversal accepted')

    def test_input_symlink_refused(self):
        original = self.root / 'original'
        original.write_bytes(b'data')
        link = self.root / 'link'
        link.symlink_to(original)
        with self.assertRaises(OSError):
            regular_bytes(link)

    def test_fifo_input_rejected(self):
        pipe = self.root / 'fifo'
        os.mkfifo(pipe)
        with self.assertRaisesRegex(ValueError, 'regular file'):
            regular_bytes(pipe)

    def sample_package(self):
        (self.root / 'payload').write_bytes(b'exact bytes')
        digest = hashlib.sha256(b'exact bytes').hexdigest()
        (self.root / 'SHA256SUMS').write_text(digest + '  payload\n', encoding='ascii')

    def test_allowlist_and_determinism(self):
        self.sample_package()
        (self.root / 'unlisted_secret').write_bytes(b'excluded')
        with patch.object(make_zip, 'FILES', ('payload',)):
            content = make_zip.collect(self.root)
        first = make_zip.archive_bytes(content)
        self.assertEqual(first, make_zip.archive_bytes(content))
        with zipfile.ZipFile(io.BytesIO(first)) as archive:
            self.assertEqual(archive.namelist(), ['SHA256SUMS', 'payload'])
            self.assertEqual(archive.read('payload'), b'exact bytes')

    def test_payload_tampering_rejected(self):
        self.sample_package()
        (self.root / 'payload').write_bytes(b'changed')
        with patch.object(make_zip, 'FILES', ('payload',)):
            with self.assertRaisesRegex(ValueError, 'Checksum mismatch'):
                make_zip.collect(self.root)

    def test_manifest_duplicate_rejected(self):
        self.sample_package()
        manifest = self.root / 'SHA256SUMS'
        manifest.write_bytes(manifest.read_bytes() * 2)
        with patch.object(make_zip, 'FILES', ('payload',)):
            with self.assertRaisesRegex(ValueError, 'Duplicate'):
                make_zip.collect(self.root)

    def test_manifest_unlisted_rejected(self):
        self.sample_package()
        with patch.object(make_zip, 'FILES', ('different',)):
            with self.assertRaisesRegex(ValueError, 'allowlist'):
                make_zip.collect(self.root)

    def test_manifest_malformed_rejected(self):
        (self.root / 'SHA256SUMS').write_text('not a manifest\n')
        with self.assertRaisesRegex(ValueError, 'Malformed'):
            make_zip.collect(self.root)


if __name__ == '__main__':
    unittest.main()
