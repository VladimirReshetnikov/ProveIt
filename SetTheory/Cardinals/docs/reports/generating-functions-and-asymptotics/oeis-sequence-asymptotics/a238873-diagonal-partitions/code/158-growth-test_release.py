"""Output safety and deterministic-archive regression tests for Report158."""
import hashlib
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile
import make_zip
from release_tools import fresh_directory, fresh_file, regular_bytes, write_member


class ReleaseTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix='report158-test-')
        self.root = Path(self.directory.name)

    def tearDown(self):
        self.directory.cleanup()

    def test_file_is_exclusive(self):
        target = self.root / 'new'
        with fresh_file(target) as output:
            output.write(b'keep')
        with self.assertRaises(FileExistsError):
            with fresh_file(target):
                self.fail('Overwrite permitted')
        self.assertEqual(target.read_bytes(), b'keep')

    def test_destination_and_parent_links_refused(self):
        original = self.root / 'original'
        original.write_bytes(b'keep')
        (self.root / 'link').symlink_to(original)
        with self.assertRaises(OSError):
            with fresh_file(self.root / 'link'):
                self.fail('Link accepted')
        folder = self.root / 'folder'
        folder.mkdir()
        (self.root / 'folder-link').symlink_to(folder, target_is_directory=True)
        with self.assertRaises(OSError):
            with fresh_file(self.root / 'folder-link' / 'new'):
                self.fail('Parent link accepted')
        self.assertEqual(original.read_bytes(), b'keep')
        self.assertFalse((folder / 'new').exists())

    def test_directory_is_exclusive_and_pinned(self):
        target = self.root / 'new'
        with fresh_directory(target) as (_, fd):
            write_member(fd, 'member', b'content')
            with self.assertRaises(ValueError):
                write_member(fd, '../bad', b'no')
        self.assertEqual((target / 'member').read_bytes(), b'content')
        with self.assertRaises(FileExistsError):
            with fresh_directory(target):
                self.fail('Existing directory accepted')
        (self.root / 'dirlink').symlink_to(target, target_is_directory=True)
        with self.assertRaises(OSError):
            with fresh_directory(self.root / 'dirlink'):
                self.fail('Directory link accepted')

    def test_special_output_paths_refused(self):
        os.mkfifo(self.root / 'pipe')
        (self.root / 'folder').mkdir()
        (self.root / 'dangling').symlink_to(self.root / 'absent')
        for name in ('pipe', 'folder', 'dangling'):
            with self.subTest(name=name):
                with self.assertRaises(OSError):
                    with fresh_file(self.root / name):
                        self.fail('Special output destination accepted')
        self.assertFalse((self.root / 'absent').exists())

    def test_file_parent_race_stays_pinned(self):
        parent = self.root / 'parent'
        parent.mkdir()
        moved = self.root / 'moved'
        outside = self.root / 'outside'
        outside.mkdir()
        original_open = os.open
        raced = []
        def swap(path, flags, *args, **kwargs):
            if path == 'new' and flags & os.O_WRONLY and not raced:
                parent.rename(moved)
                parent.symlink_to(outside, target_is_directory=True)
                raced.append(True)
            return original_open(path, flags, *args, **kwargs)
        with patch('release_tools.os.open', side_effect=swap):
            with fresh_file(parent / 'new') as output:
                output.write(b'pinned')
        self.assertEqual(raced, [True])
        self.assertEqual((moved / 'new').read_bytes(), b'pinned')
        self.assertFalse((outside / 'new').exists())

    def test_directory_parent_race_stays_pinned(self):
        parent = self.root / 'parent'
        parent.mkdir()
        moved = self.root / 'moved'
        outside = self.root / 'outside'
        outside.mkdir()
        original_mkdir = os.mkdir
        raced = []
        def swap(path, *args, **kwargs):
            if path == 'new' and not raced:
                parent.rename(moved)
                parent.symlink_to(outside, target_is_directory=True)
                raced.append(True)
            return original_mkdir(path, *args, **kwargs)
        with patch('release_tools.os.mkdir', side_effect=swap):
            with fresh_directory(parent / 'new') as (_, fd):
                write_member(fd, 'member', b'pinned')
        self.assertEqual(raced, [True])
        self.assertEqual((moved / 'new' / 'member').read_bytes(), b'pinned')
        self.assertFalse((outside / 'new').exists())

    def test_traversal_refused(self):
        with self.assertRaises(ValueError):
            with fresh_file(self.root / 'a' / '..' / 'bad'):
                self.fail('Traversal accepted')

    def test_regular_input_required(self):
        target = self.root / 'file'
        target.write_bytes(b'input')
        self.assertEqual(regular_bytes(target), b'input')
        (self.root / 'link').symlink_to(target)
        with self.assertRaises(OSError):
            regular_bytes(self.root / 'link')
        os.mkfifo(self.root / 'pipe')
        with self.assertRaisesRegex(ValueError, 'regular'):
            regular_bytes(self.root / 'pipe')

    def sample(self):
        (self.root / 'payload').write_bytes(b'content')
        digest = hashlib.sha256(b'content').hexdigest()
        (self.root / 'SHA256SUMS').write_text(digest + '  payload\n', encoding='ascii')

    def test_allowlist_and_zip_determinism(self):
        self.sample()
        (self.root / 'unlisted').write_bytes(b'private')
        with patch.object(make_zip, 'FILES', ('payload',)):
            payload = make_zip.collect(self.root)
        first = make_zip.archive_bytes(payload)
        self.assertEqual(first, make_zip.archive_bytes(payload))
        with zipfile.ZipFile(io.BytesIO(first)) as archive:
            self.assertEqual(archive.namelist(), ['SHA256SUMS', 'payload'])
            self.assertEqual(archive.read('payload'), b'content')
            self.assertEqual(archive.getinfo('payload').date_time, (2026, 10, 3, 0, 0, 0))
            self.assertEqual(archive.getinfo('payload').compress_type, zipfile.ZIP_STORED)

    def test_payload_tampering_rejected(self):
        self.sample()
        (self.root / 'payload').write_bytes(b'changed')
        with patch.object(make_zip, 'FILES', ('payload',)):
            with self.assertRaisesRegex(ValueError, 'Checksum mismatch'):
                make_zip.collect(self.root)

    def test_manifest_mutations_rejected(self):
        self.sample()
        manifest = self.root / 'SHA256SUMS'
        original = manifest.read_bytes()
        cases = [original + original, b'garbage\n', original.replace(b'payload', b'other')]
        for content in cases:
            manifest.write_bytes(content)
            with patch.object(make_zip, 'FILES', ('payload',)):
                with self.assertRaises(ValueError):
                    make_zip.collect(self.root)


if __name__ == '__main__':
    unittest.main()
