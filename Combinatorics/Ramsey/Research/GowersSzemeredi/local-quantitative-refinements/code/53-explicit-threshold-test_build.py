"""Bounded-build, exact-inventory, archive and no-follow regression tests."""
import sys
sys.dont_write_bytecode = True
import ast
import hashlib
import importlib.util
import os
from pathlib import Path
import stat
import tempfile
import unittest
from unittest.mock import patch
import zipfile
ROOT = Path(__file__).absolute().parents[1]
spec = importlib.util.spec_from_file_location('report281_build', ROOT / 'build.py')
b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
PDF = b'%PDF-1.5\nsmall test fixture\n%%EOF\n'


def make_source(root, distribution=False):
    root.mkdir()
    for name in b.SOURCE_FILES:
        path = root / name; path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(('fixture ' + name + '\n').encode())
    if distribution:
        (root / b.PDF_NAME).write_bytes(PDF)
        files = {n: (root / n).read_bytes() for n in b.PUBLIC_FILES}
        (root / b.MANIFEST_NAME).write_bytes(b.manifest_bytes(files))
    return root


class InventoryTests(unittest.TestCase):
    def test_report_identity_and_exact_allowlists(self):
        self.assertEqual(b.PDF_NAME, 'Report281.pdf')
        self.assertEqual(b.ZIP_NAME, 'report281_uniform_density_square.zip')
        self.assertEqual(b.PIN_NAME, b.ZIP_NAME + '.sha256')
        self.assertEqual({n for n in b.SOURCE_FILES if not n.startswith('provenance/')},
            {'README.md', 'SOURCES.md', 'article.tex', 'build.py',
             'companion/exact_checks.py', 'tests/test_companion.py', 'tests/test_build.py'})
        self.assertEqual(len(b.SOURCE_FILES), 31)
        self.assertEqual(len(b.SOURCE_FILES), len(set(b.SOURCE_FILES)))
        self.assertIn('provenance/source_manifest.json', b.SOURCE_FILES)
        self.assertEqual(sum(n.startswith('provenance/sources/') for n in b.SOURCE_FILES),23)
        self.assertTrue(all(n.endswith('.lean') or n == 'provenance/source_manifest.json'
                            for n in b.SOURCE_FILES if n.startswith('provenance/')))
        self.assertFalse(any('receipt' in n or 'comparison' in n for n in b.SOURCE_FILES))
        self.assertEqual(set(b.PUBLIC_FILES), set(b.SOURCE_FILES) | {b.PDF_NAME})

    def test_exact_source_and_distribution_inventory(self):
        with tempfile.TemporaryDirectory(prefix='report281-inventory-') as tmp:
            root = make_source(Path(tmp) / 'source')
            with patch.object(b, 'ROOT', root):
                self.assertEqual(set(b.verified_snapshot()), set(b.SOURCE_FILES))
                with self.assertRaises(RuntimeError): b.verify_manifest()
                (root / 'extra').write_bytes(b'x')
                with self.assertRaises(RuntimeError): b.verified_snapshot()
                (root / 'extra').unlink(); (root / 'empty').mkdir()
                with self.assertRaises(RuntimeError): b.verified_snapshot()
                (root / 'empty').rmdir()
                (root / b.PDF_NAME).write_bytes(PDF)
                with self.assertRaises(RuntimeError): b.verified_snapshot()
                (root / b.MANIFEST_NAME).write_bytes(b.manifest_bytes({n: (root / n).read_bytes() for n in b.PUBLIC_FILES}))
                self.assertEqual(set(b.verify_manifest()), set(b.PUBLIC_FILES))
                (root / 'article.tex').write_bytes(b'changed')
                with self.assertRaisesRegex(RuntimeError, 'integrity'): b.verify_manifest()

    def test_malformed_manifests(self):
        d = hashlib.sha256(b'one').hexdigest()
        cases = [b'', b'\xff', b'x' * (128 * 1024 + 1)]
        cases += [s.encode() for s in (
            d + ' one\n', d + '\tone\n', 'g' * 64 + '  one\n', d.upper() + '  one\n',
            d[:-1] + '  one\n', d + '0  one\n', d + '  \n', d + '  /one\n',
            d + '  ./one\n', d + '  ../one\n', d + '  a/../one\n', d + '  a/./one\n',
            d + '  a//one\n', d + '  one/\n', d + '  a\\one\n', d + '  MANIFEST.sha256\n',
            d + '  one\n\n', d + '  one', d + '  one\r\n',
            d + '  one\n' + d + '  one\n', d + '  two\n' + d + '  one\n')]
        for data in cases:
            with self.subTest(data=data[:80]):
                with self.assertRaises(RuntimeError): b._parse_manifest(data)
        self.assertEqual(b._parse_manifest((d + '  one\n').encode()), {'one': d})

    def test_manifest_cannot_choose_new_allowlist(self):
        with tempfile.TemporaryDirectory(prefix='report281-manifest-') as tmp:
            root = make_source(Path(tmp) / 'source', True)
            (root / b.MANIFEST_NAME).write_bytes(b.manifest_bytes({'invented': b'x'}))
            with patch.object(b, 'ROOT', root):
                with self.assertRaisesRegex(RuntimeError, 'allowlist'): b.verify_manifest()

    def test_symlinks_and_nonregular_entries_refused(self):
        for kind in ('file-link', 'directory-link', 'dangling', 'fifo'):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory(prefix='report281-entry-') as tmp:
                root = Path(tmp) / 'source'; root.mkdir(); target = root / 'bad'
                if kind == 'fifo': os.mkfifo(target)
                else: target.symlink_to('/tmp' if kind == 'directory-link' else '/etc/passwd' if kind == 'file-link' else root / 'missing')
                with patch.object(b, 'ROOT', root):
                    with self.assertRaises(RuntimeError): b.snapshot()

    def test_source_and_manifest_hardlink_aliases_refused(self):
        for name in ('article.tex', b.MANIFEST_NAME):
            for external in (False, True):
                with self.subTest(name=name, external=external), tempfile.TemporaryDirectory(prefix='report281-link-') as tmp:
                    base = Path(tmp); root = make_source(base / 'source', True)
                    alias = (base if external else root) / 'alias'; os.link(root / name, alias)
                    with patch.object(b, 'ROOT', root):
                        with self.assertRaises(RuntimeError): b.snapshot()
                    self.assertEqual((root / name).read_bytes(), alias.read_bytes())

    def test_file_and_entry_caps(self):
        with tempfile.TemporaryDirectory(prefix='report281-limits-') as tmp:
            root = Path(tmp) / 'source'; root.mkdir()
            for i in range(3): (root / str(i)).write_bytes(b'xx')
            with patch.object(b, 'ROOT', root), patch.object(b, 'MAX_ENTRIES', 2):
                with self.assertRaisesRegex(RuntimeError, 'entry limit'): b.snapshot()
            with patch.object(b, 'ROOT', root), patch.object(b, 'MAX_SOURCE_BYTES', 4):
                with self.assertRaisesRegex(RuntimeError, 'source byte limit'): b.snapshot()
            fd = b._open_directory(root)
            try:
                with self.assertRaisesRegex(RuntimeError, 'file byte limit'): b._read_regular(fd, '0', 1)
            finally: os.close(fd)

    def test_snapshot_root_is_pinned_after_rename(self):
        with tempfile.TemporaryDirectory(prefix='report281-root-swap-') as tmp:
            base = Path(tmp); root = base / 'source'; root.mkdir(); (root / 'one').write_bytes(b'checked')
            target = base / 'target'; target.mkdir(); (target / 'one').write_bytes(b'untrusted')
            old = base / 'old'; original = b._open_directory
            def swapped(path, create=False):
                fd = original(path, create)
                if Path(path) == root:
                    root.rename(old); root.symlink_to(target, target_is_directory=True)
                return fd
            with patch.object(b, 'ROOT', root), patch.object(b, '_open_directory', side_effect=swapped):
                self.assertEqual(b.snapshot()[0], {'one': b'checked'})
            self.assertEqual((target / 'one').read_bytes(), b'untrusted')

    def test_source_file_swap_before_open_rejected(self):
        with tempfile.TemporaryDirectory(prefix='report281-source-race-') as tmp:
            root = Path(tmp); (root / 'one').write_bytes(b'checked'); original = b.os.stat
            fd = b._open_directory(root); swapped = False
            def replace(path, *args, **kwargs):
                nonlocal swapped
                info = original(path, *args, **kwargs)
                if path == 'one' and kwargs.get('dir_fd') == fd and not swapped:
                    swapped = True; (root / 'one').unlink(); (root / 'one').symlink_to('/etc/passwd')
                return info
            try:
                with patch.object(b.os, 'stat', side_effect=replace):
                    with self.assertRaises(OSError): b._read_regular(fd, 'one')
            finally: os.close(fd)


class OutputTests(unittest.TestCase):
    def test_invalid_output_locations(self):
        for value in (None, False, 17, '', str(ROOT), str(ROOT / 'child'), str(ROOT.parent),
            '/', '/tmp', '/workspace', '/workspace/shared', '/etc/report281', '/usr/report281',
            '/root/report281', 'relative', '~/out', '//tmp/out', '/tmp/../out', '/tmp/./out', '/tmp/a\\b'):
            with self.subTest(value=value):
                with self.assertRaises(ValueError): b.output_directory(value)

    def test_empty_directory_creation_and_nonempty_refusal(self):
        with tempfile.TemporaryDirectory(prefix='report281-output-') as tmp:
            base = Path(tmp); out = base / 'fresh'
            self.assertEqual(b.output_directory(str(out)), out)
            (out / 'sentinel').write_bytes(b'keep')
            with self.assertRaises(ValueError): b.output_directory(out)
            link = base / 'link'; link.symlink_to(out, target_is_directory=True)
            with self.assertRaises(ValueError): b.output_directory(link / 'new')
            file = base / 'file'; file.write_bytes(b'file')
            with self.assertRaises(ValueError): b.output_directory(file)
            self.assertEqual((out / 'sentinel').read_bytes(), b'keep')

    def test_public_functions_reject_source_and_nonempty_outputs(self):
        with tempfile.TemporaryDirectory(prefix='report281-public-') as tmp:
            out = Path(tmp); (out / 'keep').write_bytes(b'keep')
            for callback in (b.compile_pdf, b.package_zip, b.reproduce):
                for value in (ROOT, ROOT / 'child', out):
                    with self.subTest(callback=callback.__name__, value=value), patch.object(b, 'run') as run:
                        with self.assertRaises(ValueError): callback(value)
                        run.assert_not_called()
            self.assertEqual((out / 'keep').read_bytes(), b'keep')

    def test_exclusive_writes_never_overwrite_existing_destinations(self):
        with tempfile.TemporaryDirectory(prefix='report281-exclusive-') as tmp:
            base = Path(tmp); sentinel = base / 'sentinel'; sentinel.write_bytes(b'keep')
            for kind in ('regular', 'symlink', 'dangling', 'hardlink'):
                path = base / kind
                if kind == 'regular': path.write_bytes(b'old')
                elif kind == 'hardlink': os.link(sentinel, path)
                else: path.symlink_to(sentinel if kind == 'symlink' else base / 'missing')
                with self.subTest(kind=kind):
                    with self.assertRaises(FileExistsError): b._write_exclusive(path, b'bad')
            self.assertEqual(sentinel.read_bytes(), b'keep')

    def test_output_read_rejects_hardlinks_and_fifo(self):
        with tempfile.TemporaryDirectory(prefix='report281-output-read-') as tmp:
            base = Path(tmp); path = base / 'file'; path.write_bytes(b'keep'); os.link(path, base / 'alias')
            os.mkfifo(base / 'fifo')
            for target in (path, base / 'fifo'):
                with self.assertRaises(RuntimeError): b._output_bytes(target)

    def test_pinned_parent_after_rename(self):
        with tempfile.TemporaryDirectory(prefix='report281-held-') as tmp:
            base = Path(tmp); out = base / 'output'; out.mkdir(); old = base / 'old'
            target = base / 'target'; target.mkdir(); (target / 'one').write_bytes(b'sentinel')
            original = b._open_directory
            def swapped(path, create=False):
                fd = original(path, create)
                if Path(path) == out:
                    out.rename(old); out.symlink_to(target, target_is_directory=True)
                return fd
            with patch.object(b, '_open_directory', side_effect=swapped): b._write_exclusive(out / 'one', b'result')
            self.assertEqual((target / 'one').read_bytes(), b'sentinel')
            self.assertEqual((old / 'one').read_bytes(), b'result')

    def test_parent_symlink_swap_before_write_refused(self):
        with tempfile.TemporaryDirectory(prefix='report281-parent-swap-') as tmp:
            base = Path(tmp); out = base / 'output'; out.mkdir(); target = base / 'target'; target.mkdir()
            (target / 'one').write_bytes(b'keep'); out.rename(base / 'old'); out.symlink_to(target, target_is_directory=True)
            with self.assertRaises(OSError): b._write_exclusive(out / 'one', b'bad')
            with self.assertRaises(OSError): b._open_directory(out / 'new', create=True)
            self.assertEqual(list(target.iterdir()), [target / 'one'])
            self.assertEqual((target / 'one').read_bytes(), b'keep')

    def test_unsupported_platform_fails_closed(self):
        with patch.object(b.os, 'name', 'unsupported'):
            with self.assertRaises(RuntimeError): b._require_posix_handles()


class ProcessTests(unittest.TestCase):
    def test_environment_is_allowlisted_and_digit_limit_is_local_to_children(self):
        contaminants = {name: 'untrusted' for name in ('TEXINPUTS', 'TEXMFHOME', 'MIKTEX_USERCONFIG',
            'BIBINPUTS', 'BSTINPUTS', 'VARTEXFONTS', 'PYTHONPATH', 'PYTHONHOME', 'PYTHONSTARTUP',
            'PYTHONINSPECT', 'LD_PRELOAD', 'LD_LIBRARY_PATH', 'BASH_ENV', 'ENV', 'SHELLOPTS', 'PATH')}
        before = sys.get_int_max_str_digits()
        with patch.dict(b.os.environ, contaminants): env = b.environment()
        self.assertTrue(all(n not in env for n in contaminants if n != 'PATH'))
        self.assertEqual(env['PATH'], '/usr/bin:/bin')
        self.assertEqual(env['PYTHONINTMAXSTRDIGITS'], '640')
        self.assertEqual(env['SOURCE_DATE_EPOCH'], b.EPOCH)
        self.assertEqual(env['TZ'], 'UTC'); self.assertEqual(env['LC_ALL'], 'C')
        self.assertEqual(sys.get_int_max_str_digits(), before)
        with tempfile.TemporaryDirectory(prefix='report281-digit-') as tmp:
            base = Path(tmp)
            stdout = b.run([sys.executable, '-B', '-c', 'import sys; print(sys.get_int_max_str_digits())'],
                           base, env, base / 'log')
            self.assertEqual(stdout, b'640\n')

    def test_normal_and_optimized_gates_do_not_use_assert(self):
        tree = ast.parse((ROOT / 'build.py').read_text())
        self.assertFalse(any(isinstance(n, ast.Assert) for n in ast.walk(tree)))
        self.assertNotIn('set_int_max_str_digits(', (ROOT / 'build.py').read_text())

    def test_strict_parameter_caps_and_argv(self):
        for name, values in (('timeout', (True, 0, -1, 1.5, 901, '10')),
                             ('output_limit', (True, 0, -1, 1.5, b.MAX_LOG_BYTES + 1, '100'))):
            for value in values:
                with self.subTest(name=name, value=value):
                    with self.assertRaises(ValueError): b.run([sys.executable, '-c', 'pass'], ROOT, b.environment(), '/tmp/never-written', **{name: value})
        for command in ('python -c pass', [], ['python', '-c', 'pass'], [sys.executable, None], [sys.executable, '\x00'], [sys.executable] * 65):
            with self.subTest(command=command):
                with self.assertRaises(ValueError): b.run(command, ROOT, b.environment(), '/tmp/never-written')

    def test_bounded_stdout_and_stderr(self):
        for target in ('stdout', 'stderr'):
            with self.subTest(target=target), tempfile.TemporaryDirectory(prefix='report281-pipe-') as tmp:
                base = Path(tmp)
                code = 'import sys; sys.' + target + '.write("x"*200000)'
                with self.assertRaisesRegex(RuntimeError, 'output limit'):
                    b.run([sys.executable, '-B', '-c', code], base, b.environment(), base / 'log', output_limit=1024)
                self.assertLessEqual((base / 'log').stat().st_size, 1024)

    def test_timeout_is_enforced(self):
        with tempfile.TemporaryDirectory(prefix='report281-timeout-') as tmp:
            base = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, 'timeout'):
                b.run([sys.executable, '-B', '-c', 'import time; time.sleep(10)'], base, b.environment(), base / 'log', timeout=1)

    def test_nonzero_exit_logs_and_fails(self):
        with tempfile.TemporaryDirectory(prefix='report281-exit-') as tmp:
            base = Path(tmp)
            with self.assertRaisesRegex(RuntimeError, 'command failed'):
                b.run([sys.executable, '-B', '-c', 'import sys; print("diagnostic"); sys.exit(3)'], base, b.environment(), base / 'log')
            self.assertIn(b'diagnostic', (base / 'log').read_bytes())

    def test_actual_subprocess_cwd_is_pinned(self):
        with tempfile.TemporaryDirectory(prefix='report281-cwd-') as tmp:
            base = Path(tmp); work = base / 'work'; work.mkdir(); old = base / 'old'
            target = base / 'target'; target.mkdir(); (target / 'result').write_bytes(b'sentinel')
            original = b.subprocess.Popen
            def swapped(*args, **kwargs):
                work.rename(old); work.symlink_to(target, target_is_directory=True)
                return original(*args, **kwargs)
            command = [sys.executable, '-B', '-c', 'from pathlib import Path; Path("result").write_bytes(b"result")']
            with patch.object(b.subprocess, 'Popen', side_effect=swapped): b.run(command, work, b.environment(), base / 'log')
            self.assertEqual((old / 'result').read_bytes(), b'result')
            self.assertEqual((target / 'result').read_bytes(), b'sentinel')


class ArchiveTests(unittest.TestCase):
    def test_deterministic_archive_exact_members_and_actual_pin(self):
        with tempfile.TemporaryDirectory(prefix='report281-zip-') as tmp:
            base = Path(tmp); root = make_source(base / 'source', True)
            one = base / 'one'; one.mkdir(); two = base / 'two'; two.mkdir()
            with patch.object(b, 'ROOT', root):
                before = b.inventory(); digest = b.package_zip(one)
                self.assertEqual(digest, b.package_zip(two)); self.assertEqual(b.inventory(), before)
            data = (one / b.ZIP_NAME).read_bytes()
            self.assertEqual(data, (two / b.ZIP_NAME).read_bytes())
            self.assertEqual(hashlib.sha256(data).hexdigest(), digest)
            self.assertEqual((one / b.PIN_NAME).read_text(), digest + '  ' + b.ZIP_NAME + '\n')
            with zipfile.ZipFile(one / b.ZIP_NAME) as archive:
                expected = [b.ARCHIVE_ROOT + n for n in sorted((*b.PUBLIC_FILES, b.MANIFEST_NAME))]
                self.assertEqual(archive.namelist(), expected); self.assertIsNone(archive.testzip())
                self.assertEqual(len(archive.infolist()), len(b.PUBLIC_FILES) + 1)
                for info in archive.infolist():
                    self.assertEqual(info.date_time, b.FIXED_TIME)
                    self.assertEqual(info.create_system, 3)
                    self.assertEqual(info.external_attr, (stat.S_IFREG | 0o644) << 16)
                    self.assertEqual(info.compress_type, zipfile.ZIP_DEFLATED)
                    self.assertFalse(info.flag_bits & 1); self.assertFalse(info.extra); self.assertFalse(info.comment)

    def test_package_requires_pinned_distribution(self):
        with tempfile.TemporaryDirectory(prefix='report281-unpinned-') as tmp:
            base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
            with patch.object(b, 'ROOT', root):
                with self.assertRaisesRegex(RuntimeError, 'manifest-pinned'): b.package_zip(out)
            self.assertEqual(list(out.iterdir()), [])

    def test_archive_rejects_missing_extra_and_changed_members(self):
        with tempfile.TemporaryDirectory(prefix='report281-bad-zip-') as tmp:
            base = Path(tmp); root = make_source(base / 'source', True)
            source = {n: (root / n).read_bytes() for n in (*b.PUBLIC_FILES, b.MANIFEST_NAME)}
            for mode in ('missing', 'extra', 'changed'):
                members = source.copy(); out = base / mode; out.mkdir()
                if mode == 'missing': members.pop('README.md')
                elif mode == 'extra': members['extra'] = b'extra'
                else: members['article.tex'] = b'changed'
                with self.subTest(mode=mode):
                    with self.assertRaises(RuntimeError): b._package_zip_stage(out, members)
                self.assertEqual(list(out.iterdir()), [])


class CompilerAndReplayTests(unittest.TestCase):
    def test_destination_preflight(self):
        names = (b.PDF_NAME, 'tex-work', 'tex-format.log', 'tex-pass-1.log', 'tex-pass-2.log')
        with tempfile.TemporaryDirectory(prefix='report281-preflight-') as tmp:
            base = Path(tmp); sentinel = base / 'sentinel'; sentinel.write_bytes(b'keep')
            for i, name in enumerate(names):
                for kind in ('regular', 'symlink', 'dangling'):
                    out = base / (str(i) + kind); out.mkdir(); entry = out / name
                    if kind == 'regular': entry.write_bytes(b'existing')
                    else: entry.symlink_to(sentinel if kind == 'symlink' else base / 'missing')
                    with self.subTest(name=name, kind=kind), patch.object(b, 'run') as run:
                        with self.assertRaises(ValueError): b._compile_pdf_stage(out, {'article.tex': b'tex'})
                        run.assert_not_called()
                    self.assertEqual(sentinel.read_bytes(), b'keep')
                    self.assertEqual([p.name for p in out.iterdir()], [name])

    def test_compile_uses_snapshot_and_restricted_tex_flags(self):
        with tempfile.TemporaryDirectory(prefix='report281-compile-') as tmp:
            base = Path(tmp); out = base / 'out'; out.mkdir(); (out / 'unrelated').write_bytes(b'keep')
            def fake(command, cwd, env, logfile, timeout=b.MAX_TIMEOUT):
                self.assertEqual(cwd, out / 'tex-work')
                self.assertEqual((cwd / 'article.tex').read_bytes(), b'checked source')
                self.assertIn('-no-shell-escape', command)
                self.assertEqual(env['openin_any'], 'p'); self.assertEqual(env['openout_any'], 'p')
                self.assertEqual(env['shell_escape'], 'f'); self.assertEqual(env['MKTEXFMT'], '0')
                (cwd / 'article.log').write_text('Clean log'); (cwd / 'article.pdf').write_bytes(PDF)
                return b''
            with patch.object(b, 'run', side_effect=fake) as run:
                self.assertEqual(b._compile_pdf_stage(out, {'article.tex': b'checked source'}), hashlib.sha256(PDF).hexdigest())
                self.assertEqual(run.call_count, 3)
            self.assertEqual((out / 'unrelated').read_bytes(), b'keep')

    def test_tex_quality_gates_and_pdf_header(self):
        for defect in ('Overfull \\hbox', 'Overfull \\vbox', 'There were undefined references',
                       'There were multiply-defined labels', 'Rerun to get cross-references right',
                       'LaTeX Warning: Citation', 'invalid PDF'):
            with self.subTest(defect=defect), tempfile.TemporaryDirectory(prefix='report281-quality-') as tmp:
                out = Path(tmp)
                def fake(command, cwd, env, logfile):
                    (cwd / 'article.log').write_text(defect)
                    (cwd / 'article.pdf').write_bytes(b'bad' if defect == 'invalid PDF' else PDF)
                    return b''
                with patch.object(b, 'run', side_effect=fake):
                    with self.assertRaises(RuntimeError): b._compile_pdf_stage(out, {'article.tex': b'source'})
                self.assertFalse((out / b.PDF_NAME).exists())

    def test_late_pdf_symlink_collision(self):
        with tempfile.TemporaryDirectory(prefix='report281-late-pdf-') as tmp:
            base = Path(tmp); out = base / 'out'; out.mkdir(); sentinel = base / 'sentinel'; sentinel.write_bytes(b'keep')
            def fake(command, cwd, env, logfile):
                (cwd / 'article.log').write_text('Clean log'); (cwd / 'article.pdf').write_bytes(PDF)
                if not (out / b.PDF_NAME).is_symlink(): (out / b.PDF_NAME).symlink_to(sentinel)
                return b''
            with patch.object(b, 'run', side_effect=fake):
                with self.assertRaises(FileExistsError): b._compile_pdf_stage(out, {'article.tex': b'source'})
            self.assertEqual(sentinel.read_bytes(), b'keep')

    def test_replay_runs_both_modes_and_records_matching_stdout(self):
        with tempfile.TemporaryDirectory(prefix='report281-replay-') as tmp:
            base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
            calls = []
            def fake_run(command, cwd, env, logfile):
                calls.append(command)
                self.assertEqual(env['PYTHONINTMAXSTRDIGITS'], '640')
                self.assertEqual(cwd, out / 'check-work')
                return b'stable stdout\n'
            def fake_compile(output, source):
                b._write_exclusive(output / b.PDF_NAME, PDF)
                return hashlib.sha256(PDF).hexdigest()
            with patch.object(b, 'ROOT', root), patch.object(b, 'run', side_effect=fake_run), patch.object(b, '_compile_pdf_stage', side_effect=fake_compile):
                before = b.inventory(); receipt = b.reproduce(out); self.assertEqual(b.inventory(), before)
            self.assertEqual(len(calls), 6)
            self.assertEqual(sum('-O' in c for c in calls), 3)
            self.assertEqual([c[-1] for c in calls[:3]], ['tests/test_build.py', 'tests/test_companion.py', 'companion/exact_checks.py'])
            self.assertTrue(receipt['matching_stdout']); self.assertTrue(receipt['source_unchanged'])
            self.assertEqual(hashlib.sha256((out / b.ZIP_NAME).read_bytes()).hexdigest(), receipt['zip_sha256'])

    def test_optimized_stdout_mismatch_blocks_compilation(self):
        with tempfile.TemporaryDirectory(prefix='report281-mode-mismatch-') as tmp:
            base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
            def fake(command, cwd, env, logfile): return b'changed' if '-O' in command else b'normal'
            with patch.object(b, 'ROOT', root), patch.object(b, 'run', side_effect=fake), patch.object(b, '_compile_pdf_stage') as compile_pdf:
                with self.assertRaisesRegex(RuntimeError, 'stdout differs'): b.reproduce(out)
                compile_pdf.assert_not_called()


class MutationTests(unittest.TestCase):
    def test_staged_mutation_stops_before_next_command_or_compilation(self):
        for mode in ('changed', 'extra', 'deleted', 'empty-directory', 'symlink', 'hardlink'):
            with self.subTest(mode=mode), tempfile.TemporaryDirectory(prefix='report281-mutation-') as tmp:
                base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
                calls = []
                def mutate(command, cwd, env, logfile):
                    calls.append(command)
                    if mode == 'changed': (cwd / 'article.tex').write_bytes(b'changed')
                    elif mode == 'extra': (cwd / 'unlisted').write_bytes(b'new')
                    elif mode == 'deleted': (cwd / 'article.tex').unlink()
                    elif mode == 'empty-directory': (cwd / 'extra').mkdir()
                    elif mode == 'symlink': (cwd / 'link').symlink_to(cwd / 'article.tex')
                    else: os.link(cwd / 'article.tex', cwd / 'alias')
                    return b'good stdout is insufficient'
                with patch.object(b, 'ROOT', root), patch.object(b, 'run', side_effect=mutate), patch.object(b, '_compile_pdf_stage') as compile_pdf:
                    with self.assertRaises(RuntimeError): b.reproduce(out)
                    self.assertEqual(len(calls), 1)
                    compile_pdf.assert_not_called()

    def test_original_source_mutation_stops_immediately(self):
        with tempfile.TemporaryDirectory(prefix='report281-original-mutation-') as tmp:
            base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
            calls = []
            def mutate(command, cwd, env, logfile):
                calls.append(command)
                (root / 'article.tex').write_bytes(b'changed original')
                return b'identical stdout'
            with patch.object(b, 'ROOT', root), patch.object(b, 'run', side_effect=mutate), patch.object(b, '_compile_pdf_stage') as compile_pdf:
                with self.assertRaisesRegex(RuntimeError, 'source inventory'): b.reproduce(out)
                self.assertEqual(len(calls), 1)
                compile_pdf.assert_not_called()

    def test_optimized_only_mutation_is_caught(self):
        with tempfile.TemporaryDirectory(prefix='report281-optimized-mutation-') as tmp:
            base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
            calls = []
            def mutate(command, cwd, env, logfile):
                calls.append(command)
                if '-O' in command: (cwd / 'extra').write_bytes(b'changed')
                return b'identical stdout'
            with patch.object(b, 'ROOT', root), patch.object(b, 'run', side_effect=mutate), patch.object(b, '_compile_pdf_stage') as compile_pdf:
                with self.assertRaisesRegex(RuntimeError, 'staged source inventory'): b.reproduce(out)
                self.assertEqual(len(calls), 4)
                compile_pdf.assert_not_called()

    def test_mutation_on_failed_test_is_still_detected(self):
        with tempfile.TemporaryDirectory(prefix='report281-failed-mutation-') as tmp:
            base = Path(tmp); root = make_source(base / 'source'); out = base / 'out'; out.mkdir()
            def mutate(command, cwd, env, logfile):
                (cwd / 'article.tex').write_bytes(b'changed')
                raise RuntimeError('test failure')
            with patch.object(b, 'ROOT', root), patch.object(b, 'run', side_effect=mutate), patch.object(b, '_compile_pdf_stage') as compile_pdf:
                with self.assertRaisesRegex(RuntimeError, 'staged source inventory'): b.reproduce(out)
                compile_pdf.assert_not_called()


if __name__ == '__main__':
    unittest.main()
