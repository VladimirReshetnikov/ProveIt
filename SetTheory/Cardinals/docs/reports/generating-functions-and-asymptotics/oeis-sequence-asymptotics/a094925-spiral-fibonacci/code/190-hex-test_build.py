#!/usr/bin/env python3
"""No-network build/manifest guards, active under ordinary Python and -O.

Compiler behavior is simulated here: this test never invokes TeX, regenerates
mathematical certificates, or writes to the source package. The real build runs
the mathematical verifier and TeX separately.
"""
from __future__ import annotations

import ast
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
from unittest import mock
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
import build
import verify_manifest
import reproduce


class Checks:
    def __init__(self):
        self.accepted = []
        self.rejected = []

    def good(self, label, condition):
        if not condition:
            raise RuntimeError(label)
        self.accepted.append(label)

    def bad(self, label, call, exceptions=(ValueError, build.BuildError, OSError)):
        try:
            call()
        except exceptions:
            self.rejected.append(label)
            return
        raise RuntimeError('expected rejection did not occur: ' + label)


def run_tests():
    checks = Checks()
    with tempfile.TemporaryDirectory(prefix='report190-guards-') as tmp:
        root = Path(tmp)
        source = root / 'source'
        source.mkdir()
        (source / 'Report190.tex').write_bytes(b'deterministic TeX fixture\n')
        (source / 'nested').mkdir()
        (source / 'nested' / 'x.txt').write_bytes(b'good')
        checks.good('regular source', build.safe_source('Report190.tex', source)
                    == source / 'Report190.tex')
        checks.good('nested regular source', build.safe_source('nested/x.txt', source)
                    == source / 'nested' / 'x.txt')
        for name in ('', '.', '..', '../escape', '/absolute', 'a/../b',
                     './report.tex', 'nested//x.txt', 'nested/./x.txt',
                     'nested/x.txt/', 'a\\b', 'C:/drive', 'x\x00y',
                     'x\ny', 'x\ry', 'x\ty', '__pycache__/x',
                     '.pytest_cache/x', '.cache/x', 'x.pyc', 'x.pyo'):
            checks.bad('unsafe source path ' + repr(name),
                       lambda name=name: build.safe_source(name, source))
        checks.bad('missing source', lambda: build.safe_source('missing', source))
        checks.bad('directory as source', lambda: build.safe_source('nested', source))
        (source / 'link').symlink_to(source / 'Report190.tex')
        (source / 'dirlink').symlink_to(source / 'nested', target_is_directory=True)
        (source / 'dangling').symlink_to(source / 'missing')
        for name in ('link', 'dirlink/x.txt', 'dangling'):
            checks.bad('symlinked source ' + name,
                       lambda name=name: build.safe_source(name, source))
        root_link = root / 'source-link'
        root_link.symlink_to(source, target_is_directory=True)
        checks.bad('symlinked source root',
                   lambda: build.safe_source('Report190.tex', root_link))
        if hasattr(os, 'mkfifo'):
            os.mkfifo(source / 'pipe')
            checks.bad('FIFO source', lambda: build.safe_source('pipe', source))
            checks.bad('FIFO read', lambda: verify_manifest.read_regular(source / 'pipe'))

        existing = root / 'existing'
        existing.mkdir()
        sentinel = existing / 'sentinel'
        sentinel.write_bytes(b'preserve')
        checks.bad('existing output directory', lambda: build.build(existing))
        checks.good('existing output preserved', sentinel.read_bytes() == b'preserve')
        existing_file = root / 'existing-file'
        existing_file.write_bytes(b'preserve file')
        checks.bad('existing output file', lambda: build.build(existing_file))
        checks.good('existing file preserved', existing_file.read_bytes() == b'preserve file')
        checks.bad('existing output symlink', lambda: build.build(root_link))
        output_link = root / 'dangling-output'
        output_link.symlink_to(root / 'absent')
        checks.bad('dangling output symlink', lambda: build.build(output_link))
        checks.bad('symlinked output parent', lambda: build.build(root_link / 'new-output'))
        checks.bad('output path traversal', lambda: build.build(source / '..' / 'new-output'))
        checks.bad('missing output parent', lambda: build.build(root / 'absent' / 'new-output'))
        checks.bad('exclusive file write', lambda: build.write_new(sentinel, b'replace'))
        checks.good('exclusive write preserved original', sentinel.read_bytes() == b'preserve')

        base = root / 'base-package'
        base.mkdir()
        (base / 'nested').mkdir()
        (base / 'payload.txt').write_bytes(b'good')
        (base / 'nested' / 'second.txt').write_bytes(b'second')
        manifest_data = build.canonical(verify_manifest.document(base))
        (base / 'SHA256SUMS.json').write_bytes(manifest_data)
        checks.good('valid manifest', verify_manifest.verify(base, expected=('payload.txt', 'nested/second.txt'))
                    ['files_checked'] == 2)
        fixture_number = 0

        def fixture():
            nonlocal fixture_number
            fixture_number += 1
            destination = root / ('fixture%03d' % fixture_number)
            shutil.copytree(base, destination)
            return destination

        def corrupt(label, mutate):
            package = fixture()
            mutate(package)
            checks.bad(label, lambda: verify_manifest.verify(package, expected=('payload.txt', 'nested/second.txt')))

        corrupt('changed payload', lambda p: (p / 'payload.txt').write_bytes(b'changed'))
        corrupt('missing payload', lambda p: (p / 'payload.txt').unlink())
        corrupt('added payload', lambda p: (p / 'extra').write_bytes(b'extra'))
        corrupt('added empty directory', lambda p: (p / 'extra-directory').mkdir())
        corrupt('missing manifest', lambda p: (p / 'SHA256SUMS.json').unlink())
        corrupt('manifest is directory', lambda p: ((p / 'SHA256SUMS.json').unlink(),
                                                   (p / 'SHA256SUMS.json').mkdir()))
        corrupt('symlinked manifest', lambda p: ((p / 'SHA256SUMS.json').unlink(),
                  (p / 'SHA256SUMS.json').symlink_to(base / 'SHA256SUMS.json')))
        corrupt('symlinked payload', lambda p: ((p / 'payload.txt').unlink(),
                  (p / 'payload.txt').symlink_to(base / 'payload.txt')))
        corrupt('symlinked package directory', lambda p: (p / 'linked').symlink_to(base,
                                                                      target_is_directory=True))
        corrupt('package dangling symlink', lambda p: (p / 'dangling').symlink_to(p / 'absent'))
        if hasattr(os, 'mkfifo'):
            corrupt('package FIFO', lambda p: os.mkfifo(p / 'pipe'))
        package_link = root / 'package-link'
        package_link.symlink_to(base, target_is_directory=True)
        checks.bad('symlinked manifest root', lambda: verify_manifest.verify(package_link))
        for cache in ('__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache', '.cache'):
            corrupt('cache directory ' + cache, lambda p, cache=cache: (p / cache).mkdir())
        for cache in ('artifact.pyc', 'artifact.pyo', '.DS_Store'):
            corrupt('cache file ' + cache,
                    lambda p, cache=cache: (p / cache).write_bytes(b'cache'))
        for label, content in (
                ('empty object', '{}'), ('list', '[]'), ('null', 'null'),
                ('string', '"manifest"'), ('invalid syntax', '{'),
                ('trailing JSON', '{} {}'),
                ('duplicate key', '{"payload.txt":"' + '0' * 64 + '","payload.txt":"'
                 + build.sha(b'good') + '"}'),
                ('NaN', '{"payload.txt":NaN}'),
                ('Infinity', '{"payload.txt":Infinity}'),
                ('non-string digest', '{"payload.txt":42}'),
                ('uppercase digest', '{"payload.txt":"' + 'A' * 64 + '"}'),
                ('short digest', '{"payload.txt":"00"}'),
                ('oversized digest', '{"payload.txt":"' + '0' * 65 + '"}'),
                ('nested digest', '{"payload.txt":{}}'),
                ('self hash', '{"SHA256SUMS.json":"' + '0' * 64 + '"}')):
            corrupt('manifest ' + label,
                    lambda p, content=content: (p / 'SHA256SUMS.json').write_text(content))
        for name in ('../escape', '/absolute', './x', 'a//b', 'a/../b',
                     'a\\b', 'C:/x', 'bad\nname', '__pycache__/x', 'a.pyc'):
            corrupt('unsafe manifest path ' + repr(name),
                    lambda p, name=name: (p / 'SHA256SUMS.json').write_bytes(
                        build.canonical({name: '0' * 64})))
        corrupt('invalid UTF-8 manifest', lambda p: (p / 'SHA256SUMS.json').write_bytes(b'\xff'))
        checks.bad('nested duplicate JSON keys', lambda: verify_manifest.load_json(
            '{"outer":{"x":1,"x":2}}'))
        checks.bad('non-finite canonical JSON', lambda: build.canonical({'x': float('nan')}))

        def mutate_manifest(label, mutate):
            def edit(package):
                document = verify_manifest.load_json((package / 'SHA256SUMS.json').read_text())
                mutate(document)
                (package / 'SHA256SUMS.json').write_bytes(build.canonical(document))
            corrupt(label, edit)

        for key, value in [('schema', 'wrong'), ('report', 187), ('report', True),
                           ('algorithm', 'md5'), ('files', []), ('files', {}),
                           ('extra', 'unlisted')]:
            mutate_manifest('manifest schema field ' + key + repr(value),
                            lambda d, key=key, value=value: d.update({key: value}))
        for key in ('schema', 'report', 'algorithm', 'files'):
            mutate_manifest('missing manifest field ' + key, lambda d, key=key: d.pop(key))
        for value in (-1, True, 4.0, '4', None, verify_manifest.MAX_FILE_BYTES + 1, 3):
            mutate_manifest('invalid or wrong byte count ' + repr(value),
                            lambda d, value=value: d['files']['payload.txt'].update({'bytes': value}))
        for value in (42, True, {}, 'A' * 64, '0' * 63, '0' * 65, '0' * 64):
            mutate_manifest('invalid or wrong digest ' + repr(value),
                            lambda d, value=value: d['files']['payload.txt'].update({'sha256': value}))
        for key in ('bytes', 'sha256'):
            mutate_manifest('missing file record field ' + key,
                            lambda d, key=key: d['files']['payload.txt'].pop(key))
        mutate_manifest('extra file record field',
                        lambda d: d['files']['payload.txt'].update({'extra': 1}))
        for value in (None, [], 'digest'):
            mutate_manifest('wrong file record type ' + repr(value),
                            lambda d, value=value: d['files'].update({'payload.txt': value}))
        for name in ('../escape', '/absolute', './x', 'a//b', 'a/../b',
                     'a\\b', 'C:/x', 'bad\nname', '__pycache__/x', 'a.pyc', 'SHA256SUMS.json'):
            mutate_manifest('unsafe schema-valid manifest path ' + repr(name),
                            lambda d, name=name: d['files'].update({name: {'bytes': 0, 'sha256': '0' * 64}}))
        checks.bad('manifest default rejects arbitrary valid inventory', lambda: verify_manifest.verify(base))
        checks.bad('manifest duplicate expected inventory', lambda: verify_manifest.verify(
            base, expected=('payload.txt', 'nested/second.txt', 'payload.txt')))
        rehashed = fixture()
        (rehashed / 'unlisted.txt').write_bytes(b'extra')
        (rehashed / 'SHA256SUMS.json').write_bytes(build.canonical(verify_manifest.document(rehashed)))
        checks.bad('rehashed extra file still rejected', lambda: verify_manifest.verify(
            rehashed, expected=('payload.txt', 'nested/second.txt')))
        checks.bad('bounded regular read', lambda: verify_manifest.read_regular(base / 'payload.txt', 3))
        checks.good('exact regular read bound', verify_manifest.read_regular(base / 'payload.txt', 4) == b'good')
        with mock.patch.object(verify_manifest, 'MAX_FILE_BYTES', 3):
            checks.bad('scanned file size cap', lambda: verify_manifest.scan(base))
        with mock.patch.object(verify_manifest, 'MAX_TOTAL_BYTES', 9):
            checks.bad('aggregate byte cap', lambda: verify_manifest.inventory(base))
            checks.bad('manifest aggregate byte cap', lambda: verify_manifest.verify(
                base, expected=('payload.txt', 'nested/second.txt')))
        with mock.patch.object(verify_manifest, 'MAX_MANIFEST_BYTES', 3):
            checks.bad('manifest byte cap', lambda: verify_manifest.verify(
                base, expected=('payload.txt', 'nested/second.txt')))
        checks.bad('read through symlinked parent', lambda: verify_manifest.read_regular(root_link / 'Report190.tex'))

        first_zip, second_zip = root / 'one.zip', root / 'two.zip'
        build.archive(base, first_zip, expected=('payload.txt', 'nested/second.txt'))
        build.archive(base, second_zip, expected=('payload.txt', 'nested/second.txt'))
        checks.good('deterministic ZIP bytes', first_zip.read_bytes() == second_zip.read_bytes())
        with zipfile.ZipFile(first_zip) as zipped:
            checks.good('sorted exact ZIP inventory', zipped.namelist()
                        == ['SHA256SUMS.json', 'nested/second.txt', 'payload.txt'])
            checks.good('fixed ZIP metadata', all(
                item.date_time == build.ZIP_TIME and item.create_system == 3
                and item.external_attr >> 16 == stat.S_IFREG | 0o644
                and item.compress_type == zipfile.ZIP_STORED
                for item in zipped.infolist()))
        before = first_zip.read_bytes()
        checks.bad('archive never overwrites', lambda: build.archive(base, first_zip, expected=('payload.txt', 'nested/second.txt')))
        checks.good('existing archive preserved', first_zip.read_bytes() == before)
        corrupt_package = fixture()
        (corrupt_package / 'payload.txt').write_bytes(b'changed')
        checks.bad('archive rejects bad manifest',
                   lambda: build.archive(corrupt_package, root / 'bad.zip', expected=('payload.txt', 'nested/second.txt')))
        checks.good('rejected archive not created', not (root / 'bad.zip').exists())

        for label, path in [('inside package', base/'archive.zip'),
                            ('symlink parent', root_link/'archive.zip'),
                            ('traversal', base/'..'/'archive.zip')]:
            checks.bad('archive output ' + label, lambda path=path: build.archive(
                base, path, expected=('payload.txt', 'nested/second.txt')))

        env_root = root / 'env'
        env_root.mkdir()
        with mock.patch.dict(os.environ, {'TEXINPUTS': '/untrusted', 'PYTHONPATH': '/untrusted',
                                           'BIBINPUTS': '/untrusted', 'SOURCE_DATE_EPOCH': '0'}):
            env = build.environment(env_root)
        checks.good('isolated environment', all(key not in env for key in
                                               ('TEXINPUTS', 'PYTHONPATH', 'BIBINPUTS')))
        checks.good('deterministic environment', env['SOURCE_DATE_EPOCH'] == str(build.EPOCH)
                    and env['FORCE_SOURCE_DATE'] == '1' and env['TZ'] == 'UTC'
                    and env['shell_escape'] == 'f' and env['openout_any'] == 'p')
        checks.good('private cache locations', all(Path(env[key]).is_relative_to(env_root)
                    for key in ('HOME', 'TMPDIR', 'TEXMFVAR', 'TEXMFCONFIG',
                                'TEXMFCACHE', 'TEXMFHOME', 'VARTEXFONTS')))
        with mock.patch.object(build, 'run', return_value='{"status":"PASS"}') as runner:
            checks.good('Python result object', build.run_python(base, 'verify.py', [], env, True)
                        == {'status': 'PASS'})
            command = runner.call_args.args[0]
            checks.good('isolated optimized Python flags', command[1:5] == ['-I', '-S', '-B', '-O'])
        for bad_json in ('{}', '{"status":"FAIL"}', '[]',
                         '{"status":"FAIL","status":"PASS"}',
                         '{"status":"PASS","x":NaN}'):
            with mock.patch.object(build, 'run', return_value=bad_json):
                checks.bad('invalid verifier result ' + bad_json,
                           lambda: build.run_python(base, 'verify.py', [], env))
        with mock.patch.object(subprocess, 'run', return_value=subprocess.CompletedProcess(
                ['fixture'], 0, 'ok', '')) as runner:
            checks.good('successful subprocess', build.run(['fixture'], root, env) == 'ok')
            checks.good('subprocess without shell', runner.call_args.kwargs['shell'] is False)
        with mock.patch.object(subprocess, 'run', return_value=subprocess.CompletedProcess(
                ['fixture'], 1, '', 'failed')):
            checks.bad('failed subprocess', lambda: build.run(['fixture'], root, env))

        # Exercise TeX stabilization and log handling without executing TeX.
        tex = root / 'tex-simulation'
        tex.mkdir()
        (tex / 'Report190.aux').write_bytes(b'stable')
        (tex / 'Report190.log').write_text('clean log\n')
        (tex / 'Report190.pdf').write_bytes(b'%PDF-fixture\n')
        with mock.patch.object(build, 'run', return_value='') as runner:
            checks.good('stable compiler output', build.compile_pdf(tex, env) == b'%PDF-fixture\n')
            checks.good('compiler exactly three passes', runner.call_count == 3)
            checks.good('compiler disables shell escape', all('-no-shell-escape' in call.args[0]
                                                              for call in runner.call_args_list))
        benign = 'Package: infwarerr 2019/12/03 v1.5 Providing info/warning/error messages (HO)'
        (tex / 'Report190.log').write_text(benign+'\n')
        with mock.patch.object(build, 'run', return_value=''):
            checks.good('benign warning-support package metadata accepted',
                        build.compile_pdf(tex, env) == b'%PDF-fixture\n')
        for defect in ('There were undefined references', 'There were undefined citations',
                       'Rerun to get cross-references right', 'Label(s) may have changed',
                       'There were multiply-defined labels', 'Overfull \\hbox (1.0pt too wide)',
                       'Missing character: There is no x in font y!',
                       'Underfull \\hbox (badness 10000)', 'LaTeX Warning: fixture', 'LaTeX Font Warning: fixture',
                       'Package hyperref Warning: fixture', 'Class article Warning: fixture',
                       'pdfTeX warning (dest): fixture', 'Warning: fixture',
                       'SomeEngine WARNING: fixture', 'unknown warning about output'):
            (tex / 'Report190.log').write_text(defect)
            with mock.patch.object(build, 'run', return_value=''):
                checks.bad('TeX log defect ' + defect, lambda: build.compile_pdf(tex, env))
        (tex / 'Report190.log').write_text('clean')
        (tex / 'Report190.pdf').write_bytes(b'not PDF')
        with mock.patch.object(build, 'run', return_value=''):
            checks.bad('invalid PDF signature', lambda: build.compile_pdf(tex, env))
        state = 0

        def never_stable(*args, **kwargs):
            nonlocal state
            state += 1
            (tex / 'Report190.aux').write_text(str(state))
            return ''
        with mock.patch.object(build, 'run', side_effect=never_stable):
            checks.bad('unstable TeX auxiliary state', lambda: build.compile_pdf(tex, env))

        # Full orchestration uses synthetic PASS results and PDF bytes. All file,
        # manifest, archive, and publication operations remain real.
        clean = root / 'clean-source'
        clean.mkdir()
        (clean / 'Report190.tex').write_bytes(b'fixture')
        with mock.patch.object(build, 'SOURCES', ('Report190.tex',)):
            checks.good('strict plain source inventory', build.validate_source(clean) is None)
            (clean / 'unexpected').write_bytes(b'rogue')
            checks.bad('source added file', lambda: build.validate_source(clean))
            (clean / 'unexpected').unlink()
            (clean / 'empty-directory').mkdir()
            checks.bad('source empty directory', lambda: build.validate_source(clean))
            (clean / 'empty-directory').rmdir()
            (clean / 'Report190.tex').unlink()
            checks.bad('source missing file', lambda: build.validate_source(clean))
            (clean / 'Report190.tex').mkdir()
            checks.bad('source wrong type', lambda: build.validate_source(clean))
            (clean / 'Report190.tex').rmdir()
            (clean / 'Report190.tex').symlink_to(source / 'Report190.tex')
            checks.bad('source symlink', lambda: build.validate_source(clean))
            (clean / 'Report190.tex').unlink()
            (clean / 'Report190.tex').write_bytes(b'fixture')
            (clean / 'SHA256SUMS.json').write_bytes(build.canonical(verify_manifest.document(clean)))
            with mock.patch.object(build, 'GENERATED', ()):
                checks.good('strict extracted inventory', build.validate_source(clean) is None)
                (clean / 'Report190.tex').write_bytes(b'changed')
                checks.bad('source incorrect hash', lambda: build.validate_source(clean))
                (clean / 'Report190.tex').write_bytes(b'fixture')
                (clean / 'unexpected').write_bytes(b'rogue')
                checks.bad('source manifest extra file', lambda: build.validate_source(clean))
                (clean / 'SHA256SUMS.json').write_bytes(build.canonical(verify_manifest.document(clean)))
                checks.bad('source rehashed but unexpected file', lambda: build.validate_source(clean))

        for script in (name for name in build.SOURCES if name.endswith('.py')):
            tree=ast.parse((Path(__file__).absolute().parent/script).read_text())
            checks.good('no removable assertions in '+script, not any(isinstance(node,ast.Assert) for node in ast.walk(tree)))
        orchestration=root/'orchestration-source'
        orchestration.mkdir()
        (orchestration/'Report190.tex').write_bytes(b'deterministic TeX fixture\n')
        calls = []

        def fake_python(package, script, args, environment, optimized=False):
            calls.append((script, tuple(args), optimized))
            if script == 'verify_manifest.py':
                return verify_manifest.verify(package, expected=build.SOURCES + build.GENERATED)
            if script == 'reproduce.py':
                replay = Path(args[1]) / 'normal'
                replay.mkdir(parents=True)
                (replay / 'exact_checks.json').write_bytes(b'{"status":"passed"}\n')
            return {'status': 'PASS', 'fixture': True}

        with mock.patch.object(build, 'ROOT', orchestration), \
             mock.patch.object(build, 'SOURCES', ('Report190.tex',)), \
             mock.patch.object(build, 'run_python', side_effect=fake_python), \
             mock.patch.object(build, 'prepare_tex'), \
             mock.patch.object(build, 'compile_pdf', return_value=b'%PDF-fixture\n'):
            checks.bad('source root as output', lambda: build.build(orchestration))
            checks.bad('output directly inside source package',
                       lambda: build.build(orchestration / 'inside-output'))
            if os.name == 'posix':
                alias_output = Path('/' + str(orchestration / 'aliased-output'))
                checks.bad('double-slash output alias inside source',
                           lambda: build.build(alias_output))
                with mock.patch.object(build, 'ROOT', Path('/' + str(orchestration))):
                    checks.bad('double-slash source-root alias',
                               lambda: build.build(orchestration / 'root-alias-output'))
            checks.good('direct output rejection preserves source',
                        sorted(p.name for p in orchestration.iterdir()) == ['Report190.tex'])
            nested_source = orchestration / 'nested'
            nested_source.mkdir()
            (nested_source / 'sentinel').write_bytes(b'preserve nested source')
            with mock.patch.object(build, 'SOURCES', ('Report190.tex', 'nested/sentinel')):
                checks.bad('output in source descendant',
                           lambda: build.build(nested_source / 'inside-output'))
            checks.good('nested output rejection preserves source',
                        sorted(p.name for p in orchestration.rglob('*'))
                        == ['Report190.tex', 'nested', 'sentinel']
                        and (nested_source / 'sentinel').read_bytes() == b'preserve nested source')
            (nested_source / 'sentinel').unlink()
            nested_source.rmdir()
            a, b = root / 'build-one', root / 'build-two'
            result_a = build.build(a)
            result_b = build.build(b)
            checks.good('successful orchestration', result_a['status'] == result_b['status'] == 'PASS')
            checks.good('repeated fresh build deterministic', result_a == result_b and all(
                (a / name).read_bytes() == (b / name).read_bytes()
                for name in ('Report190.pdf', 'Report190.tex', 'Report190_code.zip', 'ARTIFACTS.json')))
            checks.good('verification always normal and optimized', all(
                (script, (), optimized) in calls
                for script in ('test_build.py',)
                for optimized in (False, True)))
            checks.good('exact published files', sorted(p.name for p in a.iterdir())
                        == ['ARTIFACTS.json', 'Report190.pdf', 'Report190.tex', 'Report190_code.zip'])
            with zipfile.ZipFile(a / 'Report190_code.zip') as zipped:
                checks.good('published PDF and TeX match archive',
                            zipped.read('Report190.pdf') == (a / 'Report190.pdf').read_bytes()
                            and zipped.read('Report190.tex') == (a / 'Report190.tex').read_bytes())
                info = verify_manifest.load_json(zipped.read('generated/BUILD_INFO.json'))
                checks.good('Report190 build metadata', info['report'] == 190
                            and info['tex_passes'] == 3
                            and info['mandatory_python_dependencies'] == 'standard library only'
                            and info['shell_escape'] is False)
            extracted = root / 'clean-extracted-release'
            extracted.mkdir()
            with zipfile.ZipFile(a / 'Report190_code.zip') as zipped:
                zipped.extractall(extracted)
            extracted_before = build.snapshot(extracted)
            with mock.patch.object(build, 'ROOT', extracted):
                result_extracted = build.build(root / 'build-from-extraction')
            checks.good('clean extracted rebuild deterministic', result_extracted == result_a and all(
                (a / name).read_bytes() == (root / 'build-from-extraction' / name).read_bytes()
                for name in ('Report190.pdf', 'Report190.tex', 'Report190_code.zip', 'ARTIFACTS.json')))
            checks.good('extracted rebuild source unchanged', build.snapshot(extracted) == extracted_before)
            external_receipt = verify_manifest.load_json((a / 'ARTIFACTS.json').read_text())
            checks.good('external receipt exact schema', set(external_receipt) ==
                        {'schema', 'report', 'algorithm', 'files'} and
                        external_receipt['schema'] == 'report190-artifacts-v1' and
                        external_receipt['report'] == 190 and external_receipt['algorithm'] == 'sha256')
            checks.good('external receipt exact inventory', set(external_receipt['files']) ==
                        {'Report190.pdf', 'Report190.tex', 'Report190_code.zip'})
            checks.good('external receipt sizes and hashes', all(
                        row == {'bytes': len((a / name).read_bytes()),
                                'sha256': build.sha((a / name).read_bytes())}
                        for name, row in external_receipt['files'].items()))
            original_source = (orchestration / 'Report190.tex').read_bytes()
            def changing_source(*args):
                (orchestration / 'Report190.tex').write_bytes(b'changed concurrently')
                return b'%PDF-fixture\n'
            with mock.patch.object(build, 'compile_pdf', side_effect=changing_source):
                checks.bad('source mutation during build', lambda: build.build(root/'source-mutation'))
            checks.good('mutated-source build not published', not (root/'source-mutation').exists())
            (orchestration / 'Report190.tex').write_bytes(original_source)
            published_before = {p.name: p.read_bytes() for p in a.iterdir()}
            checks.bad('repeat build refuses publication', lambda: build.build(a))
            checks.good('repeat build leaves everything unchanged', published_before
                        == {p.name: p.read_bytes() for p in a.iterdir()})
            with mock.patch.object(build, 'SOURCES', ('Report190.tex', 'Report190.tex')):
                checks.bad('duplicate source inventory', lambda: build.build(root / 'duplicate'))
            with mock.patch.object(build, 'compile_pdf', side_effect=build.BuildError('synthetic failure')):
                checks.bad('compile failure', lambda: build.build(root / 'failed-build'))
            checks.good('failed build not published', not (root / 'failed-build').exists())
            with mock.patch.object(build, 'run_python', side_effect=lambda *a, **k:
                                   {'status': 'PASS', 'optimized': a[4] if len(a) > 4 else False}):
                checks.bad('normal optimized disagreement', lambda: build.build(root / 'disagreement'))
            checks.good('disagreement not published', not (root / 'disagreement').exists())
            race = root / 'race-output'

            def racing_archive(package, target, expected=None):
                race.mkdir()
                (race / 'sentinel').write_bytes(b'racing writer')
                target.write_bytes(b'archive fixture')
            with mock.patch.object(build, 'archive', side_effect=racing_archive):
                checks.bad('racing output creation', lambda: build.build(race))
            checks.good('racing writer preserved', (race / 'sentinel').read_bytes() == b'racing writer'
                        and [p.name for p in race.iterdir()] == ['sentinel'])
        # Reproduction has the same non-overwrite and source-immutability rules.
        replay_source = root / 'replay-source'
        replay_source.mkdir()
        (replay_source / 'Report190.tex').write_bytes(b'fixture')
        datum = b'{"status":"passed","arithmetic":"integer and Fraction only"}\n'
        def fake_replay(root_path, output, optimized):
            output.write_bytes(datum)
            return datum
        with mock.patch.object(build, 'SOURCES', ('Report190.tex',)), \
             mock.patch.object(reproduce, 'run_script', side_effect=fake_replay):
            for label, path in [('existing directory', existing), ('existing file', existing_file),
                                ('dangling link', output_link), ('linked parent', root_link/'replay'),
                                ('traversal', replay_source/'..'/'replay'),
                                ('inside source', replay_source/'output')]:
                checks.bad('reproduce ' + label, lambda path=path: reproduce.run(replay_source, path))
            before = verify_manifest.inventory(replay_source)
            result = reproduce.run(replay_source, root / 'replay-good')
            checks.good('reproduce successful normal optimized replay', result['status'] == 'PASS')
            checks.good('reproduction source unchanged', before == verify_manifest.inventory(replay_source))
            with mock.patch.object(reproduce, 'run_script', side_effect=[datum, b'corrupt']):
                checks.bad('reproduce mismatched output', lambda: reproduce.run(replay_source, root/'replay-bad'))
            checks.good('failed reproduction not published', not (root/'replay-bad').exists())
        script_destination = root / 'script-output.json'
        script_destination.write_bytes(datum)
        completed = subprocess.CompletedProcess(['fixture'], 0, datum, b'')
        with mock.patch.object(subprocess, 'run', return_value=completed) as runner:
            checks.good('exact subprocess reads matching byte output',
                        reproduce.run_script(replay_source, script_destination, True) == datum)
            command = runner.call_args.args[0]
            checks.good('exact subprocess isolated optimized flags', command[1:5] == ['-I', '-S', '-B', '-O'])
            checks.good('exact subprocess passes explicit output', command[-2:] == ['--output', str(script_destination)])
            checks.good('exact subprocess has no shell', runner.call_args.kwargs['shell'] is False)
        for label, status, stdout, filedata in [
                ('failure', 1, datum, datum), ('stdout mismatch', 0, b'wrong', datum),
                ('wrong status', 0, b'{"status":"PASS"}', b'{"status":"PASS"}'),
                ('wrong arithmetic', 0, b'{"status":"passed","arithmetic":"float"}',
                 b'{"status":"passed","arithmetic":"float"}'),
                ('duplicate key', 0, b'{"status":"failed","status":"passed"}',
                 b'{"status":"failed","status":"passed"}')]:
            script_destination.write_bytes(filedata)
            completed = subprocess.CompletedProcess(['fixture'], status, stdout, b'')
            with mock.patch.object(subprocess, 'run', return_value=completed):
                checks.bad('exact subprocess ' + label,
                           lambda: reproduce.run_script(replay_source, script_destination, False))
        checks.good('temporary replay workspaces removed',not list(root.glob('report190-replay-*')))
        checks.good('temporary build workspaces removed', not list(root.glob('report190-build-*')))
    return {'status': 'PASS', 'acceptance_tests': len(checks.accepted),
            'rejection_tests': len(checks.rejected),
            'total_tests': len(checks.accepted) + len(checks.rejected),
            'compiler_invoked': False, 'network_required': False}


def main():
    try:
        print(json.dumps(run_tests(), sort_keys=True))
    except Exception as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
