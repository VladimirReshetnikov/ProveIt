#!/usr/bin/env python3
"""Finite adversarial guard tests; run with python -B, normally or under -O.

No source changes are made. Temporary files are created outside the package.
Every child Python interpreter is called with -B and the decimal digit cap 640.
"""
from __future__ import annotations
import argparse
import importlib.util
import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from record_sum import ROOT, decimal_coefficients, emit, finite_counts, inverse_model, new_file_path, tree_log_coefficient

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)


def tests():
    passed = []
    spec = importlib.util.spec_from_file_location('report234_build', ROOT / 'build.py')
    build = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build)

    def reject(label, call):
        try:
            call()
        except (ValueError, OSError, RuntimeError):
            passed.append(label)
            return
        raise RuntimeError('guard failed: ' + label)

    for value in (-1, 201, True, 1.0):
        reject('finite n rejects ' + repr(value), lambda v=value: finite_counts(v))
    for n, d in ((0, 60), (6001, 60), (60, 19), (60, 201)):
        reject('Decimal cutoff rejects %s' % ((n, d),), lambda n=n, d=d: decimal_coefficients(n, d))
    for q, d in ((0, 0), (42, 0), (1, -1), (1, 41)):
        reject('tree cutoff rejects %s' % ((q, d),), lambda q=q, d=d: tree_log_coefficient(q, d))
    for target in ('nan', 'inf', '-inf', '9', '1000000000001', '1' * 641):
        reject('inverse target rejects ' + (target if len(target) < 30 else 'overlong input'),
               lambda target=target: inverse_model(target))
    reject('inverse order rejects K=4', lambda: inverse_model('1000', 4))
    reject('inverse precision cap', lambda: inverse_model('1000', digits=201))
    reject('inverse step cap', lambda: inverse_model('1000', max_steps=101))
    reject('inverse nonconvergence is explicit', lambda: inverse_model('1000', max_steps=1))

    with tempfile.TemporaryDirectory(prefix='report234-guards-') as tmp:
        work = Path(tmp)
        existing = work / 'existing'
        existing.write_text('untouched', encoding='utf-8')
        directory = work / 'directory'
        directory.mkdir()
        live = work / 'live'
        live.symlink_to(directory, target_is_directory=True)
        dangling = work / 'dangling'
        dangling.symlink_to(work / 'missing', target_is_directory=True)
        unsafe = [str(existing), str(directory), str(ROOT / 'forbidden.json'),
                  str(live / 'out.json'), str(dangling / 'out.json'),
                  str(work) + '/directory/../out.json', str(work) + '/./out.json',
                  str(work / 'missing-parent' / 'out.json')]
        for index, path in enumerate(unsafe):
            reject('file path guard %d' % index, lambda path=path: new_file_path(path))
            reject('directory path guard %d' % index, lambda path=path: build.new_output(path))
        destination = work / 'valid.json'
        emit({'ok': True}, str(destination))
        reject('exclusive output refuses reuse', lambda: emit({'ok': False}, str(destination)))
        if existing.read_text() != 'untouched' or 'true' not in destination.read_text():
            raise RuntimeError('existing output was modified')
        passed.append('preexisting files remain unchanged')
        env = os.environ.copy()
        env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONINTMAXSTRDIGITS='640', PYTHONHASHSEED='0')
        child = [sys.executable, '-B'] + (['-' + 'O' * sys.flags.optimize] if sys.flags.optimize else [])
        commands = [
            [str(ROOT / 'code/record_sum.py'), 'exact', '--n', '201'],
            [str(ROOT / 'code/record_sum.py'), 'brute', '--n', '9'],
            [str(ROOT / 'code/record_sum.py'), 'inverse', '--log-y', 'nan'],
            [str(ROOT / 'code/record_sum.py'), 'exact', '--output', str(existing)],
            [str(ROOT / 'code/checks.py'), '--output', str(live / 'bad')],
            [str(ROOT / 'build.py'), '--output-dir', str(dangling / 'bad')],
            [str(ROOT / 'build.py'), '--verify-only', '--output-dir', str(work / 'unused')],
        ]
        for index, command in enumerate(commands):
            result = subprocess.run(child + command, env=env, capture_output=True, check=False)
            if result.returncode == 0:
                raise RuntimeError('CLI guard accepted invalid input %d' % index)
            passed.append('CLI rejects invalid case %d' % index)
        if (work / 'unused').exists():
            raise RuntimeError('invalid CLI created an output directory')
        # Validate the manifest parser against fresh inert fixtures. No fixture
        # Python or TeX is executed; each mutation gets its own directory.
        required = ('README.md', 'SOURCES.md', 'article.tex', 'Report234.pdf', 'build.py',
                    'code/checks.py', 'code/record_sum.py', 'code/guard_tests.py',
                    'code/reproduce_zip.py', 'code/receipt.json', 'code/guard_receipt.json',
                    'sections/example.tex')
        serial = 0
        def fixture():
            nonlocal serial
            serial += 1
            root = work / ('manifest-fixture-%d' % serial)
            root.mkdir()
            lines = []
            for name in required:
                target = root / name
                target.parent.mkdir(exist_ok=True)
                target.write_bytes(b'inert fixture\n')
                lines.append(hashlib.sha256(target.read_bytes()).hexdigest() + '  ' + name)
            (root / 'MANIFEST.sha256').write_text('\n'.join(lines) + '\n', encoding='utf-8')
            build.ROOT = root
            return root
        original_root = build.ROOT
        try:
            fixture()
            build.verify()
            passed.append('valid complete manifest verifies')
            mutations = [
                ('changed bytes', lambda root: (root / 'README.md').write_text('changed')),
                ('extra file', lambda root: (root / 'extra').write_text('extra')),
                ('extra empty directory', lambda root: (root / 'extra').mkdir()),
                ('missing file', lambda root: (root / 'README.md').unlink()),
                ('symlink file', lambda root: (root / 'extra').symlink_to(root / 'README.md')),
                ('symlink directory', lambda root: (root / 'extra').symlink_to(root / 'code', target_is_directory=True)),
            ]
            for label, mutate in mutations:
                root = fixture()
                mutate(root)
                reject('manifest rejects ' + label, build.verify)
            bad_lines = ['0' * 64 + '  ../escape', '0' * 64 + '  ./dot',
                         '0' * 64 + '  /absolute', '0' * 64 + '  code\\bad',
                         '0' * 64 + '  MANIFEST.sha256', 'g' * 64 + '  file',
                         'malformed line']
            for index, line in enumerate(bad_lines):
                root = fixture()
                manifest = root / 'MANIFEST.sha256'
                manifest.write_text(manifest.read_text() + line + '\n')
                reject('manifest rejects malformed entry %d' % index, build.verify)
            root = fixture()
            manifest = root / 'MANIFEST.sha256'
            manifest.write_text(manifest.read_text() + manifest.read_text().splitlines()[0] + '\n')
            reject('manifest rejects duplicate entry', build.verify)
            root = fixture()
            (root / 'MANIFEST.sha256').write_text('')
            reject('manifest rejects empty entries', build.verify)
            root = fixture()
            (root / 'README.md').unlink()
            manifest = root / 'MANIFEST.sha256'
            manifest.write_text('\n'.join(line for line in manifest.read_text().splitlines()
                                           if not line.endswith('  README.md')) + '\n')
            reject('manifest rejects missing required file even with matching hashes', build.verify)
        finally:
            build.ROOT = original_root
    return {'status': 'PASS', 'guard_count': len(passed), 'guards': passed,
            'integer_decimal_digit_cap': sys.get_int_max_str_digits(),
            'scope': 'Finite boundary and filesystem guard tests; not a general security proof.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(tests(), args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError) as exc:
        raise SystemExit(str(exc))
