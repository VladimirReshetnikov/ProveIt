#!/usr/bin/env python3
"""Verify and reproduce the frozen Report 230 package without changing its files."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent
FIXED_TIME = (2026, 10, 5, 0, 0, 0)
EPOCH = '1791158400'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory():
    files = {}
    for path in sorted(ROOT.rglob('*')):
        if path.is_symlink():
            raise RuntimeError('source package must not contain symlinks')
        if path.is_file():
            files[path.relative_to(ROOT).as_posix()] = digest(path)
        elif not path.is_dir():
            raise RuntimeError('source package contains a nonregular entry')
    return files


def verify():
    expected = {}
    for line in (ROOT / 'MANIFEST.sha256').read_text(encoding='utf-8').splitlines():
        try:
            checksum, name = line.split('  ', 1)
        except ValueError as exc:
            raise RuntimeError('malformed manifest line') from exc
        if (len(checksum) != 64 or any(c not in '0123456789abcdef' for c in checksum)
                or not name or name.startswith('/') or '\\' in name
                or any(part in ('', '.', '..') for part in name.split('/'))
                or name in expected or name == 'MANIFEST.sha256'):
            raise RuntimeError('malformed manifest entry')
        expected[name] = checksum
    if not expected:
        raise RuntimeError('empty manifest')
    actual = inventory()
    actual.pop('MANIFEST.sha256', None)
    if actual != expected:
        changed = sorted(set(actual) ^ set(expected) |
                         {name for name in actual.keys() & expected.keys()
                          if actual[name] != expected[name]})
        raise RuntimeError('manifest mismatch: ' + ', '.join(changed))
    expected_dirs = {str(parent).replace(os.sep, '/')
                     for name in expected for parent in Path(name).parents
                     if str(parent) != '.'}
    actual_dirs = {path.relative_to(ROOT).as_posix() for path in ROOT.rglob('*')
                   if path.is_dir()}
    if actual_dirs != expected_dirs:
        raise RuntimeError('unexpected or missing source directories')
    return expected


def new_output(value):
    out = Path(os.path.abspath(value))
    if any(p.is_symlink() for p in (out, *out.parents)):
        raise ValueError('output path must not have a live or dangling symlink ancestor')
    if out.exists():
        raise ValueError('output path must be new and must not already exist')
    if out == ROOT or ROOT in out.parents:
        raise ValueError('output must lie outside the source package')
    return out


def run(command, cwd, env, log):
    completed = subprocess.run(command, cwd=cwd, env=env, capture_output=True, check=False)
    content = completed.stdout + completed.stderr
    log.write_bytes(content)
    if completed.returncode:
        raise RuntimeError('command failed; inspect ' + str(log))
    return completed.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true', help='check all frozen files and stop')
    parser.add_argument('--output', help='new output directory outside the package')
    parser.add_argument('--numerical', action='store_true', help='require mpmath and reproduce deep diagnostics')
    args = parser.parse_args()
    if args.verify_only and (args.output or args.numerical):
        parser.error('--verify-only cannot be combined with build options')
    if not args.verify_only and not args.output:
        parser.error('a build needs --output')
    out = None
    if args.output:
        try:
            out = new_output(args.output)
        except ValueError as exc:
            parser.error(str(exc))
    sources = verify()
    if args.verify_only:
        print(json.dumps({'status': 'verified', 'files': len(sources)}, sort_keys=True))
        return
    before = inventory()
    out.mkdir(parents=True, exist_ok=False)
    logs = out / 'logs'
    logs.mkdir()
    env = os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1', SOURCE_DATE_EPOCH=EPOCH,
               FORCE_SOURCE_DATE='1', TZ='UTC')
    py = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    run(py + [str(ROOT / 'code/selftest.py')], ROOT, env, logs / 'exact_checks.txt')
    checks = {'exact_checks': 'passed', 'numerical_checks': 'not requested',
              'source_manifest_sha256': digest(ROOT / 'MANIFEST.sha256')}
    if args.numerical:
        run(py + [str(ROOT / 'code/selftest.py'), '--numerical'], ROOT, env,
            logs / 'numerical_selftest.txt')
        result = run(py + [str(ROOT / 'code/diagnostics.py'), 'suite', '--deep'], ROOT, env,
                     logs / 'diagnostics.txt')
        fixture = (ROOT / 'code/results/diagnostics.json').read_bytes()
        if result != fixture:
            raise RuntimeError('fresh numerical diagnostics differ from checked fixture')
        checks['numerical_checks'] = 'passed and byte-identical'
        checks['diagnostics_sha256'] = hashlib.sha256(result).hexdigest()
    # Private TeX format/cache; no global or source-tree writes.
    with tempfile.TemporaryDirectory(prefix='report230-') as tmp:
        work = Path(tmp)
        shutil.copyfile(ROOT / 'article.tex', work / 'article.tex')
        shutil.copytree(ROOT / 'sections', work / 'sections')
        if Path('/usr/share/texlive/texmf-dist').exists() and not env.get('TEXMF'):
            env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
        env['TEXMFVAR'] = str(work / 'texmf-var')
        env['TEXMFCONFIG'] = str(work / 'texmf-config')
        run(['pdftex', '-ini', '-etex', '-jobname=pdflatex', '-progname=pdflatex',
             '-interaction=nonstopmode', '-halt-on-error', 'pdflatex.ini'], work, env,
            logs / 'format.txt')
        for i in range(1, 4):
            run(['pdflatex', '-fmt=./pdflatex.fmt', '-no-shell-escape',
                 '-interaction=nonstopmode', '-halt-on-error', 'article.tex'], work, env,
                logs / ('latex' + str(i) + '.txt'))
        latex_log = (work / 'article.log').read_text(errors='replace')
        forbidden = ('Overfull \\hbox', 'Overfull \\vbox', 'Missing character:',
                     'There were undefined', 'undefined references',
                     'Rerun to get cross-references')
        if any(token in latex_log for token in forbidden):
            raise RuntimeError('TeX layout/reference warning requires review')
        pdf = (work / 'article.pdf').read_bytes()
    if pdf != (ROOT / 'Report230.pdf').read_bytes():
        (out / 'Report230-rebuilt-different.pdf').write_bytes(pdf)
        raise RuntimeError('rebuilt PDF differs from frozen PDF; inspect TeX toolchain and logs')
    (out / 'Report230.pdf').write_bytes(pdf)
    checks['pdf_sha256'] = hashlib.sha256(pdf).hexdigest()
    checks['pdf_matches_frozen'] = True
    if inventory() != before:
        raise RuntimeError('source package changed during build')
    members = sorted(before)
    archive_path = out / 'Report230.zip'
    with zipfile.ZipFile(archive_path, 'w', compression=zipfile.ZIP_STORED) as archive:
        for name in members:
            info = zipfile.ZipInfo('Report230/' + name, FIXED_TIME)
            info.create_system = 3
            info.compress_type = zipfile.ZIP_STORED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (ROOT / name).read_bytes())
    checks['zip_sha256'] = digest(archive_path)
    checks['zip_members'] = len(members)
    (out / 'build_checks.json').write_text(json.dumps(checks, indent=2, sort_keys=True) + '\n')
    print(json.dumps(checks, indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError) as exc:
        raise SystemExit(str(exc))
