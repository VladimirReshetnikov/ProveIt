#!/usr/bin/env python3
"""Verify, compile and package Report 229 without changing its source tree."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
GENERATED = {'Report229.pdf', 'build_checks.json'}
FIXED_TIME = (2026, 10, 5, 0, 0, 0)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files():
    paths = sorted(ROOT.rglob('*'))
    if any(p.is_symlink() for p in paths):
        raise RuntimeError('source package must not contain symlinks')
    return [p for p in paths if p.is_file()
            and '__pycache__' not in p.relative_to(ROOT).parts
            and p.relative_to(ROOT).as_posix() not in GENERATED]


def snapshot():
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in source_files()}


def validate_source():
    expected = {}
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        try:
            checksum, name = line.split('  ', 1)
        except ValueError as exc:
            raise RuntimeError('malformed source manifest line') from exc
        if (name in expected or len(checksum) != 64
                or any(c not in '0123456789abcdef' for c in checksum)
                or name.startswith('/') or '..' in Path(name).parts
                or name == 'MANIFEST.sha256'):
            raise RuntimeError('malformed source manifest entry')
        expected[name] = checksum
    if not expected:
        raise RuntimeError('source manifest must not be empty')
    actual = snapshot()
    actual.pop('MANIFEST.sha256', None)
    if actual != expected:
        changed = sorted(set(actual) ^ set(expected) |
                         {p for p in actual.keys() & expected.keys()
                          if actual[p] != expected[p]})
        raise RuntimeError('source manifest mismatch: ' + ', '.join(changed))


def new_output(value):
    path = Path(os.path.abspath(value))
    if any(p.is_symlink() for p in (path, *path.parents)):
        raise ValueError('output path must not have a symlink ancestor')
    if path.exists():
        raise ValueError('output directory must not already exist')
    if path == ROOT or ROOT in path.parents:
        raise ValueError('output must be outside the source package')
    return path


def run(command, cwd, env, stdout_path):
    with stdout_path.open('w') as stdout:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=stdout,
                                stderr=subprocess.STDOUT, check=False)
    if result.returncode:
        raise RuntimeError(f'command failed with code {result.returncode}; see {stdout_path}')


def check_output(name, py, out, env, logs):
    target = out / (name + '.json')
    run(py + [str(ROOT / 'code' / (name + '.py')), '--output', str(target)],
        out, env, logs / (name + '.log'))
    expected_names = {'reproduce': 'exact_checks.json',
                      'check_guards': 'guard_checks.json',
                      'numerics': 'numeric_checks.json',
                      'check_poles': 'pole_checks.json'}
    expected = ROOT / 'tests' / expected_names[name]
    if target.read_bytes() != expected.read_bytes():
        raise RuntimeError(f'{name}: fresh results differ from the included fixture')
    return {'status': 'pass', 'fixture_sha256': digest(expected),
            'result': json.loads(target.read_text())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, help='new directory outside source package')
    parser.add_argument('--optional', action='store_true',
                        help='also require and run the optional SymPy pole certificate')
    args = parser.parse_args()
    try:
        out = new_output(args.out)
    except ValueError as exc:
        parser.error(str(exc))
    validate_source()
    before = snapshot()
    out.mkdir(parents=True)
    logs = out / 'logs'
    logs.mkdir()
    work = out / 'tex_work'
    work.mkdir()
    env = os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1', SOURCE_DATE_EPOCH='1791158400',
               FORCE_SOURCE_DATE='1', TZ='UTC')
    py = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    checks = {'exact': check_output('reproduce', py, out, env, logs),
              'guards': check_output('check_guards', py, out, env, logs),
              'numerics': check_output('numerics', py, out, env, logs)}
    if args.optional:
        checks['symbolic'] = check_output('check_poles', py, out, env, logs)
    else:
        checks['symbolic'] = {'status': 'not run',
                              'reason': 'optional SymPy certificate requires --optional'}
    # A private format avoids writes to a global TeX cache. This unindexed system
    # tree also works with stripped-down TeX Live package databases.
    shutil.copyfile(ROOT / 'report229.tex', work / 'report229.tex')
    if Path('/usr/share/texlive/texmf-dist').exists() and not env.get('TEXMF'):
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
    env['TEXMFVAR'] = str(work / 'texmf-var')
    env['TEXMFCONFIG'] = str(work / 'texmf-config')
    run(['pdftex', '-ini', '-etex', '-jobname=pdflatex', '-progname=pdflatex',
         '-interaction=nonstopmode', '-halt-on-error', 'pdflatex.ini'],
        work, env, logs / 'format.log')
    for index in range(1, 4):
        run(['pdflatex', '-fmt=./pdflatex.fmt', '-no-shell-escape',
             '-interaction=nonstopmode', '-halt-on-error', 'report229.tex'],
            work, env, logs / f'latex{index}.log')
    tex_log = (work / 'report229.log').read_text(errors='replace')
    bad = ('Overfull \\hbox', 'Overfull \\vbox', 'undefined references',
           'There were undefined', 'Missing character:', 'Rerun to get cross-references')
    if any(token in tex_log for token in bad):
        raise RuntimeError('TeX layout or reference warning requires inspection')
    pdf = out / 'Report229.pdf'
    shutil.copyfile(work / 'report229.pdf', pdf)
    checks['pdf_sha256'] = digest(pdf)
    checks['source_manifest_sha256'] = digest(ROOT / 'MANIFEST.sha256')
    checks['baseline_public_pdf_sha256'] = digest(ROOT / 'public227' / 'Report227.pdf')
    receipt = (json.dumps(checks, sort_keys=True, indent=2) + '\n').encode()
    (out / 'build_checks.json').write_bytes(receipt)
    if snapshot() != before:
        raise RuntimeError('source tree changed during build')
    members = {p.relative_to(ROOT).as_posix(): p.read_bytes() for p in source_files()}
    members.update({'Report229.pdf': pdf.read_bytes(), 'build_checks.json': receipt})
    archive_path = out / 'Report229.zip'
    with zipfile.ZipFile(archive_path, 'w', compression=zipfile.ZIP_STORED) as archive:
        for name, content in sorted(members.items()):
            info = zipfile.ZipInfo('Report229/' + name, FIXED_TIME)
            info.compress_type = zipfile.ZIP_STORED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, content)
    print(json.dumps({'status': 'built', 'pdf_sha256': digest(pdf),
                      'zip_sha256': digest(archive_path), 'zip_members': len(members)},
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
