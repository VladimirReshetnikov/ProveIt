#!/usr/bin/env python3
"""Check, compile and package Report 227 without modifying the source tree."""
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
GENERATED = {'Report227.pdf', 'build_checks.json'}
FIXED_TIME = (2026, 10, 5, 0, 0, 0)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files():
    paths = sorted(ROOT.rglob('*'))
    if any(path.is_symlink() for path in paths):
        raise RuntimeError('source package must not contain symlinks')
    return [path for path in paths if path.is_file()
            and path.relative_to(ROOT).as_posix() not in GENERATED]


def snapshot():
    return {path.relative_to(ROOT).as_posix(): digest(path)
            for path in source_files()}


def validate_source():
    expected = {}
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        checksum, name = line.split('  ', 1)
        if name in expected or len(checksum) != 64:
            raise RuntimeError('malformed source manifest')
        expected[name] = checksum
    actual = snapshot()
    actual.pop('MANIFEST.sha256', None)
    if actual != expected:
        raise RuntimeError('source manifest mismatch, including missing or extra files')


def new_output(value):
    path = Path(os.path.abspath(value))
    if any(part.is_symlink() for part in (path, *path.parents)):
        raise ValueError('output path must not have a symlink ancestor')
    if path.exists():
        raise ValueError('output directory must not already exist')
    if path == ROOT or ROOT in path.parents:
        raise ValueError('output must be outside the source package')
    return path


def run(command, cwd, env, stdout_path, stderr_path=None):
    with stdout_path.open('w') as stdout:
        if stderr_path is None:
            result = subprocess.run(command, cwd=cwd, env=env, stdout=stdout,
                                    stderr=subprocess.STDOUT, check=False)
        else:
            with stderr_path.open('w') as stderr:
                result = subprocess.run(command, cwd=cwd, env=env, stdout=stdout,
                                        stderr=stderr, check=False)
    if result.returncode:
        raise RuntimeError(f'command failed with code {result.returncode}; see {stdout_path}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, help='new directory outside the source tree')
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
    run(py + [str(ROOT / 'code/reproduce.py'), '--caps', '--numerics', '--order', '5'],
        out, env, logs / 'mathematical_checks.json', logs / 'mathematical_checks.stderr')
    checks = {'mathematical': json.loads((logs / 'mathematical_checks.json').read_text())}
    shutil.copyfile(ROOT / 'report227.tex', work / 'report227.tex')
    # A private format avoids writes to any user-global TeX cache. The unindexed
    # system tree also works with stripped-down TeX Live package databases.
    if Path('/usr/share/texlive/texmf-dist').exists() and not env.get('TEXMF'):
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
    env['TEXMFVAR'] = str(work / 'texmf-var')
    env['TEXMFCONFIG'] = str(work / 'texmf-config')
    run(['pdftex', '-ini', '-etex', '-jobname=pdflatex', '-progname=pdflatex',
         '-interaction=nonstopmode', '-halt-on-error', 'pdflatex.ini'],
        work, env, logs / 'format.log')
    for index in range(1, 4):
        run(['pdflatex', '-fmt=./pdflatex.fmt', '-no-shell-escape',
             '-interaction=nonstopmode', '-halt-on-error', 'report227.tex'],
            work, env, logs / f'latex{index}.log')
    tex_log = (work / 'report227.log').read_text(errors='replace')
    bad = ('Overfull \\hbox', 'Overfull \\vbox', 'undefined references',
           'There were undefined', 'Missing character:')
    if any(token in tex_log for token in bad):
        raise RuntimeError('TeX layout or reference warning requires inspection')
    pdf = out / 'Report227.pdf'
    shutil.copyfile(work / 'report227.pdf', pdf)
    checks['pdf_sha256'] = digest(pdf)
    checks['source_manifest_sha256'] = digest(ROOT / 'MANIFEST.sha256')
    receipt = (json.dumps(checks, sort_keys=True, indent=2) + '\n').encode()
    (out / 'build_checks.json').write_bytes(receipt)
    if snapshot() != before:
        raise RuntimeError('source tree changed during build')
    members = {path.relative_to(ROOT).as_posix(): path.read_bytes()
               for path in source_files()}
    members.update({'Report227.pdf': pdf.read_bytes(), 'build_checks.json': receipt})
    archive_path = out / 'Report227.zip'
    with zipfile.ZipFile(archive_path, 'w', compression=zipfile.ZIP_STORED) as archive:
        for name, content in sorted(members.items()):
            info = zipfile.ZipInfo('Report227/' + name, FIXED_TIME)
            info.compress_type = zipfile.ZIP_STORED
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            archive.writestr(info, content)
    print(json.dumps({'status': 'built', 'pdf_sha256': digest(pdf),
                      'zip_sha256': digest(archive_path), 'zip_members': len(members)},
                     sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
