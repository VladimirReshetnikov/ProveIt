#!/usr/bin/env python3
"""Verify, reproduce, compile, and package Report 228 without changing sources."""
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
FIXED_TIME = (2026, 10, 5, 0, 0, 0)
GENERATED = {'Report228.pdf', 'build_checks.json'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files():
    for p in ROOT.rglob('*'):
        if p.is_symlink():
            raise ValueError('source package must contain no symlinks')
    return sorted(p for p in ROOT.rglob('*') if p.is_file()
                  and p.relative_to(ROOT).as_posix() not in GENERATED)


def snapshot():
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in source_files()}


def validate_source():
    expected = {}
    for line in (ROOT/'MANIFEST.sha256').read_text().splitlines():
        checksum, name = line.split('  ', 1)
        if name in expected:
            raise ValueError('duplicate manifest entry')
        expected[name] = checksum
    actual = snapshot()
    actual.pop('MANIFEST.sha256', None)
    if expected != actual:
        raise ValueError('source manifest mismatch, including extra or missing files')


def output_path(value):
    out = Path(os.path.abspath(Path(value).expanduser()))
    if any(p.is_symlink() for p in [out, *out.parents]):
        raise ValueError('output must have no symlink ancestor')
    if out.exists():
        raise ValueError('output directory must not exist')
    if out == ROOT or ROOT in out.parents or out in ROOT.parents:
        raise ValueError('output must not overlap the source package')
    return out


def run(command, cwd, env, log):
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=cwd, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError('command failed; inspect '+str(log))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, help='new directory outside this package')
    args = parser.parse_args()
    try:
        out = output_path(args.out)
        validate_source()
    except ValueError as exc:
        parser.error(str(exc))
    before = snapshot()
    out.mkdir(parents=True)
    logs = out/'logs'; logs.mkdir()
    work = out/'tex_work'; work.mkdir()
    results = out/'reproduction'
    env = os.environ.copy()
    env.update({'PYTHONDONTWRITEBYTECODE':'1', 'SOURCE_DATE_EPOCH':'1791158400',
                'FORCE_SOURCE_DATE':'1', 'TZ':'UTC'})
    py = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
    run(py+[str(ROOT/'code/reproduce.py'), '--check', '--output-dir', str(results)],
        out, env, logs/'reproduction.log')
    for name in ('reproduction.json', 'crossover_table.tex'):
        if (results/name).read_bytes() != (ROOT/'results'/name).read_bytes():
            raise RuntimeError('scientific output differs from distributed '+name)
    checks = json.loads((results/'checks.json').read_text())
    if checks.get('status') != 'passed' or checks.get('explicit_checks', 0) < 136:
        raise RuntimeError('required explicit checks did not run')
    # Runtime mode is present in the separate run log, but is not scientific
    # output identity. Both modes execute the same exceptions-based tests.
    checks.pop('python_optimization', None)
    checks.pop('integer_string_limit', None)
    for path in (ROOT/'src').iterdir():
        shutil.copyfile(path, work/path.name)
    shutil.copyfile(results/'crossover_table.tex', work/'crossover_table.tex')
    if Path('/usr/share/texlive/texmf-dist').exists() and not env.get('TEXMF'):
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
    env['TEXMFVAR'] = str(work/'texmf-var')
    env['TEXMFCONFIG'] = str(work/'texmf-config')
    run(['pdftex', '-ini', '-etex', '-jobname=pdflatex', '-progname=pdflatex',
         '-interaction=nonstopmode', '-halt-on-error', 'pdflatex.ini'],
        work, env, logs/'format.log')
    for number in range(1, 4):
        run(['pdflatex', '-fmt=./pdflatex.fmt', '-no-shell-escape',
             '-interaction=nonstopmode', '-halt-on-error', 'report228.tex'],
            work, env, logs/('latex'+str(number)+'.log'))
    log = (work/'report228.log').read_text(errors='replace')
    bad = ('Overfull \\hbox', 'Overfull \\vbox', 'undefined references',
           'There were undefined', 'Missing character:')
    if any(item in log for item in bad):
        raise RuntimeError('TeX layout or reference warning requires inspection')
    pdf = out/'Report228.pdf'
    shutil.copyfile(work/'report228.pdf', pdf)
    receipt = {
        'status':'passed', 'finite_checks':checks,
        'pdf_sha256':digest(pdf),
        'source_manifest_sha256':digest(ROOT/'MANIFEST.sha256'),
        'scientific_results_sha256':digest(results/'reproduction.json'),
        'table_sha256':digest(results/'crossover_table.tex'),
        'source_preserving':True,
        'scope':'finite exact checks and deterministic build, not analytic or numerical certification',
    }
    encoded = (json.dumps(receipt, sort_keys=True, indent=2)+'\n').encode()
    (out/'build_checks.json').write_bytes(encoded)
    if snapshot() != before:
        raise RuntimeError('source package changed during build')
    members = {p.relative_to(ROOT).as_posix():p.read_bytes() for p in source_files()}
    members.update({'Report228.pdf':pdf.read_bytes(), 'build_checks.json':encoded})
    with zipfile.ZipFile(out/'Report228.zip', 'w', compression=zipfile.ZIP_STORED) as archive:
        for name, data in sorted(members.items()):
            info = zipfile.ZipInfo('Report228/'+name, FIXED_TIME)
            info.create_system = 3
            info.compress_type = zipfile.ZIP_STORED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    print(json.dumps({'status':'built', 'pdf_sha256':digest(pdf),
                      'zip_sha256':digest(out/'Report228.zip'),
                      'zip_members':len(members)}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
