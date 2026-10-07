#!/usr/bin/env python3
"""Build Report190 offline in isolated storage; never replace an existing output."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).absolute().parent))
import verify_manifest as manifest_tools

ROOT = Path(__file__).absolute().parent
REPORT = 190
BASENAME = 'Report190'
EPOCH = 1791072000
ZIP_TIME = (2026, 10, 4, 0, 0, 0)
# Explicit inventory: no source-directory caches, unrelated files, or external
# executable source copies can leak into the distributable archive.
SOURCES = manifest_tools.SOURCES
GENERATED = manifest_tools.GENERATED


class BuildError(RuntimeError):
    pass


def need(condition, message):
    if not condition:
        raise BuildError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True,
                       allow_nan=False) + '\n').encode('utf-8')


def write_new(path, data):
    with Path(path).open('xb') as stream:
        stream.write(data)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_source(name, root=None):
    root = manifest_tools.check_directory(ROOT if root is None else root)
    rel = manifest_tools.safe_name(name)
    path = root / rel
    manifest_tools.check_directory(path.parent)
    need(stat.S_ISREG(path.lstat().st_mode), 'missing regular source: ' + name)
    return path


def inventory(root):
    return manifest_tools.inventory(root)


def run(command, cwd, env, timeout=300):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=timeout, shell=False)
    need(result.returncode == 0, 'command failed: ' + ' '.join(map(str, command))
         + '\n' + (result.stdout + result.stderr)[-12000:])
    return result.stdout


def environment(temp):
    """Fixed metadata, private TeX caches, no inherited TeX/Python overrides."""
    temp = Path(temp)
    for name in ('home', 'tmp', 'texvar', 'texconfig', 'texcache', 'texhome', 'fonts'):
        (temp / name).mkdir()
    env = {
        'PATH': os.environ.get('PATH', os.defpath),
        'HOME': str(temp / 'home'), 'TMPDIR': str(temp / 'tmp'),
        'SOURCE_DATE_EPOCH': str(EPOCH), 'FORCE_SOURCE_DATE': '1',
        'TZ': 'UTC', 'LC_ALL': 'C.UTF-8',
        'PYTHONHASHSEED': '0', 'PYTHONDONTWRITEBYTECODE': '1',
        'TEXMFVAR': str(temp / 'texvar'),
        'TEXMFCONFIG': str(temp / 'texconfig'),
        'TEXMFCACHE': str(temp / 'texcache'),
        'TEXMFHOME': str(temp / 'texhome'),
        'VARTEXFONTS': str(temp / 'fonts'),
        'openin_any': 'p', 'openout_any': 'p', 'shell_escape': 'f',
    }
    if os.name == 'nt' and 'SystemRoot' in os.environ:
        env['SystemRoot'] = os.environ['SystemRoot']
    return env


def prepare_tex(work, env):
    need(shutil.which('pdflatex', path=env['PATH']) and
         shutil.which('kpsewhich', path=env['PATH']),
         'pdflatex and kpsewhich are required')
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], cwd=work, env=env,
                           capture_output=True, text=True, timeout=30, shell=False)
    if probe.returncode == 0 and probe.stdout.strip():
        return
    need(shutil.which('pdftex', path=env['PATH']),
         'pdftex is needed to initialize a local format')
    dist = Path(run(['kpsewhich', '-var-value=TEXMFDIST'], work, env).strip())
    need(dist.is_dir(), 'installed TeX tree not found')
    trees = [dist]
    sibling = dist.parent.parent / 'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{' + ','.join(map(str, trees)) + '}'
    env['TEXFORMATS'] = str(work) + os.pathsep
    run(['pdftex', '-ini', '-etex', '-no-shell-escape',
         '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex',
         'pdflatex.ini'], work, env)
    need((work / 'pdflatex.fmt').is_file(), 'local format was not produced')
    maps = []
    for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
        path = Path(run(['kpsewhich', name], work, env).strip())
        need(path.is_file(), 'installed map not found: ' + name)
        maps.append(path.read_bytes())
    write_new(work / 'pdftex.map', b'\n'.join(maps) + b'\n')


def compile_pdf(work, env):
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', '-jobname=' + BASENAME,
               'Report190.tex']
    states = []
    for passno in range(3):
        run(command, work, env)
        states.append(tuple((work / (BASENAME + '.' + suffix)).read_bytes()
                      if (work / (BASENAME + '.' + suffix)).exists() else b''
                      for suffix in ('aux', 'toc', 'out')))
    need(states[1] == states[2], 'TeX auxiliary files did not stabilize in three passes')
    log = (work / (BASENAME + '.log')).read_text(errors='replace')
    need(not any(message in log for message in
                 ('There were undefined references', 'There were undefined citations',
                  'Rerun to get cross-references right', 'Label(s) may have changed',
                  'There were multiply-defined labels')),
         'unresolved or multiply-defined TeX references')
    defects = [line for line in log.splitlines()
               if re.search(r'\b(?:Overfull|Underfull|Warning)\b|Missing character:', line, re.I)
               and not (line.startswith('Package: infwarerr ')
                        and 'Providing info/warning/error messages (HO)' in line)]
    need(not defects, 'TeX layout defects: ' + '; '.join(defects))
    data = manifest_tools.read_regular(work / (BASENAME + '.pdf'))
    need(data.startswith(b'%PDF-'), 'invalid PDF')
    return data


def run_python(package, script, args, env, optimized=False):
    flags = ['-I', '-S', '-B'] + (['-O'] if optimized else [])
    bootstrap = ('import runpy,sys; root=sys.argv.pop(1); script=sys.argv.pop(1); '
                 'sys.path.insert(0,root); sys.argv[0]=root+"/"+script; '
                 'runpy.run_path(sys.argv[0],run_name="__main__")')
    result = manifest_tools.load_json(run(
        [sys.executable, *flags, '-c', bootstrap, str(package), script, *args],
        package, env, 900))
    need(isinstance(result, dict) and result.get('status') == 'PASS',
         script + ' did not return a PASS object')
    return result


def archive(package, target, expected=None):
    # This read-only check also rejects any unexpected cache or empty directory.
    target = checked_output(target, package)
    manifest_tools.verify(package, expected=expected)
    files, _ = manifest_tools.scan(package)
    with zipfile.ZipFile(target, 'x', compression=zipfile.ZIP_STORED) as zipped:
        for name, path in sorted(files.items()):
            info = zipfile.ZipInfo(name, ZIP_TIME)
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = zipfile.ZIP_STORED
            zipped.writestr(info, manifest_tools.read_regular(path))


def validate_source(root):
    """Accept exactly a source tree or an intact extracted release tree."""
    files, directories = manifest_tools.scan(root)
    if manifest_tools.MANIFEST in files:
        manifest_tools.verify(root, expected=SOURCES + GENERATED)
        expected = set(SOURCES) | set(GENERATED) | {manifest_tools.MANIFEST}
    else:
        expected = set(SOURCES)
    need(set(files) == expected, 'source inventory mismatch; missing=' +
         repr(sorted(expected - set(files))) + '; extra=' +
         repr(sorted(set(files) - expected)))
    expected_dirs = {parent.as_posix() for name in expected
                     for parent in Path(name).parents if parent.as_posix() != '.'}
    need(directories == expected_dirs, 'source contains empty or unexpected directory')
    manifest_tools.inventory(root)  # Enforce the aggregate as well as per-file size cap.


def checked_output(output, source):
    output = Path(output).absolute()
    need('..' not in output.parts, 'unsafe output path')
    need(not os.path.lexists(output), 'refusing existing output: ' + str(output))
    manifest_tools.check_directory(output.parent)
    root = manifest_tools.check_directory(source).resolve()
    need(not output.resolve().is_relative_to(root), 'output must be outside source package')
    return output


def snapshot(root):
    files, directories = manifest_tools.scan(root)
    return ({name: {'bytes': len(data), 'sha256': sha(data)}
             for name, path in sorted(files.items())
             for data in (manifest_tools.read_regular(path),)}, directories)


def build(output):
    output = checked_output(output, ROOT)
    need(len(SOURCES) == len(set(SOURCES)), 'duplicate source path')
    validate_source(ROOT)
    before = snapshot(ROOT)
    sources = {name: manifest_tools.read_regular(safe_source(name)) for name in SOURCES}
    with tempfile.TemporaryDirectory(prefix='report190-build-', dir=output.parent) as tmp:
        temp = Path(tmp)
        package, tex = temp / 'package', temp / 'tex'
        package.mkdir()
        tex.mkdir()
        env = environment(temp)
        for name, data in sources.items():
            destination = package / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            write_new(destination, data)
        generated = package / 'generated'
        results = [run_python(package, 'test_build.py', [], env, optimized)
                   for optimized in (False, True)]
        need(canonical(results[0]) == canonical(results[1]),
             'ordinary and optimized build guards differ')
        verification = run_python(package, 'reproduce.py',
                                  ['--output-dir', str(temp / 'replay')], env)
        generated.mkdir()
        write_new(generated / 'build_guards.json', canonical(results[0]))
        write_new(generated / 'verification.json', canonical(verification))
        exact = manifest_tools.read_regular(temp / 'replay' / 'normal' / 'exact_checks.json')
        write_new(generated / 'exact_checks.json', exact)
        prepare_tex(tex, env)
        write_new(tex / 'Report190.tex', sources['Report190.tex'])
        pdf = compile_pdf(tex, env)
        write_new(package / (BASENAME + '.pdf'), pdf)
        write_new(generated / 'BUILD_INFO.json', canonical({
            'report': REPORT, 'date': '2026-10-04',
            'sequences': ['A094925', 'A094926', 'A258639'],
            'mandatory_arithmetic': 'integer and Fraction only',
            'mandatory_python_dependencies': 'standard library only',
            'floating_diagnostics_run_during_build': False,
            'normal_and_optimized_agree': True, 'network_required': False,
            'shell_escape': False, 'tex_passes': 3, 'source_date_epoch': EPOCH,
            'reproducibility': 'Byte-identical with the same source and installed '
                               'Python/TeX stack; no cross-version PDF identity is promised.',
        }))
        write_new(package / manifest_tools.MANIFEST,
                  canonical(manifest_tools.document(package)))
        receipt = run_python(package, 'verify_manifest.py', [], env)
        need(receipt.get('status') == 'PASS', 'manifest verification failed')
        zipped = temp / (BASENAME + '_code.zip')
        archive(package, zipped, expected=SOURCES + GENERATED)
        need(snapshot(ROOT) == before, 'source changed during build')
        # Exclusive mkdir is the publication boundary. A concurrently created
        # file, directory, or dangling symlink is never removed or replaced.
        output.mkdir(exist_ok=False)
        for name, data in ((BASENAME + '.pdf', pdf),
                           (BASENAME + '.tex', sources['Report190.tex']),
                           (BASENAME + '_code.zip', zipped.read_bytes())):
            write_new(output / name, data)
        result = {path.name: {'bytes': path.stat().st_size,
                             'sha256': sha(manifest_tools.read_regular(
                                 path, manifest_tools.MAX_TOTAL_BYTES + 65536))}
                  for path in sorted(output.iterdir())}
        write_new(output / 'ARTIFACTS.json', canonical({
            'schema': 'report190-artifacts-v1', 'report': REPORT,
            'algorithm': 'sha256', 'files': result}))
    return {'status': 'PASS', 'artifacts': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path,
                        help='new output directory; parent must already exist')
    args = parser.parse_args()
    try:
        print(json.dumps(build(args.output), sort_keys=True, indent=2))
    except (BuildError, ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True),
              file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
