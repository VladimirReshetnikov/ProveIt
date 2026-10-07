#!/usr/bin/env python3
"""Build Report180 offline in isolated storage; never replace an existing output."""
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
REPORT = 180
BASENAME = 'Report180'
EPOCH = 1790985600
ZIP_TIME = (2026, 10, 3, 0, 0, 0)
# Explicit inventory: no source-directory caches, unrelated files, or external
# executable source copies can leak into the distributable archive.
SOURCES = ('Report180.tex', 'README.md', 'README_CODE.md', 'SOURCE_AUDIT.md', 'build.py', 'test_build.py', 'verify_manifest.py', 'guard_tests.py', 'code/exact.py', 'code/verify.py', 'code/regenerate.py', 'data/certificates.json', 'data/PROVENANCE.json', 'optional/README.md', 'optional/requirements.txt', 'data/references/checks.json', 'data/references/entringer_connection_certificate.json', 'data/references/entringer_diagnostics.json', 'data/references/exact_checks.json', 'data/references/finite_nonreal_counterexample.json', 'data/references/marked_coefficients.json', 'optional/audit/check_exact.py', 'optional/producer/certify_entringer.py', 'optional/producer/check_marked_coefficients.py', 'optional/producer/verify_entringer.py', 'optional/root/check.py', 'optional/check_length.py', 'data/references/length_diagnostics.json')
GENERATED = ('Report180.pdf', 'generated/verification.json', 'generated/verification_guards.json', 'generated/build_guards.json', 'generated/BUILD_INFO.json')


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
               'Report180.tex']
    old = None
    for passno in range(6):
        run(command, work, env)
        state = tuple((work / (BASENAME + '.' + suffix)).read_bytes()
                      if (work / (BASENAME + '.' + suffix)).exists() else b''
                      for suffix in ('aux', 'toc', 'out'))
        if passno and state == old:
            break
        old = state
    else:
        raise BuildError('TeX auxiliary files did not stabilize')
    log = (work / (BASENAME + '.log')).read_text(errors='replace')
    need(not any(message in log for message in
                 ('There were undefined references', 'There were undefined citations',
                  'Rerun to get cross-references right', 'Label(s) may have changed',
                  'There were multiply-defined labels')),
         'unresolved or multiply-defined TeX references')
    defects = re.findall(r'(?:Overfull[^\n]*|Missing character:[^\n]*)', log, re.I)
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


def archive(package, target):
    # This read-only check also rejects any unexpected cache or empty directory.
    manifest_tools.verify(package)
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
        manifest_tools.verify(root)
        expected = set(SOURCES) | set(GENERATED) | {manifest_tools.MANIFEST}
    else:
        expected = set(SOURCES)
    need(set(files) == expected, 'source inventory mismatch; missing=' +
         repr(sorted(expected - set(files))) + '; extra=' +
         repr(sorted(set(files) - expected)))
    expected_dirs = {parent.as_posix() for name in expected
                     for parent in Path(name).parents if parent.as_posix() != '.'}
    need(directories == expected_dirs, 'source contains empty or unexpected directory')


def build(output, extended=False):
    # --extended is a harmless compatibility option. The ordinary verifier
    # already runs every configured exact check.
    output = Path(output).absolute()
    need('..' not in output.parts, 'unsafe output path')
    need(not os.path.lexists(output), 'refusing existing output directory: ' + str(output))
    manifest_tools.check_directory(output.parent)
    need(not output.resolve().is_relative_to(manifest_tools.check_directory(ROOT).resolve()),
         'output must be outside the source package')
    need(len(SOURCES) == len(set(SOURCES)), 'duplicate source path')
    validate_source(ROOT)
    sources = {name: manifest_tools.read_regular(safe_source(name)) for name in SOURCES}
    with tempfile.TemporaryDirectory(prefix='report180-build-', dir=output.parent) as tmp:
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
        generated.mkdir()
        for script, filename, label in (
                ('code/verify.py', 'verification.json', 'mathematical results'),
                ('guard_tests.py', 'verification_guards.json', 'corruption guards'),
                ('test_build.py', 'build_guards.json', 'build guards')):
            results = [run_python(package, script, [], env, optimized)
                       for optimized in (False, True)]
            need(canonical(results[0]) == canonical(results[1]),
                 'ordinary and optimized ' + label + ' differ')
            write_new(generated / filename, canonical(results[0]))
        prepare_tex(tex, env)
        write_new(tex / 'Report180.tex', sources['Report180.tex'])
        pdf = compile_pdf(tex, env)
        write_new(package / (BASENAME + '.pdf'), pdf)
        write_new(generated / 'BUILD_INFO.json', canonical({
            'report': REPORT, 'date': '2026-10-03', 'maximum_order_checked': 6,
            'normal_and_optimized_agree': True, 'network_required': False,
            'shell_escape': False, 'source_date_epoch': EPOCH,
            'reproducibility': 'Byte-identical with the same source and installed '
                               'Python/TeX stack; no cross-version PDF identity is promised.',
        }))
        write_new(package / 'SHA256SUMS.json', canonical(inventory(package)))
        receipt = run_python(package, 'verify_manifest.py', [], env)
        need(receipt.get('status') == 'PASS', 'manifest verification failed')
        zipped = temp / (BASENAME + '.zip')
        archive(package, zipped)
        # Exclusive mkdir is the publication boundary. A concurrently created
        # file, directory, or dangling symlink is never removed or replaced.
        output.mkdir(exist_ok=False)
        for name, data in ((BASENAME + '.pdf', pdf),
                           (BASENAME + '.tex', sources['Report180.tex']),
                           (BASENAME + '.zip', zipped.read_bytes())):
            write_new(output / name, data)
        result = {path.name: {'bytes': path.stat().st_size,
                             'sha256': sha(manifest_tools.read_regular(path))}
                  for path in sorted(output.iterdir())}
        write_new(output / 'ARTIFACTS.json', canonical(result))
    return {'status': 'PASS', 'artifacts': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path,
                        help='new output directory; parent must already exist')
    parser.add_argument('--extended', action='store_true',
                        help='compatibility alias; all exact checks always run')
    args = parser.parse_args()
    try:
        print(json.dumps(build(args.output, args.extended), sort_keys=True, indent=2))
    except (BuildError, ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True),
              file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
