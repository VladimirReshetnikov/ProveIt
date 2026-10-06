#!/usr/bin/env python3
"""Build Report194 offline in isolated storage; never replace an existing output."""
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
REPORT = 194
BASENAME = 'Report194'
EPOCH = 1791072000
ZIP_TIME = (2026, 10, 4, 0, 0, 0)
# Explicit inventory: no source-directory caches, unrelated files, or external
# executable source copies can leak into the distributable archive.
SOURCES = manifest_tools.SOURCES
GENERATED = manifest_tools.GENERATED
CODE_PROVENANCE_SHA256 = '9647d12f1918cdb273338feb8a3297fc90000c46c216f13edf41f023ca90609a'
CODE_FILES = ('code/check_exact.py', 'code/matrix_exact.py', 'code/derive_second_correction.py', 'code/verify_second_correction.py', 'data/reference.json')


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
               'Report194.tex']
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


def collect_replay(replay, result):
    files, directories = manifest_tools.scan(replay)
    need(set(files) == {'RESULT.json','normal/exact_checks.json','optimized/exact_checks.json'},
         'unexpected exact replay file inventory')
    need(directories == {'normal','optimized'}, 'unexpected exact replay directory inventory')
    required = {'status','standard_library_only','normal_and_optimized_byte_identical',
                'exact_checks_sha256','exact_checks_bytes','floating_diagnostics_run','scope'}
    need(type(result) is dict and set(result) == required, 'replay result schema mismatch')
    need(result['status'] == 'PASS' and result['standard_library_only'] is True
         and result['normal_and_optimized_byte_identical'] is True
         and result['floating_diagnostics_run'] is False, 'replay declaration mismatch')
    need(result['scope'] == 'Exact finite checks; general theorems are proved in Report194',
         'replay scope mismatch')
    need(manifest_tools.read_regular(replay/'RESULT.json') == canonical(result),
         'replay stdout and result differ')
    normal = manifest_tools.read_regular(replay/'normal/exact_checks.json')
    optimized = manifest_tools.read_regular(replay/'optimized/exact_checks.json')
    need(normal == optimized, 'replay mode bytes differ')
    need(canonical(manifest_tools.load_json(normal)) == normal, 'replay JSON is not canonical')
    need(type(result['exact_checks_bytes']) is int and result['exact_checks_bytes'] == len(normal)
         and result['exact_checks_sha256'] == sha(normal), 'replay checksum or length mismatch')
    return normal


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
    if 'code/PROVENANCE.json' in SOURCES:
        validate_provenance(root)


def validate_provenance(root):
    raw=manifest_tools.read_regular(root/'code/PROVENANCE.json')
    need(sha(raw) == CODE_PROVENANCE_SHA256, 'exact-code provenance checksum mismatch')
    data=manifest_tools.load_json(raw)
    need(type(data) is dict and set(data) == {'schema','report','algorithm','scope','files'},
         'exact-code provenance schema mismatch')
    need(data['schema'] == 'report194-exact-code-v1' and type(data['report']) is int
         and data['report'] == REPORT and data['algorithm'] == 'sha256',
         'exact-code provenance identity mismatch')
    need(type(data['files']) is dict and set(data['files']) == set(CODE_FILES),
         'exact-code provenance inventory mismatch')
    for name in CODE_FILES:
        payload=manifest_tools.read_regular(root/name)
        need(data['files'][name] == {'bytes':len(payload),'sha256':sha(payload)},
             'exact-code source changed: '+name)


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
    with tempfile.TemporaryDirectory(prefix='report194-build-', dir=output.parent) as tmp:
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
        exact = collect_replay(temp / 'replay', verification)
        write_new(generated / 'exact_checks.json', exact)
        prepare_tex(tex, env)
        write_new(tex / 'Report194.tex', sources['Report194.tex'])
        pdf = compile_pdf(tex, env)
        write_new(package / (BASENAME + '.pdf'), pdf)
        write_new(generated / 'BUILD_INFO.json', canonical({
            'report': REPORT, 'date': '2026-10-04',
            'sequences': ['A222959', 'A222955'],
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
                           (BASENAME + '.tex', sources['Report194.tex']),
                           (BASENAME + '_code.zip', zipped.read_bytes())):
            write_new(output / name, data)
        result = {path.name: {'bytes': path.stat().st_size,
                             'sha256': sha(manifest_tools.read_regular(
                                 path, manifest_tools.MAX_TOTAL_BYTES + 65536))}
                  for path in sorted(output.iterdir())}
        write_new(output / 'ARTIFACTS.json', canonical({
            'schema': 'report194-artifacts-v1', 'report': REPORT,
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
