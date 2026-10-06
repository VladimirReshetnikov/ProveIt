#!/usr/bin/env python3
"""Build Report173 offline in an isolated temporary tree without clobbering outputs."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
SOURCE_DATE_EPOCH = 1790985600
ZIP_TIME = (2026, 10, 3, 0, 0, 0)
SOURCE_FILES = (
    'Report173.tex', 'README.md', 'build.py', 'verify_package.py', 'test_build.py',
    'sources/REFERENCES.md',
    'companion/README.md', 'companion/coefficient_certificates.py',
    'companion/exact_counts.py', 'companion/rebuild.py', 'companion/residuals.py',
    'companion/run_checks.py', 'companion/symbolic_all_orders.py',
    'companion/verify_manifest.py', 'companion/fixtures/a137432_selected.json',
)

class BuildError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise BuildError(message)


def json_bytes(obj):
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=True) + '\n').encode()


def write_new(path, data):
    with Path(path).open('xb') as handle:
        handle.write(data)


def regular_files(root):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'input root must be a regular directory')
    paths = sorted(root.rglob('*'))
    require(all(not p.is_symlink() for p in paths), 'input contains a symlink')
    require(all(p.is_file() or p.is_dir() for p in paths), 'input contains a nonregular entry')
    return [p for p in paths if p.is_file()]


def validate_sources():
    require(len(set(SOURCE_FILES)) == len(SOURCE_FILES), 'duplicate source path')
    for name in SOURCE_FILES:
        p = Path(name)
        require(name and '\x00' not in name and '\\' not in name and not p.is_absolute()
                and '..' not in p.parts and p.as_posix() == name, 'unsafe source path')
        require((ROOT / p).is_file(), 'missing source: ' + name)
        require(all(not (ROOT / Path(*p.parts[:j])).is_symlink()
                    for j in range(1, len(p.parts) + 1)), 'symlink in source: ' + name)


def manifest(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in regular_files(root) if p.relative_to(root).as_posix() != 'SHA256SUMS.json'}


def make_zip(root, target):
    files = regular_files(root)
    with zipfile.ZipFile(target, 'x', compression=zipfile.ZIP_STORED) as archive:
        for p in files:
            zi = zipfile.ZipInfo(p.relative_to(root).as_posix(), ZIP_TIME)
            zi.create_system = 3
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_STORED
            archive.writestr(zi, p.read_bytes())


def run(command, cwd, env, timeout=300):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=timeout)
    require(result.returncode == 0, 'Command failed: ' + ' '.join(map(str, command))
            + '\n' + (result.stdout + result.stderr)[-12000:])
    return result.stdout


def prepare_tex(texwork, env):
    """Recover an absent format using installed files, without a global cache write."""
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], env=env,
                           capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return
    require(shutil.which('pdftex') is not None, 'pdftex is needed to initialize the local format')
    dist = Path(run(['kpsewhich', '-var-value=TEXMFDIST'], texwork, env).strip())
    require(dist.is_dir(), 'installed TeX distribution not found')
    trees = [dist]
    sibling = dist.parent.parent / 'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{' + ','.join(map(str, trees)) + '}'
    env['TEXFORMATS'] = str(texwork) + os.pathsep
    run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
         '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], texwork, env)
    require((texwork / 'pdflatex.fmt').is_file(), 'local format was not produced')
    maps = []
    for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
        path = Path(run(['kpsewhich', name], texwork, env).strip())
        require(path.is_file(), 'installed font map not found: ' + name)
        maps.append(path.read_bytes())
    write_new(texwork / 'pdftex.map', b'\n'.join(maps) + b'\n')


def compile_pdf(texwork, env):
    cmd = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
           '-file-line-error', '-jobname=Report173',
           r'\pdfsuppressptexinfo=15\relax\input{Report173.tex}']
    prior = None
    for iteration in range(1, 7):
        run(cmd, texwork, env)
        state = tuple((texwork / ('Report173.' + suffix)).read_bytes()
                      if (texwork / ('Report173.' + suffix)).exists() else b''
                      for suffix in ('aux', 'toc', 'out'))
        if iteration >= 2 and state == prior:
            break
        prior = state
    else:
        raise BuildError('TeX auxiliary files did not stabilize in six passes')
    log = (texwork / 'Report173.log').read_text(errors='replace')
    require(not any(x in log for x in ('There were undefined references',
            'There were undefined citations', 'Rerun to get cross-references right')),
            'TeX references remain unresolved')
    defects = re.findall(r'(?:Overfull[^\n]*|Missing character:[^\n]*)', log, re.I)
    require(not defects, 'TeX layout or glyph defect: ' + '; '.join(defects))
    data = (texwork / 'Report173.pdf').read_bytes()
    require(data.startswith(b'%PDF-'), 'invalid PDF output')
    return data


def build(output, pdf_output=None):
    targets = [Path(output).absolute()]
    if pdf_output is not None:
        targets.append(Path(pdf_output).absolute())
    require(len({str(p.resolve()) for p in targets}) == len(targets), 'output paths must differ')
    for p in targets:
        require(not p.exists() and not p.is_symlink(), 'refusing existing output: ' + str(p))
        require(p.parent.is_dir(), 'output parent must exist: ' + str(p.parent))
    require(shutil.which('pdflatex') is not None, 'pdflatex is required')
    require(shutil.which('kpsewhich') is not None, 'kpsewhich is required')
    validate_sources()
    require(datetime.datetime.fromtimestamp(SOURCE_DATE_EPOCH, datetime.timezone.utc).timetuple()[:6]
            == ZIP_TIME, 'inconsistent deterministic timestamps')
    env = dict(os.environ, SOURCE_DATE_EPOCH=str(SOURCE_DATE_EPOCH), FORCE_SOURCE_DATE='1',
               TZ='UTC', LC_ALL='C.UTF-8', PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    with tempfile.TemporaryDirectory(prefix='report173-') as temp:
        work = Path(temp)
        env.update(TEXMFVAR=str(work / 'var'), TEXMFCONFIG=str(work / 'config'),
                   TEXMFCACHE=str(work / 'cache'))
        package, texwork = work / 'package', work / 'tex'
        package.mkdir(); texwork.mkdir()
        for name in SOURCE_FILES:
            p = package / name
            p.parent.mkdir(parents=True, exist_ok=True)
            write_new(p, (ROOT / name).read_bytes())
        gen = package / 'generated'; gen.mkdir()
        results = []
        for optimize, name in ((False, 'checks.json'), (True, 'checks_optimized.json')):
            cmd = [sys.executable, '-I', '-B'] + (['-O'] if optimize else [])
            # Isolated mode omits the source directory. Add just this controlled copied directory.
            runner = 'import runpy,sys; sys.path.insert(0,sys.argv[1]); sys.argv=["run_checks.py"]; runpy.run_path(sys.path[0]+"/run_checks.py",run_name="__main__")'
            text = run(cmd + ['-c', runner, str(package / 'companion')], work, env)
            result = json.loads(text)
            results.append(result)
            write_new(gen / name, json_bytes(result))
        require(results[0] == results[1], 'normal and optimized checks differ')
        residual_runner = 'import runpy,sys; sys.path.insert(0,sys.argv[1]); sys.argv=["residuals.py","--precision","80"]; runpy.run_path(sys.path[0]+"/residuals.py",run_name="__main__")'
        residual = json.loads(run([sys.executable, '-I', '-B', '-c', residual_runner,
                                  str(package / 'companion')], work, env))
        write_new(gen / 'residuals.json', json_bytes(residual))
        for optimize, name in ((False, 'build_checks.json'), (True, 'build_checks_optimized.json')):
            cmd = [sys.executable, '-I', '-B'] + (['-O'] if optimize else [])
            test_runner = 'import runpy,sys; sys.path.insert(0,sys.argv[1]); sys.argv=["test_build.py"]; runpy.run_path(sys.path[0]+"/test_build.py",run_name="__main__")'
            receipt = json.loads(run(cmd + ['-c', test_runner, str(package)], work, env))
            write_new(gen / name, json_bytes(receipt))
        prepare_tex(texwork, env)
        write_new(texwork / 'Report173.tex', (package / 'Report173.tex').read_bytes())
        pdf_data = compile_pdf(texwork, env)
        write_new(package / 'Report173.pdf', pdf_data)
        write_new(gen / 'BUILD_INFO.json', json_bytes({
            'report': 'Report173', 'normal_optimized_agree': True,
            'network_required': False, 'shell_escape': False,
            'source_date_epoch': SOURCE_DATE_EPOCH,
            'default_transfer_max': 7, 'default_board_max': 5,
            'coefficient_certificates': [0, 1, 2, 3],
            'residual_precision': 80,
            'reproducibility': 'Identical bytes with the same source and installed Python/TeX stack; no cross-version PDF byte identity is promised.'}))
        write_new(package / 'SHA256SUMS.json', json_bytes(manifest(package)))
        make_zip(package, targets[0])
        if len(targets) == 2:
            write_new(targets[1], pdf_data)
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in targets}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True, help='new ZIP destination; parent must exist')
    p.add_argument('--pdf', help='optional new standalone PDF destination')
    args = p.parse_args()
    try:
        result = build(args.output, args.pdf)
    except (BuildError, OSError, ValueError, subprocess.TimeoutExpired) as exc:
        p.exit(1, 'FAIL: ' + str(exc) + '\n')
    print(json.dumps({'status': 'PASS', 'sha256': result}, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
