#!/usr/bin/env python3
"""Rebuild Report223 offline in a new directory; no existing file is overwritten.

Requires Python 3.11+, SymPy, mpmath, pdfTeX/LaTeX and the installed packages used
by Report223.tex. Use --verify-only to verify an extracted full package without
running optional libraries or TeX. A full build reproduces all package members,
including diagnostics, and creates a deterministic uncompressed ZIP.
"""
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

ROOT = Path(__file__).resolve().parent
SOURCES = (
    'Report223.tex', 'README.md', 'SOURCES.json', 'requirements-optional.txt',
    'build.py', 'code/lengyel_exact.py', 'code/test_lengyel_exact.py',
    'code/symbolic.py', 'code/diagnostics.py',
)
GENERATED = (
    'Report223.pdf', 'generated/exact_checks.txt', 'generated/symbolic.txt',
    'generated/diagnostics.txt', 'generated/toolchain.json',
)
MANIFEST = 'SHA256SUMS'
ZIPNAME = 'Report223.zip'
STAMP = (1980, 1, 1, 0, 0, 0)
EPOCH = '315532800'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def inventory(root):
    need(root.is_dir() and not root.is_symlink(), 'package root must be a real directory')
    files = {}
    directories = set()
    for path in sorted(root.rglob('*')):
        need(not path.is_symlink(), 'symlinks are not permitted in the package')
        if path.is_file():
            need(stat.S_ISREG(path.stat().st_mode), 'nonregular package member')
            files[path.relative_to(root).as_posix()] = path.read_bytes()
        else:
            need(path.is_dir(), 'special package member')
            directories.add(path.relative_to(root).as_posix())
    implied = {p.as_posix() for name in files for p in Path(name).parents if p.as_posix() != '.'}
    need(directories == implied, 'empty or unexpected package directory')
    return files


def manifest_bytes(files):
    return ''.join(digest(data)+'  '+name+'\n'
                   for name, data in sorted(files.items()) if name != MANIFEST).encode('ascii')


def verify(root):
    files = inventory(root)
    expected = set(SOURCES) | set(GENERATED) | {MANIFEST}
    need(set(files) == expected, 'package inventory does not match the declared complete inventory')
    need(files[MANIFEST] == manifest_bytes(files), 'package SHA256SUMS verification failed')
    print('PASS complete package inventory and SHA256SUMS')
    return files


def source_payload():
    files = inventory(ROOT)
    if MANIFEST in files:
        files = verify(ROOT)
    else:
        need(set(files) == set(SOURCES), 'source-only inventory contains missing or unexpected files')
    for name in SOURCES:
        files[name].decode('utf-8')
        need(not any(byte < 32 and byte not in (9, 10) for byte in files[name]),
             'control byte in source: '+name)
    return {name: files[name] for name in SOURCES}


def run(command, cwd, env, timeout=900):
    result = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                            text=True, timeout=timeout, shell=False)
    need(result.returncode == 0,
         'command failed: '+' '.join(map(str, command))+'\n'+
         (result.stdout+result.stderr)[-12000:])
    return result.stdout


def environment(temp):
    for subdir in ('home', 'tmp', 'texvar', 'texconfig', 'texcache', 'texhome', 'fonts'):
        (temp/subdir).mkdir()
    env = {
        'PATH': os.environ.get('PATH', os.defpath),
        'HOME': str(temp/'home'), 'TMPDIR': str(temp/'tmp'),
        'SOURCE_DATE_EPOCH': EPOCH, 'FORCE_SOURCE_DATE': '1',
        'TZ': 'UTC', 'LC_ALL': 'C.UTF-8',
        'PYTHONHASHSEED': '0', 'PYTHONDONTWRITEBYTECODE': '1',
        'TEXMFVAR': str(temp/'texvar'), 'TEXMFCONFIG': str(temp/'texconfig'),
        'TEXMFCACHE': str(temp/'texcache'), 'TEXMFHOME': str(temp/'texhome'),
        'VARTEXFONTS': str(temp/'fonts'),
        'openin_any': 'p', 'openout_any': 'p', 'shell_escape': 'f',
    }
    # Preserve the supported integer cap rather than overriding it.
    if 'PYTHONINTMAXSTRDIGITS' in os.environ:
        env['PYTHONINTMAXSTRDIGITS'] = os.environ['PYTHONINTMAXSTRDIGITS']
    if os.name == 'nt' and 'SystemRoot' in os.environ:
        env['SystemRoot'] = os.environ['SystemRoot']
    return env


def prepare_tex(work, env):
    for name in ('pdflatex', 'pdftex', 'kpsewhich'):
        need(shutil.which(name, path=env['PATH']), 'required executable missing: '+name)
    dist = Path(run(['kpsewhich', '-var-value=TEXMFDIST'], work, env).strip())
    need(dist.is_dir(), 'installed TeX distribution not found')
    trees = [dist]
    sibling = dist.parent.parent/'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{'+','.join(map(str, trees))+'}'
    env['TEXFORMATS'] = str(work)+os.pathsep
    run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
         '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], work, env)
    need((work/'pdflatex.fmt').is_file(), 'private TeX format not generated')
    maps = []
    for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
        path = Path(run(['kpsewhich', name], work, env).strip())
        need(path.is_file(), 'installed font map missing: '+name)
        maps.append(path.read_bytes())
    (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')


def compile_pdf(work, env):
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', 'Report223.tex']
    previous = None
    stable = False
    for _ in range(5):
        run(command, work, env)
        state = tuple((work/('Report223.'+suffix)).read_bytes()
                      if (work/('Report223.'+suffix)).exists() else b''
                      for suffix in ('aux', 'toc', 'out'))
        if state == previous:
            stable = True
            break
        previous = state
    need(stable, 'TeX cross references did not stabilize')
    log = (work/'Report223.log').read_text(errors='replace')
    defects = [line for line in log.splitlines()
               if re.search(r'Overfull|Missing character:|undefined references|undefined citations|'
                            r'multiply-defined|Rerun to get cross-references|Label\(s\) may have changed',
                            line, re.I)]
    need(not defects, 'TeX reference/layout defects: '+'; '.join(defects))
    pdf = (work/'Report223.pdf').read_bytes()
    need(pdf.startswith(b'%PDF-'), 'PDF output invalid')
    need(b'/CreationDate' not in pdf and b'/ModDate' not in pdf and b'/ID [' not in pdf,
         'PDF has variable date or identifier metadata')
    return pdf


def fresh_output(text):
    raw = Path(text).absolute()
    need(not raw.exists() and not raw.is_symlink(), 'output must not already exist')
    need(raw.parent.is_dir(), 'output parent must already exist')
    for ancestor in (raw.parent, *raw.parent.parents):
        need(not ancestor.is_symlink(), 'output ancestors must not be symlinks')
    path = raw.parent.resolve()/raw.name
    need(path != ROOT and ROOT not in path.parents, 'output must be outside the source package')
    return path


def make_archive(package, target):
    files = inventory(package)
    with zipfile.ZipFile(target, 'x', compression=zipfile.ZIP_STORED) as archive:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo(name, STAMP)
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info, data)
    with zipfile.ZipFile(target) as archive:
        need(archive.namelist() == sorted(files), 'archive member inventory mismatch')
        for name, data in files.items():
            need(archive.read(name) == data, 'archive member content mismatch')


def build(output):
    sources = source_payload()
    output = fresh_output(output)
    with tempfile.TemporaryDirectory(prefix='report223-', dir=output.parent) as name:
        temp = Path(name)
        package, tex = temp/'package', temp/'tex'
        package.mkdir(); tex.mkdir()
        for member, data in sources.items():
            target = package/member
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        env = environment(temp)
        flags = ['-B']+(['-O'] if sys.flags.optimize else [])
        python = [sys.executable, *flags]
        generated = package/'generated'
        generated.mkdir()
        for script, filename in (('test_lengyel_exact.py', 'exact_checks.txt'),
                                 ('symbolic.py', 'symbolic.txt'),
                                 ('diagnostics.py', 'diagnostics.txt')):
            stdout = run([*python, str(package/'code'/script)], package, env)
            (generated/filename).write_text(stdout, encoding='utf-8')
        versions = run([*python, '-c',
                        'import json,sys,sympy,mpmath; print(json.dumps({'
                        '"python":sys.version.split()[0],"sympy":sympy.__version__,'
                        '"mpmath":mpmath.__version__},sort_keys=True))'], package, env)
        toolchain = json.loads(versions)
        toolchain['pdftex'] = run(['pdftex', '--version'], tex, env).splitlines()[0]
        (generated/'toolchain.json').write_text(json.dumps(toolchain, indent=2, sort_keys=True)+'\n')
        prepare_tex(tex, env)
        (tex/'Report223.tex').write_bytes(sources['Report223.tex'])
        (package/'Report223.pdf').write_bytes(compile_pdf(tex, env))
        (package/MANIFEST).write_bytes(manifest_bytes(inventory(package)))
        verify(package)
        # Only after all checks succeed publish a new output directory.
        output.mkdir()
        shutil.copytree(package, output/'package')
        make_archive(output/'package', output/ZIPNAME)
        artifacts = {ZIPNAME: (output/ZIPNAME).read_bytes(),
                     'package/Report223.pdf': (output/'package/Report223.pdf').read_bytes()}
        (output/'ARTIFACT_SHA256SUMS').write_bytes(manifest_bytes(artifacts))
    print('PASS full Report223 rebuild')
    print('PDF:', output/'package/Report223.pdf')
    print('ZIP:', output/ZIPNAME)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', help='new output directory outside this package')
    group.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    if args.verify_only:
        verify(ROOT)
    else:
        build(args.output)


if __name__ == '__main__':
    main()
