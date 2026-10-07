#!/usr/bin/env python3
"""Run every check, generate tables/PDF, and make a byte-reproducible archive."""
import argparse
import hashlib
import importlib.metadata
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
CODE = ROOT/'code'
sys.path.insert(0,str(CODE))
EPOCH = '1791072000'  # 2026-10-04 00:00:00 UTC
ZIP_DATE = (2026,10,4,0,0,0)
MANIFEST = 'MANIFEST.sha256'
ARCHIVE = 'Report204.zip'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def verify_dependencies():
    for package,version in [('mpmath','1.3.0'),('sympy','1.14.0')]:
        actual = importlib.metadata.version(package)
        require(actual == version, f'{package} {version} required; found {actual}')


def prepare_tex(work):
    """Use isolated writable caches and a fresh installed-source TeX format."""
    locations = {}
    for name in ('home','tmp','texvar','texconfig','texcache','texhome','fonts'):
        location = work/name
        location.mkdir(exist_ok=True)
        locations[name] = str(location)
    env = {'PATH':os.environ.get('PATH',os.defpath),
           'HOME':locations['home'],'TMPDIR':locations['tmp'],
           'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1','TZ':'UTC',
           'LC_ALL':'C','LANG':'C','max_print_line':'1000',
           'TEXMFVAR':locations['texvar'],'TEXMFCONFIG':locations['texconfig'],
           'TEXMFCACHE':locations['texcache'],'TEXMFHOME':locations['texhome'],
           'VARTEXFONTS':locations['fonts'],'openout_any':'p','shell_escape':'f'}
    def run(command):
        result = subprocess.run(command,cwd=work,env=env,capture_output=True,
                                text=True,check=False,timeout=300)
        require(result.returncode == 0,'TeX preparation failed: '+str(command)
                +'\n'+(result.stdout+result.stderr)[-12000:])
        return result.stdout.strip()
    require(shutil.which('kpsewhich') and shutil.which('pdftex'),
            'kpsewhich and pdftex are required')
    dist = Path(run(['kpsewhich','-var-value=TEXMFDIST']))
    require(dist.is_dir(),'installed TeX distribution tree was not found')
    trees = [dist]
    sibling = dist.parent.parent/'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{'+','.join(map(str,trees))+'}'
    env['TEXFORMATS'] = str(work)+os.pathsep
    env['TEXFONTMAPS'] = str(work)+os.pathsep
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
         '-halt-on-error','-jobname=pdflatex','pdflatex.ini'])
    require((work/'pdflatex.fmt').is_file(),'local TeX format was not produced')
    maps = []
    for name in ('cm.map','cmextra.map','latxfont.map','symbols.map','lm.map'):
        path = Path(run(['kpsewhich',name]))
        require(path.is_file(),'installed font map missing: '+name)
        maps.append(path.read_bytes())
    (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    return env


def compile_pdf():
    require((ROOT/'Report204.tex').is_file(),'Report204.tex is missing')
    require(shutil.which('pdflatex') is not None,'pdflatex is required for the PDF build')
    work = ROOT/'.build'
    work.mkdir(exist_ok=True)
    for path in sorted(work.glob('Report204.*')):
        require(path.is_file() and not path.is_symlink(),'unexpected build path')
        path.unlink()
    env = prepare_tex(work)
    source = (r'\def\DoNotLoadEpstopdf{}\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15'
              r'\input{Report204.tex}')
    command = ['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error',
               '-no-shell-escape','-jobname=Report204','-output-directory=.build',source]
    previous = None
    for run in range(1,7):
        completed = subprocess.run(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT,check=False)
        (work/f'pdflatex-{run}.txt').write_bytes(completed.stdout)
        if completed.returncode != 0:
            raise RuntimeError('pdflatex failed:\n'+completed.stdout.decode('utf-8',errors='replace')[-12000:])
        state = tuple((work/('Report204.'+suffix)).read_bytes()
                      if (work/('Report204.'+suffix)).exists() else b''
                      for suffix in ('aux','toc','out'))
        if run >= 2 and state == previous:
            break
        previous = state
    else:
        raise RuntimeError('TeX references did not stabilize in six passes')
    log = (work/'Report204.log').read_text(errors='replace')
    unresolved = ('There were undefined references','There were undefined citations',
                  'Rerun to get cross-references right','Label(s) may have changed',
                  'There were multiply-defined labels')
    require(not any(message in log for message in unresolved),'unresolved TeX references')
    defects = re.findall(r'(?:Overfull[^\n]*|Underfull[^\n]*|Missing character:[^\n]*|'
                         r'(?:LaTeX(?: Font)?|Package \S+|Class \S+|pdfTeX|LuaTeX|XeTeX) Warning[^\n]*|'
                         r'^Warning:[^\n]*)',log,re.I|re.M)
    require(not defects,'TeX layout or warning defects: '+'; '.join(defects))
    require((work/'Report204.pdf').is_file(),'PDF build produced no PDF')
    shutil.copyfile(work/'Report204.pdf',ROOT/'Report204.pdf')


def public_files(include_manifest=True):
    excluded_dirs = {'.build','__pycache__','.git','.pytest_cache'}
    excluded_suffixes = ('.aux','.log','.out','.toc','.fls','.fdb_latexmk','.synctex.gz','.pyc','.pyo')
    result = []
    for path in sorted(ROOT.rglob('*')):
        relative = path.relative_to(ROOT)
        if any(part in excluded_dirs for part in relative.parts):
            continue
        if path.name == ARCHIVE or path.name.endswith(excluded_suffixes):
            continue
        if path.name == MANIFEST and not include_manifest:
            continue
        require(not path.is_symlink(),'public package may not depend on symbolic links')
        if path.is_file():
            result.append(path)
    return result


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def package():
    files = public_files(include_manifest=False)
    manifest = ''.join(digest(path)+'  '+path.relative_to(ROOT).as_posix()+'\n' for path in files)
    (ROOT/MANIFEST).write_text(manifest,encoding='utf-8')
    files = public_files()
    # STORE avoids implementation-dependent compression streams. Times and modes
    # are assigned explicitly; file-system mtimes and umask have no effect.
    with zipfile.ZipFile(ROOT/ARCHIVE,'w',compression=zipfile.ZIP_STORED) as archive:
        for path in files:
            info = zipfile.ZipInfo(path.relative_to(ROOT).as_posix(),ZIP_DATE)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info,path.read_bytes())
    with zipfile.ZipFile(ROOT/ARCHIVE) as archive:
        require(archive.testzip() is None,'archive CRC check failed')
        require(archive.namelist() == [p.relative_to(ROOT).as_posix() for p in files],
                'archive membership mismatch')
        for path in files:
            require(archive.read(path.relative_to(ROOT).as_posix()) == path.read_bytes(),
                    'archive content mismatch')
        for line in archive.read(MANIFEST).decode('utf-8').splitlines():
            expected,name = line.split('  ',1)
            require(hashlib.sha256(archive.read(name)).hexdigest() == expected,
                    'manifest mismatch for '+name)
    return ROOT/ARCHIVE


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checks-only',action='store_true',
                        help='run the complete computation suite and generate tables, without PDF/ZIP')
    args = parser.parse_args()
    verify_dependencies()
    from exact_checks import run as exact_run
    from numerical_diagnostics import run as numerical_run
    from tables import write_tables
    from manuscript_checks import run as manuscript_run
    exact = exact_run(CODE/'results')
    print(f"Passed {exact['explicit_checks']} explicit exact checks",flush=True)
    numerical = numerical_run(CODE/'results')
    write_tables(numerical,ROOT/'tables.tex')
    manuscript = manuscript_run(ROOT/'Report204.tex',numerical,CODE/'results')
    print(f"Checked {manuscript['numeric_cells_checked']} printed numerical cells",flush=True)
    print('Passed independent coefficient and inverse numerical diagnostics',flush=True)
    if not args.checks_only:
        compile_pdf()
        archive = package()
        print('Built Report204.pdf and '+archive.name,flush=True)
        print('Archive SHA-256: '+digest(archive),flush=True)


if __name__ == '__main__':
    main()
