#!/usr/bin/env python3
"""Deterministic local PDF and ZIP builder; no downloads or package installation."""
import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

ROOT=Path(__file__).resolve().parent
EPOCH='1791072000'  # 2026-10-04 UTC
ZIP_DATE=(2026,10,4,0,0,0)
MANIFEST='SHA256SUMS'
ARCHIVE='Report222.zip'


def require(condition,message):
    if not condition:
        raise RuntimeError(message)


def tex_environment(work):
    """Use installed TeX sources with writable local caches and a fresh format."""
    env={key:os.environ[key] for key in ('PATH','SYSTEMROOT') if key in os.environ}
    for variable,subdir in [('HOME','home'),('TMPDIR','tmp'),('TEXMFVAR','texvar'),
                           ('TEXMFCONFIG','texconfig'),('TEXMFCACHE','texcache'),
                           ('TEXMFHOME','texhome'),('VARTEXFONTS','fonts')]:
        directory=work/subdir
        directory.mkdir(parents=True,exist_ok=True)
        env[variable]=str(directory)
    env.update(SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',TZ='UTC',
               LC_ALL='C',LANG='C',max_print_line='1000',openout_any='p',shell_escape='f')
    def run(command):
        result=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True,timeout=300)
        require(result.returncode==0,'TeX preparation failed:\n'+(result.stdout+result.stderr)[-12000:])
        return result.stdout.strip()
    require(shutil.which('kpsewhich') and shutil.which('pdftex'),'Installed TeX Live with kpsewhich and pdftex is required')
    dist=Path(run(['kpsewhich','-var-value=TEXMFDIST']))
    require(dist.is_dir(),'Installed TeX source tree unavailable')
    trees=[dist]
    sibling=dist.parent.parent/'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF']='{'+','.join(map(str,trees))+'}'
    env['TEXFORMATS']=str(work)+os.pathsep
    env['TEXFONTMAPS']=str(work)+os.pathsep
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
         '-halt-on-error','-jobname=pdflatex','pdflatex.ini'])
    maps=[]
    for name in ('cm.map','cmextra.map','latxfont.map','symbols.map','lm.map'):
        path=Path(run(['kpsewhich',name]))
        require(path.is_file(),'Installed font map missing: '+name)
        maps.append(path.read_bytes())
    (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    return env


def pdf():
    work=ROOT/'.build'
    work.mkdir(exist_ok=True)
    env=tex_environment(work)
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
             '-file-line-error','-jobname=Report222','-output-directory=.build','article.tex']
    previous=None
    for number in range(1,7):
        result=subprocess.run(command,cwd=ROOT,env=env,capture_output=True,timeout=300)
        (work/f'compile-{number}.txt').write_bytes(result.stdout+result.stderr)
        require(result.returncode==0,'PDF compilation failed:\n'+(result.stdout+result.stderr).decode(errors='replace')[-12000:])
        state=tuple((work/f'Report222.{suffix}').read_bytes() if (work/f'Report222.{suffix}').exists() else b'' for suffix in ('aux','toc','out'))
        if number>=2 and state==previous:
            break
        previous=state
    else:
        raise RuntimeError('References did not stabilize')
    log=(work/'Report222.log').read_text(errors='replace')
    bad=('There were undefined references','There were undefined citations',
         'Rerun to get cross-references right','Label(s) may have changed','There were multiply-defined labels','Missing character:')
    require(not any(x in log for x in bad),'Unresolved references or missing glyphs')
    overflow=re.findall(r'Overfull[^\n]*',log)
    require(not overflow,'Overfull layout: '+'; '.join(overflow))
    shutil.copyfile(work/'Report222.pdf',ROOT/'Report222.pdf')
    return ROOT/'Report222.pdf'


def public_files(include_manifest=True):
    files=[]
    for path in sorted(ROOT.rglob('*')):
        rel=path.relative_to(ROOT)
        if any(part.startswith('.') or part=='__pycache__' for part in rel.parts):
            continue
        if path.name==ARCHIVE or path.suffix in ('.aux','.log','.toc','.out','.pyc','.pyo'):
            continue
        if not include_manifest and path.name==MANIFEST:
            continue
        require(not path.is_symlink(),'Symlinks are not permitted in public files')
        if path.is_file():
            files.append(path)
    return files


def package():
    files=public_files(False)
    require(ROOT/'Report222.pdf' in files,'Build the PDF first')
    (ROOT/MANIFEST).write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix()+'\n' for p in files),encoding='ascii')
    files=public_files()
    with zipfile.ZipFile(ROOT/ARCHIVE,'w',compression=zipfile.ZIP_STORED) as archive:
        for path in files:
            info=zipfile.ZipInfo(path.relative_to(ROOT).as_posix(),ZIP_DATE)
            info.create_system=3
            info.external_attr=0o100644 << 16
            info.compress_type=zipfile.ZIP_STORED
            archive.writestr(info,path.read_bytes())
    with zipfile.ZipFile(ROOT/ARCHIVE) as archive:
        require(archive.testzip() is None,'ZIP integrity failure')
        require(archive.namelist()==[p.relative_to(ROOT).as_posix() for p in files],'ZIP membership failure')
        for line in archive.read(MANIFEST).decode().splitlines():
            digest,name=line.split('  ',1)
            require(hashlib.sha256(archive.read(name)).hexdigest()==digest,'ZIP manifest mismatch')
    return ROOT/ARCHIVE


def checks(optional=False):
    results=ROOT/'results'
    results.mkdir(exist_ok=True)
    commands=[('analytic_bounds.json',['code/certify_bounds.py']),('exact_checks.json',['code/test_exact.py'])]
    if optional:
        commands.extend([('palette_jets.json',['code/palette_jets.py']),('diagnostics.json',['code/diagnostics.py','--tv'])])
    for name,args in commands:
        command=[sys.executable]
        if sys.flags.optimize:
            command.append('-O')
        result=subprocess.run(command+args,cwd=ROOT,capture_output=True,timeout=1200)
        require(result.returncode==0,'Check failed: '+' '.join(args)+'\n'+result.stderr.decode(errors='replace'))
        (results/name).write_bytes(result.stdout)
    table=subprocess.run([sys.executable,'code/make_tables.py'],cwd=ROOT,capture_output=True,timeout=60)
    require(table.returncode==0,'Table generation failed')
    (ROOT/'tables.tex').write_bytes(table.stdout)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checks',action='store_true',help='run portable exact checks before building')
    parser.add_argument('--optional',action='store_true',help='also regenerate SymPy/mpmath diagnostics; implies --checks')
    parser.add_argument('--pdf-only',action='store_true')
    parser.add_argument('--zip-only',action='store_true')
    args=parser.parse_args()
    require(not(args.pdf_only and args.zip_only),'Choose at most one build-only mode')
    if args.checks or args.optional:
        checks(args.optional)
    if not args.zip_only:
        print(pdf().name)
    if not args.pdf_only:
        print(package().name)


if __name__=='__main__':
    main()
