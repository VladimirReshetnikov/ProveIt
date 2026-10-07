#!/usr/bin/env python3
"""Verify and reproduce the frozen Report234 without writing into its sources."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(640)
ROOT=Path(__file__).resolve().parent
FIXED_TIME=(2026,10,5,0,0,0)
EPOCH='1791158400'


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory():
    files={};directories=set()
    for path in sorted(ROOT.rglob('*')):
        mode=path.lstat().st_mode
        name=path.relative_to(ROOT).as_posix()
        if stat.S_ISLNK(mode):raise RuntimeError('source symlink forbidden: '+name)
        if stat.S_ISREG(mode):files[name]=digest(path)
        elif stat.S_ISDIR(mode):directories.add(name)
        else:raise RuntimeError('nonregular source entry: '+name)
    return files,directories


def verify():
    actual,directories=inventory()
    expected={}
    for line in (ROOT/'MANIFEST.sha256').read_text(encoding='utf-8').splitlines():
        try:checksum,name=line.split('  ',1)
        except ValueError as exc:raise RuntimeError('malformed manifest line') from exc
        if (len(checksum)!=64 or any(c not in '0123456789abcdef' for c in checksum)
            or not name or name.startswith('/') or '\\' in name
            or any(part in ('','.','..') for part in name.split('/'))
            or name in expected or name=='MANIFEST.sha256'):
            raise RuntimeError('malformed manifest entry')
        expected[name]=checksum
    if not expected:raise RuntimeError('empty manifest')
    actual.pop('MANIFEST.sha256',None)
    if actual!=expected:
        changed=sorted(set(actual)^set(expected)|{name for name in actual.keys()&expected.keys() if actual[name]!=expected[name]})
        raise RuntimeError('manifest mismatch: '+', '.join(changed))
    expected_dirs={parent.as_posix() for name in expected for parent in Path(name).parents if parent.as_posix()!='.'}
    if directories!=expected_dirs:raise RuntimeError('unexpected or missing source directories')
    required={'README.md','SOURCES.md','article.tex','Report234.pdf','build.py',
              'code/checks.py','code/record_sum.py','code/guard_tests.py',
              'code/reproduce_zip.py','code/receipt.json','code/guard_receipt.json'}
    if not required.issubset(expected):raise RuntimeError('required public package files missing')
    return expected


def new_output(value):
    # Reject dot components before abspath can hide a symlink followed by '..'.
    if any(part in ('.','..') for part in value.split(os.sep)):
        raise ValueError('output path must not contain dot or dot-dot components')
    out=Path(os.path.abspath(value))
    for path in (out,*out.parents):
        if path.is_symlink():raise ValueError('output path has a live or dangling symlink ancestor')
    if out.exists():raise ValueError('output directory must be new')
    if out==ROOT or ROOT in out.parents:raise ValueError('output must be outside the source package')
    if not out.parent.is_dir():raise ValueError('output parent must already exist')
    return out


def environment():
    env=os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONINTMAXSTRDIGITS='640',
               PYTHONHASHSEED='0',SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C')
    return env


def run(command,cwd,env,log):
    result=subprocess.run(command,cwd=cwd,env=env,capture_output=True,check=False)
    log.write_bytes(result.stdout+result.stderr)
    if result.returncode:raise RuntimeError('command failed; inspect '+str(log))
    return result.stdout


def compile_pdf(logs):
    """Compile a disposable source copy; usable while authoring before freezing."""
    env=environment()
    with tempfile.TemporaryDirectory(prefix='report234-') as tmp:
        work=Path(tmp)
        shutil.copyfile(ROOT/'article.tex',work/'article.tex')
        shutil.copytree(ROOT/'sections',work/'sections')
        if Path('/usr/share/texlive/texmf-dist').exists():
            env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
        env['TEXMFVAR']=str(work/'texmf-var');env['TEXMFCONFIG']=str(work/'texmf-config')
        # Build a private format, avoiding global texmf caches or source-tree files.
        run(['pdftex','-ini','-no-shell-escape','-etex','-jobname=pdflatex','-progname=pdflatex',
             '-interaction=nonstopmode','-halt-on-error','pdflatex.ini'],work,env,logs/'format.txt')
        for iteration in range(1,4):
            run(['pdflatex','-fmt=./pdflatex.fmt','-no-shell-escape',
                 '-interaction=nonstopmode','-halt-on-error','article.tex'],work,env,
                logs/('latex%d.txt'%iteration))
        log=(work/'article.log').read_text(errors='replace')
        forbidden=('Overfull \\hbox','Overfull \\vbox','Missing character:',
                   'There were undefined','undefined references','Rerun to get cross-references')
        if any(word in log for word in forbidden):
            raise RuntimeError('TeX layout/reference warning requires review')
        return (work/'article.pdf').read_bytes()


def make_zip(path,files):
    with zipfile.ZipFile(path,'x',compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(files):
            info=zipfile.ZipInfo('Report234/'+name,FIXED_TIME)
            info.create_system=3;info.compress_type=zipfile.ZIP_STORED
            info.external_attr=0o100644<<16
            archive.writestr(info,(ROOT/name).read_bytes())


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only',action='store_true')
    parser.add_argument('--output-dir','--output',dest='output',help='new output directory outside source package')
    args=parser.parse_args()
    if args.verify_only and args.output:parser.error('choose --verify-only or --output-dir')
    if not args.verify_only and not args.output:parser.error('a build requires --output-dir')
    out=None
    if args.output:
        try:out=new_output(args.output)
        except ValueError as exc:parser.error(str(exc))
    sources=verify()
    if args.verify_only:
        print(json.dumps({'status':'verified','files':len(sources)},sort_keys=True));return
    before=inventory()
    # Atomic exclusive creation; neither reuse nor merge into an existing directory.
    out.mkdir(exist_ok=False)
    logs=out/'logs';logs.mkdir()
    env=environment()
    python=[sys.executable,'-B']+(['-'+'O'*sys.flags.optimize] if sys.flags.optimize else [])
    receipt=run(python+[str(ROOT/'code/checks.py')],ROOT,env,logs/'exact_checks.json')
    if receipt!=(ROOT/'code/receipt.json').read_bytes():
        raise RuntimeError('fresh exact certificate differs from frozen receipt')
    guard_receipt=run(python+[str(ROOT/'code/guard_tests.py')],ROOT,env,logs/'guard_checks.json')
    if guard_receipt!=(ROOT/'code/guard_receipt.json').read_bytes():
        raise RuntimeError('fresh guard tests differ from frozen receipt')
    pdf=compile_pdf(logs)
    if pdf!=(ROOT/'Report234.pdf').read_bytes():
        (out/'Report234-rebuilt-different.pdf').write_bytes(pdf)
        raise RuntimeError('rebuilt PDF differs from frozen PDF; inspect TeX toolchain and logs')
    (out/'Report234.pdf').write_bytes(pdf)
    shutil.copyfile(ROOT/'code/receipt.json',out/'exact_checks.json')
    shutil.copyfile(ROOT/'code/guard_receipt.json',out/'guard_checks.json')
    version=run(['pdftex','-no-shell-escape','--version'],ROOT,env,logs/'toolchain.txt').decode('utf-8',errors='replace').splitlines()[0]
    if inventory()!=before:raise RuntimeError('source package changed during build')
    archive=out/'Report234.zip';make_zip(archive,before[0])
    if inventory()!=before:raise RuntimeError('source package changed during archive assembly')
    checks={'status':'PASS','exact_checks':'passed and byte-identical',
            'exact_receipt_sha256':hashlib.sha256(receipt).hexdigest(),
            'guard_checks':'passed and byte-identical',
            'guard_receipt_sha256':hashlib.sha256(guard_receipt).hexdigest(),
            'manifest_sha256':digest(ROOT/'MANIFEST.sha256'),
            'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'pdf_matches_frozen':True,
            'zip_sha256':digest(archive),'zip_members':len(before[0]),
            'source_files':before[0],'source_tree_unchanged':True,
            'reproducibility':{'python':sys.version.split()[0],'pdftex':version,
                'SOURCE_DATE_EPOCH':EPOCH,'timezone':'UTC','zip_method':'stored',
                'zip_timestamp':list(FIXED_TIME),'zip_mode':'100644',
                'python_children_no_bytecode':True,'PYTHONINTMAXSTRDIGITS':640,
                'private_tex_cache':True,'shell_escape':False}}
    encoded=json.dumps(checks,indent=2,sort_keys=True)+'\n'
    (out/'build_checks.json').write_text(encoded,encoding='utf-8')
    print(encoded,end='')


if __name__=='__main__':
    try:main()
    except (RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
