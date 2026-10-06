#!/usr/bin/env python3
"""Verify and reproduce the frozen Report236 without writing into its sources."""
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
sys.dont_write_bytecode = True
import tempfile
import zipfile

if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(640)
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from common import ARTIFACT_STEM
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
    required={'README.md','SOURCES.md','article.tex',ARTIFACT_STEM+'.pdf','build.py',
              'code/connected_wick.py','code/common.py','code/formal_factorization.py',
              'code/small_gaussian.py','code/verify_coefficients.py','code/inverse_reversion.py',
              'code/count_tables.py','code/diagnostics.py','code/density_coefficients.py','code/guard_tests.py','code/reproduce_zip.py',
              'code/connected_wick_receipt.json','code/verification_receipt.json',
              'code/table_count_receipt.json','code/guard_receipt.json',
              'requirements.txt','COMPUTATION.md'}
    if not required.issubset(expected):raise RuntimeError('required public package files missing')
    return expected


def new_output(value):
    if not isinstance(value,str) or not value:raise ValueError('output path must be nonempty')
    if '\\' in value:raise ValueError('backslash output components are forbidden')
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
    with log.open('xb') as handle:handle.write(result.stdout+result.stderr)
    if result.returncode:raise RuntimeError('command failed; inspect '+str(log))
    return result.stdout


def compile_pdf(logs):
    """Compile a disposable source copy; usable while authoring before freezing."""
    env=environment()
    with tempfile.TemporaryDirectory(prefix='report236-') as tmp:
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
            info=zipfile.ZipInfo(ARTIFACT_STEM+'/'+name,FIXED_TIME)
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
    receipts={}
    for script,name in (('connected_wick.py','connected_wick_receipt.json'),
                        ('verify_coefficients.py','verification_receipt.json'),
                        ('count_tables.py','table_count_receipt.json'),
                        ('guard_tests.py','guard_receipt.json')):
        result=run(python+[str(ROOT/'code'/script)],ROOT,env,logs/name)
        if result!=(ROOT/'code'/name).read_bytes():
            raise RuntimeError('fresh receipt differs from frozen receipt: '+name)
        receipts[name]=result
    pdf=compile_pdf(logs)
    if pdf!=(ROOT/(ARTIFACT_STEM+'.pdf')).read_bytes():
        with (out/(ARTIFACT_STEM+'-rebuilt-different.pdf')).open('xb') as handle:handle.write(pdf)
        raise RuntimeError('rebuilt PDF differs from frozen PDF; inspect TeX toolchain and logs')
    with (out/(ARTIFACT_STEM+'.pdf')).open('xb') as handle:handle.write(pdf)
    for name,data in receipts.items():
        with (out/name).open('xb') as handle:handle.write(data)
    version=run(['pdftex','-no-shell-escape','--version'],ROOT,env,logs/'toolchain.txt').decode('utf-8',errors='replace').splitlines()[0]
    if inventory()!=before:raise RuntimeError('source package changed during build')
    archive=out/(ARTIFACT_STEM+'.zip');make_zip(archive,before[0])
    if inventory()!=before:raise RuntimeError('source package changed during archive assembly')
    checks={'status':'PASS','mathematical_checks':'passed and byte-identical',
            'receipt_sha256':{name:hashlib.sha256(data).hexdigest() for name,data in receipts.items()},
            'guard_checks':'passed and byte-identical',
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
    with (out/'build_checks.json').open('x',encoding='utf-8',newline='\n') as handle:handle.write(encoded)
    print(encoded,end='')


if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:raise SystemExit(str(exc))
