#!/usr/bin/env python3
"""Verify, compile and package Report 226 without changing this source tree."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile
ROOT=Path(__file__).resolve().parent
FIXED_TIME=(2026,10,5,0,0,0)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def files():
    return sorted(p for p in ROOT.rglob('*') if p.is_file() and p.relative_to(ROOT).as_posix() not in {'Report226.pdf','build_checks.json'})

def snapshot():
    return {p.relative_to(ROOT).as_posix():digest(p) for p in files()}

def validate_source():
    manifest=ROOT/'MANIFEST.sha256'
    expected={}
    for line in manifest.read_text().splitlines():
        checksum,name=line.split('  ',1)
        expected[name]=checksum
    actual=snapshot();actual.pop('MANIFEST.sha256',None)
    if actual != expected:
        raise RuntimeError('source manifest mismatch (including extra or missing files)')

def output_path(value):
    raw=Path(os.path.abspath(value))
    if any(p.is_symlink() for p in [raw,*raw.parents]):
        raise ValueError('output must have no symlink ancestor')
    if raw.exists(): raise ValueError('output directory must not exist')
    if raw == ROOT or ROOT in raw.parents:
        raise ValueError('output must be outside the source package')
    return raw

def run(command,cwd,env,log):
    with log.open('w') as stream:
        result=subprocess.run(command,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'command failed ({result.returncode}); see {log}')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',required=True)
    ap.add_argument('--cap',type=int,default=414)
    args=ap.parse_args()
    if args.cap != 414: ap.error('this build is tested at cap 414; use --cap 414')
    try: out=output_path(args.out)
    except ValueError as exc: ap.error(str(exc))
    validate_source();before=snapshot()
    out.mkdir(parents=True)
    logs=out/'logs';logs.mkdir()
    work=out/'tex_work';work.mkdir()
    env=os.environ.copy()
    env.update({'PYTHONDONTWRITEBYTECODE':'1','SOURCE_DATE_EPOCH':'1791158400','FORCE_SOURCE_DATE':'1','TZ':'UTC'})
    py=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
    run(py+[str(ROOT/'code/test_exact.py'),'--cap',str(args.cap)],out,env,logs/'exact_tests.json')
    checks={'exact':json.loads((logs/'exact_tests.json').read_text())}
    run(py+[str(ROOT/'code/clock_checks.py')],out,env,logs/'symbolic_checks.json')
    checks['symbolic']=json.loads((logs/'symbolic_checks.json').read_text())
    if checks['symbolic'] != json.loads((ROOT/'data/symbolic_checks.json').read_text()):
        raise RuntimeError('symbolic output differs from recorded public checks')
    run(py+[str(ROOT/'code/test_guards.py')],out,env,logs/'guard_checks.json')
    guards=json.loads((logs/'guard_checks.json').read_text())
    # Optimization and the caller's integer-string limit are intentionally logged
    # but are not output identity: both modes must run the same actual checks.
    guards.pop('optimization',None); guards.pop('integer_string_limit',None)
    checks['guards']=guards
    for source in (ROOT/'src').iterdir(): shutil.copyfile(source,work/source.name)
    # Build a private format to avoid user-global TeX cache writes. A stripped
    # TeX Live installation may need an unindexed system tree (without !!).
    if Path('/usr/share/texlive/texmf-dist').exists() and not env.get('TEXMF'):
        env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
    env['TEXMFVAR']=str(work/'texmf-var')
    env['TEXMFCONFIG']=str(work/'texmf-config')
    run(['pdftex','-ini','-etex','-jobname=pdflatex','-progname=pdflatex','-interaction=nonstopmode','-halt-on-error','pdflatex.ini'],work,env,logs/'format.log')
    for pass_no in range(3):
        run(['pdflatex','-fmt=./pdflatex.fmt','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','report226.tex'],work,env,logs/f'latex{pass_no+1}.log')
    log=(work/'report226.log').read_text(errors='replace')
    if 'Overfull \\hbox' in log or 'Overfull \\vbox' in log or 'undefined references' in log or 'There were undefined' in log or 'Missing character:' in log:
        raise RuntimeError('TeX layout/reference warning requires inspection')
    pdf=out/'Report226.pdf';shutil.copyfile(work/'report226.pdf',pdf)
    checks['pdf_sha256']=digest(pdf)
    checks['source_manifest_sha256']=digest(ROOT/'MANIFEST.sha256')
    receipt=json.dumps(checks,sort_keys=True,indent=2).encode()+b'\n'
    (out/'build_checks.json').write_bytes(receipt)
    if snapshot()!=before: raise RuntimeError('source tree changed during build')
    members={p.relative_to(ROOT).as_posix():p.read_bytes() for p in files()}
    members.update({'Report226.pdf':pdf.read_bytes(),'build_checks.json':receipt})
    with zipfile.ZipFile(out/'Report226.zip','w',compression=zipfile.ZIP_STORED) as archive:
        for name,data in sorted(members.items()):
            info=zipfile.ZipInfo('Report226/'+name,FIXED_TIME)
            info.compress_type=zipfile.ZIP_STORED
            info.create_system=3
            info.external_attr=(0o100644 << 16)
            archive.writestr(info,data)
    print(json.dumps({'pdf_sha256':digest(pdf),'zip_sha256':digest(out/'Report226.zip'),
                      'zip_members':len(members),'status':'built'},sort_keys=True,indent=2))

if __name__=='__main__': main()
