#!/usr/bin/env python3
"""Check actual files and replay every public calculation with explicit guards."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok: raise RuntimeError(message)

def digest(data): return hashlib.sha256(data).hexdigest()

def safe(name):
    p=PurePosixPath(name)
    need(isinstance(name,str) and not p.is_absolute() and '\\' not in name and
         all(x not in ('','.','..') for x in p.parts) and str(p)==name,'Unsafe manifest name')
    return p

def manifest_check():
    path=ROOT/'MANIFEST.json'
    need(path.is_file() and not path.is_symlink(),'Manifest must be a regular file')
    obj=json.loads(path.read_text())
    need(obj['schema']==1,'Manifest schema')
    files=obj['files']
    need(isinstance(files,dict) and 'MANIFEST.json' not in files,'Bad manifest inventory')
    for name,pin in files.items():
        rel=safe(name);p=ROOT/rel
        need(p.is_file() and not p.is_symlink(),'Missing or symlink file '+name)
        need(len(pin)==64 and digest(p.read_bytes())==pin,'Hash mismatch '+name)
    actual=set()
    for p in ROOT.rglob('*'):
        need(not p.is_symlink(),'Symlink member')
        if p.is_file():actual.add(p.relative_to(ROOT).as_posix())
        else:need(p.is_dir(),'Special member')
    need(actual==set(files)|{'MANIFEST.json'},'Actual file inventory mismatch')
    return len(actual)

def run(script,args=()):
    flags=['-B']+(['-O'] if sys.flags.optimize else [])
    p=subprocess.run([sys.executable,*flags,str(ROOT/script),*map(str,args)],
                     cwd=ROOT,capture_output=True,timeout=300)
    need(p.returncode==0,'Replay failed '+script+'\n'+p.stderr.decode(errors='replace'))
    return p.stdout

count=manifest_check()
for script,expected in [('repro/verify_exact.py','repro/exact.json'),
                        ('repro/verify_coefficients.py','repro/coefficients_check.txt'),
                        ('repro/diagnostics.py','repro/diagnostics.json'),
                        ('repro/derive_coefficients.py','repro/coefficients.json')]:
    args=('--order','4') if 'derive_' in script else ()
    need(run(script,args)==(ROOT/expected).read_bytes(),'Replay byte mismatch '+expected)
need(run('repro/build_tables.py',('--check',)).startswith(b'PASS:'),'Table check failed')
with tempfile.TemporaryDirectory(prefix='report211-replay-') as temp:
    pdf=Path(temp)/'Report211.pdf'
    run('build_pdf.py',('--output',pdf))
    need(pdf.read_bytes()==(ROOT/'Report211.pdf').read_bytes(),
         'Rebuilt PDF differs; inspect TeX environment/version before claiming byte reproduction')
need(manifest_check()==count,'Source changed during checks')
print(json.dumps({'status':'PASS','actual_member_files':count,'manifest':'all members checked',
                  'replay':'exact, symbolic, diagnostics, generator, numeric tables and PDF byte-identical',
                  'assertions_required':False},indent=2,sort_keys=True))
