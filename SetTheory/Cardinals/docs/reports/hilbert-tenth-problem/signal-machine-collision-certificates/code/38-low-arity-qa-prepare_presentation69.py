"""Presentation-only Report69 initialization: inert copies, metadata and text adaptation.
No scientific module is imported or executed.
"""
from pathlib import Path
import hashlib, json, os, stat
R=Path('/workspace/shared/report69-low-arity-compilers-release-20261004')
P=Path('/workspace/shared/report68-gap-statistics-release-20261004')
PROTECTED=[
'/workspace/shared/two-witness-tensor-compiler-20261004',
'/workspace/shared/three-witness-bounded-halting-20261004',
'/workspace/shared/three-witness-independent-audit-20261004',
'/workspace/shared/positive-power12-continuation-20261004',
'/workspace/shared/independent-power12-audit-20261004',
'/workspace/shared/report66-bounded-certificates-counting-release-20261004',
'/workspace/shared/report67-power-reductions-release-20261004',
'/workspace/shared/report68-gap-statistics-release-20261004']
def enc(x): return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
    out={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat(); assert stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode)
        row={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'kind':'directory' if p.is_dir() else 'file'}
        if p.is_file():
            assert s.st_nlink==1
            b=p.read_bytes(); row.update(bytes=len(b),sha256=sha(b))
        out[str(p)]=row
    return out
original={}
for name in PROTECTED: original.update(inventory(Path(name)))
(R/'qa/ORIGINAL_INPUT_METADATA.json').write_bytes(enc(original))
(R/'qa/PRESENTATION_ORIGINS.json').write_bytes(enc({'scope':'Report69-owned adaptation of fully read accepted Report68 presentation tools; prior tools retained inertly','predecessor_files':{n:sha((P/n).read_bytes()) for n in ['tools/build_report68.py','tools/release68.py','tools/selftest68.py','README.md']},'read_complete':True,'scientific_execution':False}))
(R/'audits/AUDIT_STATUS.md').write_text('Fresh full audit in progress; this file is authoring-only and will be replaced before sealing.\n')
source_roots={'science/low-arity':PROTECTED[0]}
files={}; directories={}; roots={}
for scope in ('science','audits'):
    inv=inventory(R/scope)
    for full,row in inv.items():
        p=Path(full); rel=p.relative_to(R).as_posix(); row=dict(row); kind=row.pop('kind')
        if rel==scope: roots[scope]=row
        elif kind=='file': files[rel]=row
        else: directories[rel]=row
pins={'format':'Report69 frozen input pins v1','roots':roots,'source_roots':source_roots,'files':files,'directories':directories}
pindata=enc(pins); (R/'INPUT_PINS.json').write_bytes(pindata)
for old,new in [('release68.py','release69.py'),('build_report68.py','build_report69.py'),('selftest68.py','selftest69.py')]:
    text=(P/'tools'/old).read_text().replace('Report68','Report69').replace('report68','report69').replace('release68','release69').replace('selftest68','selftest69')
    if old=='release68.py':
        lines=text.splitlines()
        for i,line in enumerate(lines):
            if line.startswith('INPUT_PINS_SHA256 ='): lines[i]='INPUT_PINS_SHA256 = '+repr(sha(pindata))
            if line.startswith('MODULES ='): lines[i]="MODULES = ('Report69.tex', 'tensor.tex', 'one-witness.tex', 'classification.tex', 'costs.tex', 'power.tex', 'scope.tex')"
            if line.startswith('PROTECTED ='): lines[i]='PROTECTED = ('+', '.join('Path('+repr(p)+')' for p in PROTECTED)+')'
        text='\n'.join(lines)+'\n'
    if old=='selftest68.py':
        text=text.replace('science/counting','science/low-arity')
        text=text.replace("target = clone('extra-input'); (target / 'science/low-arity/unexpected.txt').write_text('unexpected')", "target = clone('extra-input'); (target / 'science/low-arity').chmod(0o755); (target / 'science/low-arity/unexpected.txt').write_text('unexpected')")
        text=text.replace("target = clone('empty-input'); (target / 'science/low-arity/empty').mkdir()", "target = clone('empty-input'); (target / 'science/low-arity').chmod(0o755); (target / 'science/low-arity/empty').mkdir()")
    (R/'tools'/new).write_text(text)
p=R/'tools/build_report69.py'; lines=p.read_text().splitlines()
for i,line in enumerate(lines):
    if line.startswith('HELPER_SHA256 ='): lines[i]='HELPER_SHA256 = '+repr(sha((R/'tools/release69.py').read_bytes()))
p.write_text('\n'.join(lines)+'\n')
print('Report69 initial presentation tools and input snapshots prepared')
