#!/usr/bin/env python3
"""Compare current first selections of direct endpoint source imports only."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
parent=here.parent
lower=json.loads((parent/'trace74-n5-r9-lower-draft/observations/attempt01/terminal.json').read_text())
upper=json.loads((parent/'trace74-n5-r9-upper-bound-draft/observations/attempt01/terminal.json').read_text())
pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
lo=Path('/tmp/trace74-n5-r9-lower-vww54v8f/lib')
up=Path('/tmp/trace74-n5-r9-upper-bound-gtjvynbj/lib')
uc=Path('/tmp/trace74-n5-r9-upper-cert-j22gd2eu/lib')
join=[lo,up,uc,pack]
names=['Mathlib/Algebra/Order/Ring/Basic','Mathlib/Tactic/Ring',
       'Mathlib/Tactic/Positivity','Mathlib/Tactic/Linarith']
def select(path,name):
    for root in map(Path,path):
        p=root/(name+'.olean')
        if p.is_symlink() and not p.exists(): raise RuntimeError('dangling shadow: '+str(p))
        if p.is_file():
            return {'path':str(p),'target':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    raise RuntimeError('missing '+name)
rows={}
for name in names:
    row={key:select(path,name) for key,path in [('lower',lower['lean_path'].split(':')),
                                               ('upper',upper['lean_path'].split(':')),
                                               ('join',join)]}
    assert len({(v['target'],v['sha256']) for v in row.values()})==1,(name,row)
    rows[name]=row
for name,path,expected in [
    ('Trace74N5R9LowerCertificate',lower['lean_path'].split(':'),lo),
    ('Trace74N5R9UpperCertificate',upper['lean_path'].split(':'),uc)]:
    a=select(path,name);b=select(join,name)
    assert (a['target'],a['sha256'])==(b['target'],b['sha256']) and Path(b['path']).parent==expected
    rows[name]={'producer':a,'join':b}
for name,expected in [('Trace74N5R9LowerBound',lo),('Trace74N5R9UpperBound',up)]:
    a=select(join,name);assert Path(a['path']).parent==expected
    rows[name]={'join':a}
print(json.dumps({'status':'PASS','join_path':list(map(str,join)),
 'scope':'current direct source-import first selections and hashes only; no serialized transitive/package or producer-time ancestry capture',
 'selections':rows},sort_keys=True,indent=2))
