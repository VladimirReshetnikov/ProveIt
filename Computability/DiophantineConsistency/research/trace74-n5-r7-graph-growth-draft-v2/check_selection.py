#!/usr/bin/env python3
"""Current direct-source-import selection comparison; not a closure capture."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; parent=here.parent
grow=json.loads((parent/'trace74-n5-r7-growth-draft/observations/attempt01/terminal.json').read_text())
y7=json.loads((parent/'trace74-n4-r7-pell-identity-draft/observations/attempt01/terminal.json').read_text())
gp=Path('/tmp/trace74-n5-r7-growth-ewym4ilo/lib');yp=Path('/tmp/trace74-n4-r7-pell-identity-s0_o0sqr/lib')
old=y7['lean_path'].split(':'); join=[gp,*map(Path,old)]
names=['Mathlib/Algebra/Order/Ring/Basic','Mathlib/Tactic/Ring',
       'Mathlib/Tactic/Positivity','Mathlib/Tactic/Linarith']
def select(roots,name):
    for root in map(Path,roots):
        p=root/(name+'.olean')
        if p.is_symlink() and not p.exists():raise RuntimeError('dangling shadow: '+str(p))
        if p.is_file():return {'path':str(p),'target':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    raise RuntimeError('missing '+name)
rows={}
for name in names:
    row={k:select(path,name) for k,path in [('growth',grow['lean_path'].split(':')),('y7',old),('join',join)]}
    assert len({(v['target'],v['sha256']) for v in row.values()})==1,(name,row)
    rows[name]=row
for name in ['Trace74N2FifthGrowth','Trace74Pell']:
    a=select(old,name);b=select(join,name);assert (a['target'],a['sha256'])==(b['target'],b['sha256'])
    rows[name]={'y7':a,'join':b}
for name,root in [('Trace74N5R7Growth',gp),('Trace74N4R7PellIdentity',yp)]:
    a=select(join,name);assert Path(a['path']).parent==root;rows[name]={'join':a}
print(json.dumps({'status':'PASS','join_path':list(map(str,join)),'selections':rows,
 'scope':'current direct imports and first selections only; no full transitive/package or producer-time ancestry capture'},sort_keys=True,indent=2))
