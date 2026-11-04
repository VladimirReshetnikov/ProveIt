#!/usr/bin/env python3
"""Current direct-source-import selections only; no closure capture."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;parent=here.parent
lower=json.loads((parent/'trace74-n6-r11-scalar-draft/observations/attempt01/terminal.json').read_text())
upper=json.loads((parent/'trace74-n6-r11-upper-compact-draft-v4/observations/attempt01/terminal.json').read_text())
assert lower['status']=='FAIL' and lower['stages'][0]['module']=='Trace74N6R11LowerCertificate' and lower['stages'][0]['status']=='PASS'
assert upper['status']=='PASS'
lo=Path('/tmp/trace74-n6-r11-scalar-h80u7iit/lib');up=Path('/tmp/trace74-n6-r11-upper-compact-v4-0up3vfpa/lib');pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
join=[lo,up,pack]
def select(roots,name):
    for root in map(Path,roots):
        p=root/(name+'.olean')
        if p.is_symlink() and not p.exists():raise RuntimeError('dangling shadow: '+str(p))
        if p.is_file():return {'path':str(p),'target':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    raise RuntimeError('missing '+name)
rows={}
for name in ['Mathlib/Algebra/Order/Ring/Basic','Mathlib/Tactic/Ring','Mathlib/Tactic/Positivity','Mathlib/Tactic/Linarith']:
    row={k:select(path,name) for k,path in [('lower',lower['lean_path'].split(':')),('upper',upper['lean_path'].split(':')),('join',join)]}
    assert len({(v['target'],v['sha256']) for v in row.values()})==1,(name,row)
    rows[name]=row
for name,path,expected in [('Trace74N6R11LowerCertificate',lower['lean_path'].split(':'),lo),('Trace74N6R11CompactBase',upper['lean_path'].split(':'),up)]:
    a=select(path,name);b=select(join,name)
    assert (a['target'],a['sha256'])==(b['target'],b['sha256']) and Path(b['path']).parent==expected
    rows[name]={'producer':a,'join':b}
name='Trace74N6R11CompactUpper';a=select(join,name);assert Path(a['path']).parent==up;rows[name]={'join':a}
print(json.dumps({'status':'PASS','join_path':list(map(str,join)),'selections':rows,
 'scope':'current direct source-import first selections only; lower is a passed stage of a failed run; no full serialized/package or producer-time ancestry capture'},sort_keys=True,indent=2))
