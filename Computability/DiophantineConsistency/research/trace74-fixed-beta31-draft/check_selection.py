#!/usr/bin/env python3
"""Current direct provider selection only; no transitive closure capture."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent;parent=here.parent
parent_result=json.loads((parent/'trace74-n5-r7-graph-growth-draft-v2/observations/attempt01/terminal.json').read_text())
old=parent_result['lean_path'].split(':');join=old[1:]
beta_old=['/tmp/trace74-symbolic-fixed-mask-cover-x2i5dfft/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
def select(roots,name):
    for root in map(Path,roots):
        p=root/(name+'.olean')
        if p.is_symlink() and not p.exists():raise RuntimeError('dangling shadow: '+str(p))
        if p.is_file():return {'path':str(p),'target':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
    raise RuntimeError('missing '+name)
rows={}
for name,prior in [('Trace74Pell',old),('DiophantineConsistency/CompactFixedBeta',beta_old)]:
    a=select(prior,name);b=select(join,name)
    assert (a['target'],a['sha256'])==(b['target'],b['sha256'])
    rows[name]={'prior':a,'join':b}
print(json.dumps({'status':'PASS','join_path':join,'selections':rows,
 'scope':'current direct object first selections only; no full serialized/package or producer-time ancestry capture'},sort_keys=True,indent=2))
