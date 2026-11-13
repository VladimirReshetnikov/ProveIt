#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group02-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-group02-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'d1ec4a373141b7dd06a7be11975c66d395ceb4c8146e5da4562cb6bd2297c0bd','Sign33ForwardGroup02-compile.txt':'a35d9531a5559817451e89608e3817536d7edcd432b39caa31583f9edf10a257','outer-observation.json':'1d96f760f4b6927a69a5cb49052b02e380f927e275dc1fda5c2f9677392dc799'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(61899,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardGroup02' and r['source_sha256']=='0e03687df38ef9718cc142c2ba0df5fe0aff6f45a98fba4de8157af9de809c66' and r['object_sha256']=='17586f6302f4986996edb54f85eb8aad51990a57941aa09b2d2bd56b5d537540'
assert h(p/'src/DiophantineConsistency/Sign33ForwardGroup02.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardGroup02.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardGroup02-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardGroup02-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('constructor_cuts',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardGroup02\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':61899,'direct_guard_slots':150,'overlay_links':1194,'scope':'third three forward cut equations only; no Lean replay'},sort_keys=True,indent=2))
