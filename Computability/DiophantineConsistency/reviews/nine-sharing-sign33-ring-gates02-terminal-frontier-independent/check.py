#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates02-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates02-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'9dd055cf97426f28f7ad18f147c81656a4312dd1438389cd4f4c15d85ef76ae6','Sign33RingGates02-compile.txt':'f0513b8ec25fa89522d235ca2e5f219aaf50621d1b7c5d19be97856289e2395e','outer-observation.json':'5b08b0ee5febe8680be0fbb70ba2da0fa5ae5d2b2ce1fa3401f369cdc1da777a'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(57513,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates02' and r['source_sha256']=='c417b34168c5829933e9350f3a24f59d62c22310c2d8a4ef421d7d9e71b67e65' and r['object_sha256']=='d52d0bdf60296f93e73bd9d5fa0cd9c10ef744a22c3df41348e036a06a55933e'
assert h(p/'src/DiophantineConsistency/Sign33RingGates02.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates02.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates02-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates02-compile.txt').read_text();assert log.count('warning:')==1 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate27','gate28','gate29'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates02\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':57513,'direct_guard_slots':150,'overlay_links':1193,'scope':'three ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
