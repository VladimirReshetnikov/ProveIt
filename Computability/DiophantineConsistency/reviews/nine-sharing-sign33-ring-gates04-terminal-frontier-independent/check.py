#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates04-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates04-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'8d4c24f479dd9166d8985c9b1f3dbafeb6a3156739ce21f27f06433f689de79a','Sign33RingGates04-compile.txt':'1046d1db359fffbcd846ed5539a33511e5352ee23d28d2a10630b7708c2c1dc9','outer-observation.json':'950718ba00287e69e412a312dad3a6c8b97ca5c2bd22d6070226b2f5515286dd'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(86431,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates04' and r['source_sha256']=='9bfb26008806fb305d244c8b6482dde299f195b62997c0ae9fb502a6383dca4c' and r['object_sha256']=='a76c09da0b982c31a6ffc20240515dcede25b47cc35c5f8fdd1821705d1ac49a'
assert h(p/'src/DiophantineConsistency/Sign33RingGates04.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates04.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates04-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates04-compile.txt').read_text();assert log.count('warning:')==2 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate36','gate37','gate38','gate39','gate40','gate41'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates04\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':86431,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
