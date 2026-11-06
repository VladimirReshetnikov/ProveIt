#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates11-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates11-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'d38536175d16604eff873910d5985f952f0ff53c899cd14860b7a424633304b8','Sign33RingGates11-compile.txt':'b392959c361dfc7946d87b9c2fa3d15b3d9aa3b07b68b301114c48a972c3ff92','outer-observation.json':'f6d80cc1d3cec2d6ae2ddcd75d809e6e712991b910908898977c95883918717c'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(71006,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates11' and r['source_sha256']=='89f295708e83fbd98d80b7c0e37cfb00ee8a9ac74313aff2c5f5472e96f6c631' and r['object_sha256']=='8cf05f65584725d62c9222bf6856c5f2a08ace766dcf4a9a0fe113e5bba16240'
assert h(p/'src/DiophantineConsistency/Sign33RingGates11.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates11.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates11-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates11-compile.txt').read_text();assert log.count('warning:')==10 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate78','gate79','gate80'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates11\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':71006,'direct_guard_slots':150,'overlay_links':1193,'scope':'three ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
