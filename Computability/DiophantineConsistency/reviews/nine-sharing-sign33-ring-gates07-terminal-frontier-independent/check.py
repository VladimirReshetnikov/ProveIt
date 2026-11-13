#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates07-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates07-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'1725ebece53a54243ce67dfe4637c1f47febcf84caae84c2c203373f82098902','Sign33RingGates07-compile.txt':'92674bd0e347e6ff966b6401b3b1e61b0352870d7ab7936b1ca02d2215b59870','outer-observation.json':'d9c5ae8f120c5fb6538d7916e314b1ccc30cd646203252584f3acf4354b1c061'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(37036,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates07' and r['source_sha256']=='1906127d0dbfebcf7a4fdf78f7087baa01d90f8e736a7304d903a8816e8af71d' and r['object_sha256']=='1a87f1c4181bef6b9f37234e6c7cb72dcbb26601bde887e8844d8cd53d70f615'
assert h(p/'src/DiophantineConsistency/Sign33RingGates07.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates07.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates07-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates07-compile.txt').read_text();assert log.count('warning:')==17 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate54','gate55','gate56','gate57','gate58','gate59'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates07\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':37036,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
