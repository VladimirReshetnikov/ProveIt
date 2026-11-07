#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-static-node30-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-static-node30-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'c1e7cabe5281270ce4d094989938ad9dee3897f11fa1426787cad078b3b3a86f','Sign33StaticNode30-compile.txt':'cbd48e2abc74153318f0c5620ab69e3a608739faff1caae9d9974f77978c9e89','outer-observation.json':'cdd411cc0245c4ea113e266d96ab8ff28dd93b93ee3a5a663014cc41f8ec85d7'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(90897,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33StaticNode30' and r['source_sha256']=='67a323664b3090f05212d9b2fe9842de4371bdd9dee8883e0cf9a9c088f09f2f' and r['object_sha256']=='8d150d69ce5e2e75fa7e4722bda965d746678ebb1f5eca50a546332e8d3c974c'
assert h(p/'src/DiophantineConsistency/Sign33StaticNode30.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33StaticNode30.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33StaticNode30-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33StaticNode30-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('node30',):assert re.search(r"'DiophantineConsistency\.Sign33StaticNode30\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':90897,'direct_guard_slots':100,'overlay_links':1194,'scope':'conditional static and reference value at node30; no Lean replay'},sort_keys=True,indent=2))
