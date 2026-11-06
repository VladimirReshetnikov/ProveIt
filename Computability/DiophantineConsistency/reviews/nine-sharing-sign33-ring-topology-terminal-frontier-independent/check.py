#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-topology-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-topology-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'91774b1327ec3ec0e5c86d2b8a8183fb0e18afc72a4a6a0cc89cadf991b266e4','Sign33RingTopology-compile.txt':'093eff2f521b8bbf4e226a7a0c5ddfd0c2723fbeb573f00296cf06c0d021903a','outer-observation.json':'c4da6c8de0cff8f6561136f3d54ed7ccb77c61943c791c82c0c68df266dc1013'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(89578,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingTopology' and r['source_sha256']=='74fc4a3c1c2302d3c35a23239f286cb991d3a64e823694299bae214474e2dc3f' and r['object_sha256']=='12541ed2f43c8fa4e2bee94b089ef7f74802fe15cf253809b6e659bde73365b5'
assert h(p/'src/DiophantineConsistency/Sign33RingTopology.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingTopology.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingTopology-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingTopology-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33RingTopology.static_agrees_of_topological' depends on axioms: [propext]" in log
dep=r['dependencies']['DiophantineConsistency.SharingTopology38'];assert dep['sha256']=='90661b7bf1e7be709ad2d32e67447e6e05a3d698c975a3e5632566b91fdcca38' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1192
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':89578,'direct_guard_slots':100,'overlay_links':1192,'axioms':['propext'],'scope':'conditional generic ring topology; no Lean replay'},sort_keys=True,indent=2))
