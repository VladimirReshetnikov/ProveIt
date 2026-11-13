#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-constructor-ell-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-constructor-ell-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();n='Sign33ConstructorEll'
for f,h in {'state.json':'5b86f1052850fad9fea548dfcf11cdbc814b273edf4c9b63fe648e175d1de5df',n+'-compile.txt':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855','outer-observation.json':'b8a7419437c981c092425632f3530bce515d429c7fcab696eb73e7a53b6d7430'}.items():assert sha(a/f)==h
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(3811,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1195;r=s['rows'][0]
assert r['module']==n and r['source_sha256']=='5b53d2dc7b13f93019c618e6584c427b36f7792f98c94e0a123ba38d1cb7770c' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase,code in [('deps',0),('compile',-15)]:
 x=r[phase];assert x['exit']==code and x['stop_reason']==('timeout' if phase=='compile' else None) and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert log==''
assert r['compile']['elapsed_seconds']==120.206 and r['compile']['peak_session_rss_bytes']==2178195456 and r['compile']['samples']==1138
for mod,h in {'DiophantineConsistency.Sign33ReferenceEll':'0bc514b3781c16434a3360dd905fa32b0711491713f5b234f0dff0c482e9696d','DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f','DiophantineConsistency.Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','DiophantineConsistency.Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':h}
assert len(r['direct_guard'])==300
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':3811,'lean_exit':-15,'scope':'monitor timeout with unknown cause; no theorem; no Lean replay','guard_slots':300,'overlay_links':1195},indent=2,sort_keys=True))
