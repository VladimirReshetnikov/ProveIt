#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-negative-node76-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-negative-node76-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();n='Sign33NegativeNode76'
for f,h in {'state.json':'134a6c8fbd060e56b15e90b839d2efd48a273ab5cf6ad7174a3a306ff057bc3a',n+'-compile.txt':'462397c2c61b0f495a6a6a799711794610529285330b4017479f47feb6ba80d7','outer-observation.json':'4d7eca50add7129aece45c7268ef2b1c71a5527ab3f4ed331536e0cf44e886d7'}.items():assert sha(a/f)==h
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(26754,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1196;r=s['rows'][0]
assert r['module']==n and r['source_sha256']=='b3aabf0b9b2510dbbb4a18e8747f48700db68b60876252e2cf4c0974360d6637' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase,code in [('deps',0),('compile',1)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert '`dsimp` made no progress' in log and 'sorryAx' in log
assert r['compile']['elapsed_seconds']==3.533 and r['compile']['peak_session_rss_bytes']==2168762368 and r['compile']['samples']==34
for mod,h in {'DiophantineConsistency.Sign33StaticNode76':'7c622ce54abd71af4d2c1c38a8e9808605480ea023312f3b6ea799654a42579b','DiophantineConsistency.Sign33ReferenceNode76':'62b5b7e2edb65010dc4c4eba34aac7c6a362b6e7827129485f0dbd6458057b5c','DiophantineConsistency.Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','DiophantineConsistency.Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':h}
assert len(r['direct_guard'])==250
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':26754,'lean_exit':1,'scope':'dsimp made no progress; no theorem; no Lean replay','guard_slots':250,'overlay_links':1196},indent=2,sort_keys=True))
