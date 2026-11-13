#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-p-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-p-retry01-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();n='Sign33ForwardNormP'
for f,h in {'state.json':'99e21c0f27a5640f0968a60b9f6e86dd8818413f5af0c90f77a0bc578401c4e3',n+'-compile.txt':'2a1d806a2f43823ab0410f9e3992d2d0836c883b4d15e636bf5a8e6940d4fdad','outer-observation.json':'27f39b2e8b0049d521f5da4ef36ce7ccafe04744ebbe8f1cbf7e37998c9d4c51'}.items():assert sha(a/f)==h
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(19944,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1200;r=s['rows'][0]
assert r['module']==n and r['source_sha256']=='fccbcedbe2384a7957070704048ccc9f19dff2a414ac42a9c5329956e2a78166' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase,code in [('deps',0),('compile',1)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'Type mismatch' in log and 'ι (u j) + 1' in log and 'sorryAx' in log
assert r['compile']['elapsed_seconds']==5.793 and r['compile']['peak_session_rss_bytes']==2180296704 and r['compile']['samples']==55
for mod,h in {'DiophantineConsistency.Sign33ConstructorEllRetry':'be7375726277bf550e39cfd39b20955b120c6febd748362e1a269c46072ad830'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':h}
assert len(r['direct_guard'])==100
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':19944,'lean_exit':1,'scope':'type mismatch in tau cast-shift; no theorem; no Lean replay','guard_slots':100,'overlay_links':1200},indent=2,sort_keys=True))
