#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-p-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-p-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();n='Sign33ForwardNormPEll'
for f,h in {'state.json':'8afc4390ae5c85d26671afdfc25ae0239e14a4ac8e335a5cfe4c4d234c0f6a59',n+'-compile.txt':'48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a','outer-observation.json':'09cfd90d80d8881f1e5e19c2ae9b2f098a9547af19886dc7d216032c32106300'}.items():assert sha(a/f)==h
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(99769,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1194;r=s['rows'][0]
assert r['module']==n and r['source_sha256']=='af8221a7514d2d1647170b7f1cc2aee1b9e7a271a520983b73135ad4224596b8' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase,code in [('deps',0),('compile',-6)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'lean::memory_exception' in log and "'interpreter'" in log and 'depends on axioms:' not in log
assert r['compile']['elapsed_seconds']==5.752 and r['compile']['peak_session_rss_bytes']==2938245120 and r['compile']['samples']==55
for mod,h in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':h}
assert len(r['direct_guard'])==200
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':99769,'lean_exit':-6,'scope':'Lean interpreter memory exception; no theorem; no Lean replay','guard_slots':200,'overlay_links':1194},indent=2,sort_keys=True))
