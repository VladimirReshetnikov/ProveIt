#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-value-negative-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-value-negative-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();n='Sign33ForwardValueNegative'
for f,h in {'state.json':'0ff0b3b7d022958b2b9abe6ace52c90271c7a9ad2f3c6dbb5d72d9bd272a9791',n+'-compile.txt':'715fd834c83726d42783224ebae4388bdd409a2ae3a699d64c6871a88f552556','outer-observation.json':'4b039d428cb8ebb28da451e7de3fea11977d2f91c40d13cbbe8219b26842be58'}.items():assert sha(a/f)==h
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(82339,1);s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1194;r=s['rows'][0]
assert r['module']==n and r['source_sha256']=='07908bd4b4850700f5fda96103abddc45deb55f5804404b38e2c673debd97fe9' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and not r.get('object_sha256') and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase,code in [('deps',0),('compile',1)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(a/f'{n}-{phase}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert log.count('Application type mismatch')==2 and 'Fin.cons' in log and 'lean.synthInstanceFailed' in log and log.count('lean.unknownIdentifier')==2 and 'depends on axioms:' not in log
for mod,h in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':h}
assert len(r['direct_guard'])==200
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert not (a/'survey-after.json').exists()
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':82339,'lean_exit':1,'scope':'Fin.cons elaboration failure; no theorem; no Lean replay','guard_slots':200,'overlay_links':1194},indent=2,sort_keys=True))
