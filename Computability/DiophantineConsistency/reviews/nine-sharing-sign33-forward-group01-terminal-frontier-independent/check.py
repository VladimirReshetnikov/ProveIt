#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-group01-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'d3aedeb8261f059ff714def42a7dc56dedf1630c29b9d145832ee7b83ddbe7d2','Sign33ForwardGroup01-compile.txt':'41dbedda3c62a7ebbfd62ee277d21ddba6fb0f5ddff5921891951b6d783d0f23','outer-observation.json':'e5ddaed871dcbfb713ce70b59b2c1cb49281b2d3b28ecf93e0eb31c5c0b80eb3'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(25653,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardGroup01' and r['source_sha256']=='baddb6b73d4f98ef664c2a5bd91937ef659740a5ddd8e6056c32f003651a600e' and r['object_sha256']=='a4f6e2fc5d46f70f3cd6c4e3c0c4a154c7e1592117fcfdae799a2f1d72838542'
assert h(p/'src/DiophantineConsistency/Sign33ForwardGroup01.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardGroup01.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardGroup01-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardGroup01-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('constructor_cuts',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardGroup01\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':25653,'direct_guard_slots':150,'overlay_links':1194,'scope':'second three forward cut equations only; no Lean replay'},sort_keys=True,indent=2))
