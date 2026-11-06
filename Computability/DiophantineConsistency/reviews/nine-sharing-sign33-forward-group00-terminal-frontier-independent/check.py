#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group00-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-group00-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'670a12d60b02d3c6e9e2021ee9661e5edf5fefd3c09d96c4b9d1758b48804acd','Sign33ForwardGroup00-compile.txt':'46002e76b8c4686fee000371f4c3f8dd88bb76afa85e589592331f346c4b18b1','outer-observation.json':'2fe8be7ca9ca690445758e5ab828d1f728039f1abd65ab1cb480ac51581ca2f3'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(61078,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardGroup00' and r['source_sha256']=='fa537a7a95c379533bc2e316fde45665679066eae7c07c69a799fffef4483248' and r['object_sha256']=='74257d5b86784d8674d052c40fead9afe6f90a45d372b0d6219f75442a59a9cc'
assert h(p/'src/DiophantineConsistency/Sign33ForwardGroup00.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardGroup00.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardGroup00-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardGroup00-compile.txt').read_text();assert log.count('warning:')==5 and 'simp argument is unused:' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('constructor_cuts',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardGroup00\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':61078,'direct_guard_slots':150,'overlay_links':1194,'scope':'first three forward cut equations only; no Lean replay'},sort_keys=True,indent=2))
