#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates-assembly-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates-assembly-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'816e2b54bb19fb6c3fa32dc80f3ae724c90154f94a97fcdf51337caf52b15f09','Sign33RingGatesAssembly-compile.txt':'31ed239b5cfb8631c5d24cb3cb4dfb1e7640722e4dd23860943d3d8f166ef8f9','outer-observation.json':'b5e0ee9928e8cc9223d9afe7111bf6bb1f56a1494c2e83ab89e87d02ffea55b1'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(33843,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGatesAssembly' and r['source_sha256']=='b56a55e1e9759f0b0e2bf1f0119d5a272b54bfb2a35fb0a1761e5d391fe115c6' and r['object_sha256']=='f2a70591bb828df70f3b1a70bc93a927ed77e3f406af39577ec56aefa81e0d09'
assert h(p/'src/DiophantineConsistency/Sign33RingGatesAssembly.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGatesAssembly.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGatesAssembly-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGatesAssembly-compile.txt').read_text();assert log.count('warning:')==2 and 'simp argument is unused:' in log and 'forall_const' in log and 'and_true' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('all_ring_gates',):assert re.search(r"'DiophantineConsistency\.Sign33RingGatesAssembly\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for i in range(12):
 mod=f'Sign33RingGates{i:02d}';provider=d/f'research/nine-sharing-sign33-ring-gates{i:02d}-check/attempt01/state.json';state=json.loads(provider.read_text());assert state['status']=='PASS';row=state['rows'][0];assert row['module']==mod and row['compile']['exit']==0
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==row['object_sha256'] and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==650 and len(s['overlay_links'])==1205
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':33843,'direct_guard_slots':650,'overlay_links':1205,'scope':'60-gate conditional assembly; no Lean replay'},sort_keys=True,indent=2))
