#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates03-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates03-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'752b84aa3aa3f04dfbff18bade27b2bfcb619e69aa1a1f5589a1c1f24796aa1c','Sign33RingGates03-compile.txt':'e7222f8c40e91f46b254b306a0b53d1bdd7a3e95b9e36b429398d401425c66ec','outer-observation.json':'45d9fb8048e32386339b20c5bda0c0bfbaa3bdacf334bdc1c2ccfb217571788e'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(49117,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates03' and r['source_sha256']=='f90cc7222e7e8eab85dec5f5d5e45a5030e39f1e9c316b522a4ce81302755a59' and r['object_sha256']=='1ab19a19a5a4bff5a5e7ced99e8eef16edbc12775443f124c3cfc07aefde182c'
assert h(p/'src/DiophantineConsistency/Sign33RingGates03.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates03.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates03-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates03-compile.txt').read_text();assert log.count('warning:')==5 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate30','gate31','gate32','gate33','gate34','gate35'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates03\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':49117,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
