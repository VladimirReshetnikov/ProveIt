#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates08-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates08-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'901706f4ce0d840d81c6fb6bd4e9be81f0009130b3c7ec905e19f90dcb576c9b','Sign33RingGates08-compile.txt':'5074e9b1fb3bff7d4bc7a1cf7280c55ecb365067864647995c78113c91b3b0b9','outer-observation.json':'0102917be26436fa9081e4b87ba6ba744f845525d29da449ce1e8d3ae8d87ba4'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(74439,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates08' and r['source_sha256']=='ff6e1ca1ce6859441eb5de3d147292c6a88905dc8d50eba7e7ce39dd2856bcce' and r['object_sha256']=='a0727b0568d06c80d49238ab4a169cb988e87d39ed6c493f255c8aba56c37055'
assert h(p/'src/DiophantineConsistency/Sign33RingGates08.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates08.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates08-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates08-compile.txt').read_text();assert log.count('warning:')==17 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate60','gate61','gate62','gate63','gate64','gate65'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates08\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':74439,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
