#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates09-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates09-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'301a24b20177aa7a773acbc3f154284b3e00dc3cfc56b62857db6b47928a551c','Sign33RingGates09-compile.txt':'14ce204b0ed1eb8c78bbf6f6e30d5acc655cb6c06f856f67bc3ba94d26c5c045','outer-observation.json':'16a24c88235ee34166aaefaff9089b23954766999dd9258c180bad5d8b5c6cae'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(11832,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates09' and r['source_sha256']=='a86d7a81fec2a3334317e0aba3db6dab2cf727fc83c9bbbd4adab76dc32e28c9' and r['object_sha256']=='f0bbc07cc705a37b4313af09cb4c22d049496d2c11fa99b28e4d754ad606323b'
assert h(p/'src/DiophantineConsistency/Sign33RingGates09.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates09.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates09-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates09-compile.txt').read_text();assert log.count('warning:')==10 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate66','gate67','gate68','gate69','gate70','gate71'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates09\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':11832,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
