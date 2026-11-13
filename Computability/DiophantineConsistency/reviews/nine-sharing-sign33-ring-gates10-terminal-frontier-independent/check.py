#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates10-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates10-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'fb5a9c7b3a9bc1ec634e0b017bbcc8933d7551098fc35bdc01408332df94273b','Sign33RingGates10-compile.txt':'9c8924a27a46a7a61d47310e63d72429f27568e01d9255407e5dd3896d6b6382','outer-observation.json':'16830e7135b7540ed1249ee1a1b2ba4d867113253ade621fe1fc53cac6085a78'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(26780,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates10' and r['source_sha256']=='654ac31a6b1567e70ba076049caae3e7bea28e5a427fcbb492b696dfd10fdd20' and r['object_sha256']=='be57c50ad87a44737ddc9573f20c0cc7a8b2fc4466ef4d9a4a50627b58a37ce7'
assert h(p/'src/DiophantineConsistency/Sign33RingGates10.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates10.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates10-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates10-compile.txt').read_text();assert log.count('warning:')==12 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate72','gate73','gate74','gate75','gate76','gate77'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates10\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':26780,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
