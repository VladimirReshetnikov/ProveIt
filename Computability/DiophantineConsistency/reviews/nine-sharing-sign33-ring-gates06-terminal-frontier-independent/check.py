#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates06-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates06-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'9c9063672bfad1b72c3bfbfb7427b71cbebae3c11aa1d8764d7c716cb131f2ed','Sign33RingGates06-compile.txt':'e718549f83e1e73bb4aae51bbc82b053e5923788db74dcdee1d691a42d23d27f','outer-observation.json':'e15d4ed49d1070b78d3be5dec55ba5d70ecc04370646c031b90e5495b0519c41'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(32805,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates06' and r['source_sha256']=='8af4324714e056003d46d4d55d8282aa8e9f0b64c6f5a01edef3b915ff827913' and r['object_sha256']=='574b56c743e3b4f68c35c811caec821f3af49fc49a20a1838eb9687b26fe3691'
assert h(p/'src/DiophantineConsistency/Sign33RingGates06.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates06.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates06-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates06-compile.txt').read_text();assert log.count('warning:')==18 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate48','gate49','gate50','gate51','gate52','gate53'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates06\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':32805,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
