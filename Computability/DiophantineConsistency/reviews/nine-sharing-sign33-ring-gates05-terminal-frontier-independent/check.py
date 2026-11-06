#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates05-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates05-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'803f5e148047dfdf156e92a114b7692e6b10ebbb6f03c0a47f9128e7ffcf6f6a','Sign33RingGates05-compile.txt':'cfae81331d1db650d018b5dcdea0bf8a7a6d728a1bb3beacaa46755fc704c126','outer-observation.json':'2ba0131bbb32e9027b6e15b8ca621b2a7bb8403ffd57f816b9baf6d07bc24adf'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(74209,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates05' and r['source_sha256']=='27c9b233f5ae2825bb4929a662b3383378943d996e23bcd9566195b5fd27e39a' and r['object_sha256']=='d0821a3c532c69e215a272adace97a8c44c68f9b1cb22459ae6f3ca3761d66c2'
assert h(p/'src/DiophantineConsistency/Sign33RingGates05.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates05.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates05-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates05-compile.txt').read_text();assert log.count('warning:')==15 and 'simp argument is unused:' in log and 'map_mul' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate42','gate43','gate44','gate45','gate46','gate47'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates05\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':74209,'direct_guard_slots':150,'overlay_links':1193,'scope':'six ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
