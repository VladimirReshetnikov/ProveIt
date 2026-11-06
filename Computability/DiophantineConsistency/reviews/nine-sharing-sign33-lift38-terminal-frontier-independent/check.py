#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-lift38-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-lift38-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'98e91e8236694a2e6531268547b2f6ef45cd0dec2213e06bdf535e2b27d8ebd0','Sign33Lift38-compile.txt':'76cbf2291f47b035ccc0f0a5fb3aba4a6085e56bdb0f6196681dc3432cfd03d5','outer-observation.json':'fb936de19d3e577441a60bf06274a7228ea8b739cfeba34c63f890742f82b10a'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(45574,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33Lift38' and r['source_sha256']=='fc0db4bb388bd6e044d6127ba3d0e8f5690c8420d07bf3a4cb9bfe7be59b0c87' and r['object_sha256']=='d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3'
assert h(p/'src/DiophantineConsistency/Sign33Lift38.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33Lift38.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33Lift38-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33Lift38-compile.txt').read_text();assert log.count('warning:')==2 and log.count('warning: automatically included section variable(s) unused')==2 and 'error:' not in log and 'sorryAx' not in log
for t in ('signed_values_of_all_cuts','lift_inputs','lift_signed_coordinates'):assert re.search(r"'DiophantineConsistency\.Sign33Lift38\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.Sign33ResidualAssembly'];assert dep['sha256']=='0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1192
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':45574,'direct_guard_slots':100,'overlay_links':1192,'warnings':2,'scope':'coordinate and signed-value lemmas only; no Lean replay'},sort_keys=True,indent=2))
