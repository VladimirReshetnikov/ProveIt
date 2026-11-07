#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-seed-iff-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-seed-iff-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'b522e615e253dc5f8d5b4f30a8f147578f060940e3e5b5c5dd78551ceb4cad87','Sign33CurrentSeedIff-compile.txt':'af0e7bf07da4151a452ac792f9c5cf4797950da64dbc207a970fb89be80d35dd','outer-observation.json':'c5b3b738f1ffa8f9890125294c55507659d7167b93b0c7a261c3162a3d1e6063'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(39473,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentSeedIff' and r['source_sha256']=='e1f8fe053dcb1d1cad7caa1f29ec21e0842060ad6d940501952b971acebf7b62' and r['object_sha256']=='e4e6780fd199443f88f1b142f8eb284757c1293e3b0aa804c3d0f4d3af963670'
assert h(p/'src/DiophantineConsistency/Sign33CurrentSeedIff.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentSeedIff.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentSeedIff-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentSeedIff-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('seed_exists_iff_source',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentSeedIff\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33CurrentSourceSeedCastFree':'796fd8b523c9ab3669d09ecf874f2bbe96318c56c90dea586d83e87b2cfd0d77','DiophantineConsistency.Sign33CurrentSeedSourceRetry':'0be588190cf45140471a6cca9c58a1246e50313fa81b9e80f1370ee1d94ea009'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1260
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':39473,'direct_guard_slots':150,'overlay_links':1260,'scope':'33 seed and current natural source existential iff in IΣ₁ models; no Lean replay'},sort_keys=True,indent=2))
