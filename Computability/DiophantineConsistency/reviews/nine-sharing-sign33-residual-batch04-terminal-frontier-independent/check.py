#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch04-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch04-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'c5bf9844cfb813dcabdcadde7438970c97d72bfd37d3081da668f0356a67fa67','Sign33ResidualBatch04-compile.txt':'044bafa25e351cfc8194171211037c86a6122ded0b4927c20969b6c68dd6c4b4','outer-observation.json':'a10c41011ea96a45979a76fd401340ba3f534ca0538b3adf52098aaacfc63288'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(65291,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch04' and r['source_sha256']=='2497af05c79a7c5c586b183bd58fca389728f8736f4ef39dc7524ce6c2d3d10a' and r['object_sha256']=='ebfab8778a83272454b7aa164b22e02d5aad1070dcab389001854a41d3adb829'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch04.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch04.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch04-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch04-compile.txt').read_text();assert log.count('warning:')==1 and 'warning: This simp argument is unused:' in log and 'error:' not in log and 'sorryAx' not in log
for t in ('row12_eval','row13_eval','row14_eval','signed_cuts_and_norm_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch04\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':65291,'direct_guard_slots':100,'overlay_links':1174,'warnings':1,'scope':'two signed cuts and one norm with casts; no Lean replay'},sort_keys=True,indent=2))
