#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch02-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch02-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'e73c186d80a98879177d8867b9328406a50b0b10b5d200ec012046443ec20c98','Sign33ResidualBatch02-compile.txt':'840a8c845ac3638737db3005d07fab101370c78610527d3353cd8dde24c2f13d','outer-observation.json':'e3b43238e5571ad255da0fa8260fda7cb2388114ed445d4b7eceb550f08cecf2'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(31501,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch02' and r['source_sha256']=='dddf446dd66f4467cccc5fbe0fd46b57c54be9b4b7e663ebd94e5b15dfb6c5da' and r['object_sha256']=='bae92aa8c5fbb599205cd75c4848ff45d474188eee6f34e4b7e867589b4fe2b0'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch02.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch02.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch02-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch02-compile.txt').read_text();assert log.count('warning:')==5 and log.count('warning: This simp argument is unused:')==5 and 'error:' not in log and 'sorryAx' not in log
for t in ('row6_eval','row7_eval','row8_eval','three_cuts_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch02\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':31501,'direct_guard_slots':100,'overlay_links':1174,'warnings':5,'scope':'three same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
