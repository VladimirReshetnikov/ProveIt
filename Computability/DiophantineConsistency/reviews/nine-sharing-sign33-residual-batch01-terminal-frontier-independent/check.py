#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch01-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'6170430d297f93910f6ea89f35d0994308ea9968f8d25f903d990519859e4773','Sign33ResidualBatch01-compile.txt':'5296fd1184a5695f4c750acbc93c8f9b4ecd5c58adc2ff4bb724c254dbacaba1','outer-observation.json':'e9c11c4b0424716adae6964e264ac85545be560a0ec401ee0ee8ae6ad560a302'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(23045,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch01' and r['source_sha256']=='c5a5b2664f56d3b07307dd9e55155feda19e793f76cd3ecdd4ec02feb7e5d8f5' and r['object_sha256']=='de360ead8b07e8b770029067431decacd8323e56d1b4870b5b1333ed077c1f5b'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch01.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch01.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch01-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch01-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('row3_eval','row4_eval','row5_eval','three_cuts_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch01\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':23045,'direct_guard_slots':100,'overlay_links':1174,'scope':'three same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
