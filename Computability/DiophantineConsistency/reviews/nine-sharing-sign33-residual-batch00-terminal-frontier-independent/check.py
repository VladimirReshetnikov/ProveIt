#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch00-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch00-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'580b48eb8714eb4ee78ac24d87c4114fb0ce368ec1b625978480dd7be6f1f1a7','Sign33ResidualBatch00-compile.txt':'ea54636cbc78f0071f944541edfdc3a25500b0b808e05d84041e39bdf40d6ce6','outer-observation.json':'f50d7552035e925eae852c325b0d7e0c7fe7de384382f2a6d9b9eea900e04e2f'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(87174,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch00' and r['source_sha256']=='8b0ae5b586f534856b90b8de1afe334df3819e4cf676f3e693d358bd50463ece' and r['object_sha256']=='b50a018d85c5d6939cfc6025bcac5612d01b2e3c2570d3780725a708ebe92cc7'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch00.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch00.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch00-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch00-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('row1_eval','row2_eval','three_cuts_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch00\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for name,sha in {'SharingSign33Squares':'48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42','Sign33FirstCut':'65bdf051fa81c881099198b4b46e17f4cccb05e0c9e373e977c3502b0ff310ae'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+name];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':87174,'direct_guard_slots':150,'overlay_links':1174,'scope':'three same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
