#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch06-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch06-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'38aab91c79cf582e9c8910eb4998dd6ce6bfa72ff729de468e1061c5b019dc8e','Sign33ResidualBatch06-compile.txt':'427fca3769c847832bca6855a1a64a15a3ecd7ffba975dacdee789effe9187ac','outer-observation.json':'84fb6660e11f091c05123c3f7e0ac52e9703ecc6a525102dbdaa903a7bd5d597'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(57740,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch06' and r['source_sha256']=='8224c869cf3ba236e16cdd8a070ced48a1e55426ecd5451b5b813fe96fe1239d' and r['object_sha256']=='3cf0a657954b0c53bb61c11e2a090069a63567f610826a0be23885b320ec2722'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch06.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch06.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch06-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch06-compile.txt').read_text();assert log.count('warning:')==3 and log.count('warning: This simp argument is unused:')==3 and 'error:' not in log and 'sorryAx' not in log
for t in ('row18_eval','row19_eval','row20_eval','three_cuts_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch06\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':57740,'direct_guard_slots':100,'overlay_links':1174,'warnings':3,'scope':'three same-valuation cuts; no Lean replay'},sort_keys=True,indent=2))
