#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch07-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch07-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'cb55da080e2fec69cb082e9deaa5d9e6f03dfbd106e9fa22107cc3626d7fd69c','Sign33ResidualBatch07-compile.txt':'0da5b65ee7a7a38260ce1dd706b8a38b0c329303a052f15a22d0293ee9d3b2ed','outer-observation.json':'e4fcdd810d47d3036793a9318cc50c0aab726a944364cbe8b1529fd34d1dc059'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(79102,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch07' and r['source_sha256']=='a885cf06bee543a48505664621cd553f2a30bd868aa563893c26f4b9c34af45d' and r['object_sha256']=='b31aafb38c8892ae24e459edc57b1a7cd32ea932392bc6733fecdc12a2e16c40'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch07.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch07.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch07-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch07-compile.txt').read_text();assert log.count('warning:')==3 and log.count('warning: This simp argument is unused:')==3 and 'error:' not in log and 'sorryAx' not in log
for t in ('row21_eval','row22_eval','row23_eval','cut_and_norms_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch07\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':79102,'direct_guard_slots':100,'overlay_links':1174,'warnings':3,'scope':'negative-orientation cut and two norms; no Lean replay'},sort_keys=True,indent=2))
