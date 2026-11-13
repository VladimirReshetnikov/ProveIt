#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch03-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch03-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'5162fbb298874db8f114ee3bd5b2c18756690f86272f6ff0ef6d48db3551d599','Sign33ResidualBatch03-compile.txt':'f805067547b2991ce61c52d5459a1dc0c9eae9e43abd086b77996f80e5413994','outer-observation.json':'86b606b68e56e866fa471327b9f1abbc5712c6da6338498a36b7e7e92399b8b5'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(56254,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch03' and r['source_sha256']=='0ddc9592dd0c3a66fa0d62485479246928ec7d9f778306a58ad206d7bf3d9ad6' and r['object_sha256']=='63cd9e3752c33243326e16f99015e247b2f15f223ca740c74d0fc17ab6bc59c5'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch03.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch03.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch03-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch03-compile.txt').read_text();assert log.count('warning:')==3 and log.count('warning: This simp argument is unused:')==3 and 'error:' not in log and 'sorryAx' not in log
for t in ('row9_eval','row10_eval','row11_eval','two_cuts_and_norm_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch03\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':56254,'direct_guard_slots':100,'overlay_links':1174,'warnings':3,'scope':'two same-valuation cuts and one norm; no Lean replay'},sort_keys=True,indent=2))
