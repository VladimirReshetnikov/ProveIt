#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-forward-all-cuts-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-forward-all-cuts-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'a2a847e5f153f20fc29faaf3b19ffe4c8730f99b608f42be21ac05c95f751109','Sign33CurrentForwardAllCuts-compile.txt':'ca523d721476350bad7bad2543c82ea1791ba1c3e02cbc8700ce1af7bfe02d4a','outer-observation.json':'a2e7fe8b7774c5e557b73ca39a9f689a22c95e62dfdc46c089c539b6d56640c4'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(96155,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentForwardAllCuts' and r['source_sha256']=='d8442a76e62ff2f2e2b8f806577d5b9f01a976da155971d27772c717ad5700c7' and r['object_sha256']=='f961b85eac605d4429adac9fd17684b9af10fd1ae90b8c8b4a8aa86f6bfd4223'
assert h(p/'src/DiophantineConsistency/Sign33CurrentForwardAllCuts.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentForwardAllCuts.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentForwardAllCuts-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentForwardAllCuts-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('source_has_all_cuts',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentForwardAllCuts\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33ForwardAllCuts':'c50b0dd8f83a448eeebbc441f36d903c316d764a8722590dfb51facfdae6b916','DiophantineConsistency.Sign33CurrentCoreCuts':'1f9a7c639979896a0fbdcc8213a6410c83062953c500a9f9beebd1fa1e75812b','DiophantineConsistency.Sign33CurrentNaturalCoreNorms':'07ddb5120d90585c4f86147aa3e8d388f5999356c2938ff8782513489f077c02'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1229
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':96155,'direct_guard_slots':200,'overlay_links':1229,'scope':'current natural source zero with port casts implies existential AllCuts; no Lean replay'},sort_keys=True,indent=2))
