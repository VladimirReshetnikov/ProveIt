#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-jones-source-iff-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-jones-source-iff-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'87f18e7aec2758fb2a4f04893255a9f4e3076f80e00efa1024d965378a3b3f72','Sign33CurrentJonesSourceIff-compile.txt':'f41878d6cdd6e815e9bb7cc272e6565dc3241f20eaf6c7a4b5471b88664c3362','outer-observation.json':'0b9c402adb4994120102bb334b1bb711c1a47833fd4ab8aad4ecb62f537fd83d'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(44724,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentJonesSourceIff' and r['source_sha256']=='0f17c0ee0d8758b70d0a3fd645a80a33748bf4c750b93fccc9acf0d176056721' and r['object_sha256']=='dc8f78ec59c2030ff3af9d3eb709bca470f7f86e76afad79fc1ba7f001434d34'
assert h(p/'src/DiophantineConsistency/Sign33CurrentJonesSourceIff.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentJonesSourceIff.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentJonesSourceIff-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentJonesSourceIff-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('nine_exists_iff_source',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentJonesSourceIff\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33CurrentSeedIff':'e4e6780fd199443f88f1b142f8eb284757c1293e3b0aa804c3d0f4d3af963670','DiophantineConsistency.SharingSeed33CurrentJones':'062ef2b3adcab259480533ce7a0cac972952b840dd6a305f6eab04f40822e2f9'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1265
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':44724,'direct_guard_slots':150,'overlay_links':1265,'scope':'symbolic nine Jones and current natural source existential iff in IΣ₁ models; no Lean replay'},sort_keys=True,indent=2))
