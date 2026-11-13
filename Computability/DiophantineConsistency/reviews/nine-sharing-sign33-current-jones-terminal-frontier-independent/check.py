#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-jones-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-jones-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'a70978bcae7aba18f3b472554763f7222fed54e34f129a65cb9d9183bed36294','SharingSeed33CurrentJones-compile.txt':'19dd8e210cc8b6eabd4bcac0919b13156ac72f1579156b19bb7b8409747ab627','outer-observation.json':'b88c34d95f218ae66e5d9beb57aca713dec9e5020839bc1608af474d90345fa8'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(48375,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='SharingSeed33CurrentJones' and r['source_sha256']=='f41fe843a3c5fb5a5410756d3ceeac26a1a2e4f9121053615a4b0543671da280' and r['object_sha256']=='062ef2b3adcab259480533ce7a0cac972952b840dd6a305f6eab04f40822e2f9'
assert h(p/'src/DiophantineConsistency/SharingSeed33CurrentJones.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/SharingSeed33CurrentJones.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('SharingSeed33CurrentJones-'+k+'.txt'))==x['log_sha256']
log=(a/'SharingSeed33CurrentJones-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('current_beta_positive','current_degree','current_normalized','current_nine_iff'):assert re.search(r"'DiophantineConsistency\.SharingSeed33CurrentJones\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingSeed33Degree':'4e315b2439ee1f8133cd358c3ff8031bad9b23efbaf3907ef35529c81c859527','DiophantineConsistency.SharingSeed33Normalize':'f4aac073a2cacfe0886b97e4b1894f02d1c64e3537ac2e1a9f141b4e5e517867','DiophantineConsistency.SharingSeed38CurrentJones':'9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1197
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':48375,'direct_guard_slots':200,'overlay_links':1197,'scope':'33 seed Jones nine-variable existential iff in IΣ₁ models; no Lean replay'},sort_keys=True,indent=2))
