#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-value-negative-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-value-negative-retry01-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'6a0a5b963330ade28c199869910227980747a6f8f7b16420242de5744d6141bb','Sign33ForwardValueNegative-compile.txt':'b6d1909610958e003b8ecd02788c696c022afc6a41a04ecfaf19c32e2ad6d299','outer-observation.json':'f5a93c3f7876692fca99d3c4b950b2dfd20746cac386260e2eb4af79c814564b'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(96310,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardValueNegative' and r['source_sha256']=='66d8a782a4dc98ef16d55e5d5e7a43400c6b91f1a0dc27aae480ce6a2a383ba1' and r['object_sha256']=='df7966db6beb033d7ad87887c142297f6412a2d923d3f7b8c5d104402539c5df'
assert h(p/'src/DiophantineConsistency/Sign33ForwardValueNegative.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardValueNegative.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardValueNegative-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardValueNegative-compile.txt').read_text();assert log.count('warning:')==8 and 'error:' not in log and 'sorryAx' not in log
for t in ('value_of_core','negative_of_core'):assert re.search(r"'DiophantineConsistency\.Sign33ForwardValueNegative\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':96310,'direct_guard_slots':200,'overlay_links':1194,'scope':'conditional forward value/negative cuts only; no Lean replay'},sort_keys=True,indent=2))
