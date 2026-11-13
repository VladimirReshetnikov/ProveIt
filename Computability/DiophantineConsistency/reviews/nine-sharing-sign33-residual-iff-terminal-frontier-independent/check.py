#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-iff-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-iff-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'675b8c15e4f4e084ba650bc49590384612292c45b1f2cbc345a72e5ae399a36b','Sign33ResidualIff-compile.txt':'a8ec3fe5cbafafcd041b798b7051934df975e0f742346110b597f255d997af47','outer-observation.json':'3a8ea98e42282d78f0c4683a769e0e93b94997605290bf72cf4175371c5a16cf'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(67314,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualIff' and r['source_sha256']=='0a18244fdc58e0859cac5b9f1a8d3a74db3582af897942b6a8da8de6d16c3456' and r['object_sha256']=='33eb8b457ea09983d4591856171a37bd8e625dd4cf2d712dbcd621290b5fe204'
assert h(p/'src/DiophantineConsistency/Sign33ResidualIff.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualIff.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualIff-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualIff-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log and re.search(r"'DiophantineConsistency\.Sign33ResidualIff\.seed_zero_iff_all_cuts' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8','Sign33ResidualConverse':'b8ca561a903d941caadfc8cdd1dd05d7ba25f746e87a1e05b6cb26ce412d2272'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1192
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':67314,'direct_guard_slots':150,'overlay_links':1192,'scope':'same-valuation seed/AllCuts iff with four casts; no Lean replay'},sort_keys=True,indent=2))
