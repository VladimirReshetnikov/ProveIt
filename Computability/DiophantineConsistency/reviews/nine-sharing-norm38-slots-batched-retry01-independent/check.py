#!/usr/bin/env python3
"""Review retry's precise source/runner delta and preceding failed evidence."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];a=D/'research/nine-sharing-norm38-slots-batched-draft';b=D/'research/nine-sharing-norm38-slots-batched-retry01';out=Path('/tmp/nine-sharing-norm38-slots-batched-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(b/'run.py')=='a5ab6e841ac6a2e0f82519ad5b273cd14c64871cd167597d174ebe13283094eb' and sha(b/'source-manifest.json')=='c9f2135eb1fb83e1ea9e004ee9dd87141aba51badcd4e0c8b361e3e954cfd6ec'
old=(a/'run.py').read_text();new=(b/'run.py').read_text();assert old.replace('/tmp/nine-sharing-norm38-slots-batched-20261105','/tmp/nine-sharing-norm38-slots-batched-retry01-20261105').replace('97c061c885b7be6495b1244713b31fea1ff0ac955b493e066eaa1139c8ab40ac','c9f2135eb1fb83e1ea9e004ee9dd87141aba51badcd4e0c8b361e3e954cfd6ec')==new
ma=json.loads((a/'source-manifest.json').read_text())['rows'];mb=json.loads((b/'source-manifest.json').read_text())['rows'];assert len(ma)==len(mb)==12
for x,y in zip(ma,mb):
 assert x['module']==y['module'] and x['imports']==y['imports'];n=x['module'].split('.')[-1];old=(a/'src/DiophantineConsistency'/(n+'.lean')).read_text();new=(b/'src/DiophantineConsistency'/(n+'.lean')).read_text()
 assert sha(b/'src/DiophantineConsistency'/(n+'.lean'))==y['source_sha256']
 if n in {f'Norm38Slots{i:02d}' for i in range(2,10)}:
  assert old.count('map_add, map_mul, h') in (2,3)
  assert old.replace('map_add, map_mul, h','map_add, map_mul, map_ofNat, h')==new
 else:assert old==new
state=a/'attempt01/state.json';assert sha(state)==sha(out/'state.json')=='a8ce8f12f4948c97b8a171e34c3c8c1f652ce03ec6d28251ae82555f6dc4b9f0';s=json.loads(state.read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38Slots02')" and len(s['rows'])==4
assert [r['module'] for r in s['rows']]==['Norm38SlotsBase','Norm38Slots00','Norm38Slots01','Norm38Slots02']
for i,r in enumerate(s['rows']):
 n=r['module'];assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None and r['compile']['stop_reason'] is None and r['compile']['exit']==(0 if i<3 else 1)
 for typ in ('deps','compile'):
  log=a/'attempt01'/(n+'-'+typ+'.txt');assert sha(log)==sha(out/(n+'-'+typ+'.txt'))==r[typ]['log_sha256']
 if i<3:assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 else:assert 'object_sha256' not in r
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
log=(a/'attempt01/Norm38Slots02-compile.txt').read_text();assert 'error: unsolved goals' in log and 'ι 3' in log and 'ι 4' in log
outer=json.loads((a/'attempt01/outer-terminal-author-record.json').read_text());assert outer['outer_session_id']==38247 and outer['outer_exit_code']==1 and 'not independently observed' in outer['observation_kind']
print(json.dumps({'status':'PASS_RETRY_DELTA_AND_PRIOR_EVIDENCE_ONLY','retry_runner_sha256':sha(b/'run.py'),'retry_manifest_sha256':sha(b/'source-manifest.json'),'prior_state_sha256':sha(state),'prior_outer_session_author_recorded':38247,'prior_compile_successes':3,'prior_failed_module':'Norm38Slots02','scope':'Source and retained prior evidence only; no retry Lean run or independently observed outer exit.'},indent=2,sort_keys=True))
