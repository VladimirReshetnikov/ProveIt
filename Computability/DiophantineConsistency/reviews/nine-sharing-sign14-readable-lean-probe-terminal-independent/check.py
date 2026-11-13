#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-readable-lean-probe-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-readable-lean-probe-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==59353 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign14ReadableLow')" and len(s['rows'])==2 and s['runner_sha256']==sha(p/'run.py')=='c55a15c78cc13c7eb3fc21b29dc2945b2e2478f14c6b332f47735c3a6d59924c';rows=json.loads((p/'source-manifest.json').read_text())['rows']
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];assert r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(1 if i==1 and ph=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 obj=out/'lib/DiophantineConsistency'/(n+'.olean')
 if i==0:assert r['object_sha256']==sha(obj)
 else:assert not obj.exists() and 'object_sha256' not in r
log=(a/'Sign14ReadableLow-compile.txt').read_text();assert 'error: unsolved goals' in log and 'Expr.evalRing v 1' in log and 'sorryAx' in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':59353,'successful_definition_stages':1,'scope':'low identity leaves Expr.evalRing v 1; no low object/postflight'},indent=2))
