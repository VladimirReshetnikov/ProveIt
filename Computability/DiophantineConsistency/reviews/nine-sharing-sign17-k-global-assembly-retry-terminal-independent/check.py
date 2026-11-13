#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-global-assembly-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-global-assembly-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==54087 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==5 and s['exception']=="RuntimeError('compile failed Sign17KGlobalAssembly')" and s['manifest_sha256']==sha(p/'source-manifest.json')=='d842f3a270a12b7826115e813ffef98c294a5599082f9b54ca33855dfd977a13' and sha(p/'run.py')=='48128671a535948958b995ca728843944316bbc186c01afbbfe8504e531cdb06'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];guards=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];assert r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(1 if i==4 and ph=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(out/name)==x['log_sha256']
  if i==4:assert sha(a/name)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 obj=out/'lib/DiophantineConsistency'/(n+'.olean')
 if i<4:assert r['object_sha256']==sha(obj) and 'sorryAx' not in (out/(n+'-compile.txt')).read_text()
 else:assert not obj.exists() and 'object_sha256' not in r
log=(a/'Sign17KGlobalAssembly-compile.txt').read_text();assert log.count('error: Type mismatch')==2 and 'Sign17KGlobalChunk00.nonzero x0' in log and 'Sign17KGlobalChunk00.adjacent x0' in log and 'Fin.castLE' in log and 'sorryAx' in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':54087,'outer_exit':1,'successful_stages':4,'guard_entries':guards,'scope':'global rank assembly two chunk00 Fin.castLE mismatches, sorryAx, no final object/postflight'},indent=2))
