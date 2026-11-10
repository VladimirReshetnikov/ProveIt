#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-stream-compare-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-stream-compare-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert json.loads((a/'outer-result.json').read_text())=={'outer_session':40062,'outer_exit_code':0} and sha(a/'state.json')==sha(out/'state.json')=='e61e8c7da4bfb9523627206909413722882bc8d598949760576542f087e026e7';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==8 and s['manifest_sha256']==sha(p/'source-manifest.json');entries=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-stream-explicit-check/attempt01/state.json').read_text());other=json.loads((root/'research/nine-sharing-sign17-k-byte-compose-retry-check/attempt01/state.json').read_text());assert prior['status']==other['status']=='PASS' and s['provider_overlap_count']==1188 and s['provider_state_sha256']==sha(root/'research/nine-sharing-sign17-k-stream-explicit-check/attempt01/state.json') and s['second_provider_state_sha256']==sha(root/'research/nine-sharing-sign17-k-byte-compose-retry-check/attempt01/state.json');providers={row['module']:row for row in prior['rows']+other['rows']}
for i,r in enumerate(s['rows']):
 n=f'Sign17KStreamCompare{i:02}';e=entries[i];assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];obj=out/'lib/DiophantineConsistency'/(n+'.olean');assert obj.is_file() and sha(obj)==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(x not in log for x in ('error:','warning:','sorryAx')) and log.count('does not depend on any axioms')==1 and f'{n}.chunk' in log
 for mod,d in r['dependencies'].items():
  if mod=='Init':continue
  name=mod.split('.')[-1];assert name in providers and d['sha256']==providers[name]['object_sha256'] and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':40062,'stages':8,'equalities':8,'scope':'eight bounded actual/fixture digit slice comparisons; whole-list assembly and external file linkage separate'},indent=2))
