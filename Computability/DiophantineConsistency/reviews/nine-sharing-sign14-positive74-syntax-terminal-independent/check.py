#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-syntax-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-syntax-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();receipt=json.loads((a/'outer-result.json').read_text());assert receipt['author_observed_outer_session']==73299 and receipt['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==receipt['state_sha256']=='676839408f7a853da29301231420e17071e62d20fd9b33b4dfe11b52861d4180'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==10 and s['runner_sha256']==sha(p/'run.py');entries=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign14-86gate-expression-check/attempt01/state.json').read_text());assert prior['status']=='PASS';providers={row['module']:row for row in prior['rows']};built={};warnings=0
for i,r in enumerate(s['rows']):
 n=f'Sign14Positive74Nodes{i:02}' if i<9 else 'Sign14Positive74Expression';e=entries[i];assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==receipt['logs'][name]
 log=(a/(n+'-compile.txt')).read_text();warnings+=log.count('warning:');assert all(x not in log for x in ('error:','sorryAx','declaration uses sorry'))
 for mod,d in r['dependencies'].items():
  if mod=='Init':continue
  name=mod.split('.')[-1];assert name in providers or name in built;expected=(providers if name in providers else built)[name]['object_sha256'];assert d['sha256']==expected and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 built[n]=r
assert warnings==4
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':73299,'stages':10,'warnings':warnings,'scope':'positive-coordinate source syntax compilation only; no Lean transport or JSON/PDF binding'},indent=2))
