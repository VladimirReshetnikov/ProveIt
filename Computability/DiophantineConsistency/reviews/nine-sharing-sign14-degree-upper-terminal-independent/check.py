#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-degree-upper-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-degree-upper-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==45953 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='e2ea07c58678851c104564609722c7dc092c11d026f7428de158ba23b6a7be97'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==len(s['rows'])==18;provider=json.loads((root/'research/nine-sharing-sign14-expression-eval-check/attempt01/state.json').read_text());pins={r['module']:r['object_sha256'] for r in provider['rows']};guards=0
for r,e in zip(s['rows'],rows):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 log=(a/(n+'-compile.txt')).read_text();assert all(x not in log for x in ('error:','warning:','sorryAx'));pins[n]=r['object_sha256']
log=' '.join((a/'Sign14DegreeCompose-compile.txt').read_text().split());assert all(t in log for t in ('seed_degree_le','expression_degree_le','expression_polynomial_degree_le','current_polynomial_degree_le')) and log.count('[propext, Classical.choice, Quot.sound]')==2 and log.count('[propext, Quot.sound]')==2
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':45953,'stages':18,'guard_entries':guards,'scope':'Fin14 arbitrary-port and current symbolic polynomial totalDegree ≤124; no lower or external binding'},indent=2))
