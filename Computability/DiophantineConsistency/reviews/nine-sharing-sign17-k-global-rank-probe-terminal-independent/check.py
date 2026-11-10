#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-global-rank-probe-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-global-rank-probe-20261110');base=Path('/tmp/nine-sharing-sign17-k-weight-union942-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==20939 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['manifest_sha256']==sha(p/'source-manifest.json')=='be11c383dccc8b922ab5d28479d9e6cddcdde9501f7dbd2c4753b182e75118c4'
prov=root/'research/nine-sharing-sign17-k-weight-union942-check/attempt01/state.json';assert sha(prov)==s['provider_state_sha256'];ps=json.loads(prov.read_text());providers={r['module']:r for r in ps['rows']};init=ps['rows'][0]['dependencies']['Init'];assert all(r['dependencies']['Init']==init for r in ps['rows'])
rows=json.loads((p/'source-manifest.json').read_text())['rows'];reports=[];guards=0
for r,e in zip(s['rows'],rows):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
 assert r['dependencies']['Init']==init and set(r['dependencies'])==set(e['imports'])|{'Init'}
 for mod in e['imports']:
  d=r['dependencies'][mod];pr=providers[mod.split('.')[-1]];assert d['sha256']==pr['object_sha256'] and d['realpath']==str((base/'lib/DiophantineConsistency'/(mod.split('.')[-1]+'.olean')).resolve()) and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 log=(a/(n+'-compile.txt')).read_text();assert all(t not in log for t in ('error:','warning:','sorryAx'));reports+=re.findall(r"'DiophantineConsistency\.(\w+\.\w+)' depends on axioms: \[([^]]+)\]",' '.join(log.split()))
expected={'Sign17KGlobalRankProbe.'+k for k in ('start_index','first_nonzero','first_adjacent')}
assert len(reports)==3 and {a for a,b in reports}==expected and all(b in ('propext, Quot.sound','propext, Classical.choice, Quot.sound') for a,b in reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(p/'run.py')=='8b53194941037c264738b948c6925b652eafc23fbf493b779a4117bcdbd6c3ff'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':20939,'stages':1,'reports':len(reports),'warnings':0,'guard_entries':guards,'scope':'Start and first sixteen candidate nonzero and numeric adjacency cases; global ranking/K/file separate'},indent=2))
