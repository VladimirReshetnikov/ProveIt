#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-ranked-rawword-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-ranked-rawword-retry-20261110');base=Path('/tmp/nine-sharing-sign17-k-ranked-tile-sum-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==82177 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['manifest_sha256']==sha(p/'source-manifest.json')=='f02853edc208faf626f6934722df7bbc86a487a3db76006fba486b47b95d4890'
prov=root/'research/nine-sharing-sign17-k-ranked-tile-sum-retry-check/attempt01/state.json';assert sha(prov)==s['provider_state_sha256'];ps=json.loads(prov.read_text());providers={r['module']:r for r in ps['rows']};init=ps['rows'][0]['dependencies']['Init'];assert all(r['dependencies']['Init']==init for r in ps['rows'])
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
expected={'Sign17KRankedRawWord.'+k for k in ('rawWord_ranked','K_ranked')}
assert len(reports)==2 and {a for a,b in reports}==expected and all(b in ('propext, Quot.sound','propext, Classical.choice, Quot.sound') for a,b in reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert sha(p/'run.py')=='b43b9ae175f9056316616e6f8c78790a6a9a183b8c79fb2e0e7e65788ae49ba3'
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':82177,'stages':1,'reports':len(reports),'warnings':0,'guard_entries':guards,'scope':'rawWord and K split into ranked tile/control/sentinel sums; coefficient/file binding separate; global ranking/K/file separate'},indent=2))
