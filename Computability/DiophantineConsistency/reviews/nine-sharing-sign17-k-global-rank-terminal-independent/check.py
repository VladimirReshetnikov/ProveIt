#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-global-rank-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-global-rank-20261110');base=Path('/tmp/nine-sharing-sign17-k-weight-union942-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==99607 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and s['manifest_sha256']==sha(p/'source-manifest.json')=='51df379c79399f6bd1b16696d4ab3b15551d8e16657ed641748ab6f102356172' and sha(p/'run.py')=='4d31df1375651e0a8da7caf13954b64804e73b5348ab488bdaf476e84dc984a5'
prov=root/'research/nine-sharing-sign17-k-weight-union942-check/attempt01/state.json';assert sha(prov)==s['provider_state_sha256'];ps=json.loads(prov.read_text());providers={r['module']:r for r in ps['rows']};init=ps['rows'][0]['dependencies']['Init'];assert all(r['dependencies']['Init']==init for r in ps['rows']);pins={n:r['object_sha256'] for n,r in providers.items()};pins.update({'MFWangTiles942Permutation':'746ee3bbee5b45245056866af653077343b4613078b7251ec1abcca7566b4db8','WellFounded':'ca401b51912d529f98ac681a875d6932f2007191ba8fb0ad9d8c8a25c652be7c','Basic':'7f0e65d168054f0c977dea30e1268dab68b5754949fc814c8ed33ff9966238f5'})
rows=json.loads((p/'source-manifest.json').read_text())['rows'];guards=0;reports=[]
for r,e in zip(s['rows'],rows):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(out/name)==x['log_sha256'];
  if n=='Sign17KGlobalRankConditional':assert sha(a/name)==x['log_sha256']
 assert r['dependencies']['Init']==init and set(r['dependencies'])==set(e['imports'])|{'Init'}
 for mod in e['imports']:
  d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 log=(out/(n+'-compile.txt')).read_text();assert all(t not in log for t in ('error:','warning:','sorryAx'));reports+=re.findall(r"'DiophantineConsistency\.(\w+\.\w+)' depends on axioms: \[([^]]+)\]",' '.join(log.split()));pins[n]=r['object_sha256']
assert len(reports)>=5 and all(b in ('propext','propext, Quot.sound','propext, Classical.choice, Quot.sound') for a,b in reports);assert {'Sign17KGlobalRankConditional.actual_adjacent_of_numeric','Sign17KGlobalRankConditional.candidate_positions_if'}<=set(a for a,b in reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':99607,'stages':4,'reports':len(reports),'warnings':0,'guard_entries':guards,'scope':'physical rank conditional on explicit Start, global nonzero and numeric adjacency; no unconditional rank/K/file'},indent=2))
