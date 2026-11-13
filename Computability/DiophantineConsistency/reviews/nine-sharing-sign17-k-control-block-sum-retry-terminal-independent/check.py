#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-control-block-sum-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-control-block-sum-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==61467 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and s['manifest_sha256']==sha(p/'source-manifest.json')=='61e1e2f0843a98ec64e3f18405271baddaebcc68720f7e71c837b7040768f03a' and sha(p/'run.py')=='6355556b3dab5d032064ff949ad7444c3958042e235e2d3b48498f7af5ae424b'
prov=root/'research/nine-sharing-sign17-k-ranked-rawword-retry-check/attempt01/state.json';assert sha(prov)==s['provider_state_sha256'];ps=json.loads(prov.read_text());pins={r['module']:r['object_sha256'] for r in ps['rows']};init=ps['rows'][0]['dependencies']['Init'];rows=json.loads((p/'source-manifest.json').read_text())['rows'];warnings=0;reports=[];guards=0
for i,(r,e) in enumerate(zip(s['rows'],rows)):
 n=r['module'];assert r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean')) and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(out/name)==x['log_sha256']
  if i==2:assert sha(a/name)==x['log_sha256']
 assert r['dependencies']['Init']==init and set(r['dependencies'])==set(e['imports'])|{'Init'}
 for mod in e['imports']:
  d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 log=(out/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log;warnings+=log.count('warning:');reports+=re.findall(r"'DiophantineConsistency\.(\w+\.\w+)' depends on axioms: \[([^]]+)\]",' '.join(log.split()));pins[n]=r['object_sha256']
assert warnings==1 and len(reports)==5 and all(b=='propext, Classical.choice, Quot.sound' for a,b in reports) and {'Sign17KControlBlockSum.symbolic_sum','Sign17KControlBlockSum.literal_sum_eq','Sign17KControlBlockSum.controls_as_sum'}<=set(a for a,b in reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':61467,'stages':3,'reports':len(reports),'warnings':warnings,'guards':guards,'scope':'actual symbolic control sum equals literal vector sum; external array/full K/file separate'},indent=2))
