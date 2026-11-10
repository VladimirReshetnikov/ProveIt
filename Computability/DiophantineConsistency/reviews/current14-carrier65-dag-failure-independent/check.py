#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-dag-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-dag-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==79111 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['exception']=="RuntimeError('compile failed Current14Carrier65DAGValue')"
es=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(es)==len(s['rows'])==3
for i,(e,r) in enumerate(zip(es,s['rows'])):
 n=e['module'].split('.')[-1];assert n==r['module'] and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(1 if i==2 and ph=='compile' else 0) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
 obj=out/'lib/DiophantineConsistency'/(n+'.olean')
 if i<2:assert obj.is_file() and sha(obj)==r['object_sha256']
 else:assert not obj.exists() and 'object_sha256' not in r
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 assert 'Init' in r['dependencies']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
for i in (1,2):
 r=s['rows'][i]
 for mod in es[i]['imports']:
  dep=r['dependencies'][mod];assert Path(dep['path']).is_file() and str(Path(dep['path']).resolve())==dep['realpath'] and sha(Path(dep['path']))==dep['sha256']
  if mod.endswith('ArithmeticDAG'):assert dep['sha256']==s['rows'][0]['object_sha256']
  if mod.endswith('Current14Carrier65DAGCore'):assert dep['sha256']==s['rows'][1]['object_sha256']
  if mod.endswith('Carrier65'):assert dep['sha256']=='10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f'
core=' '.join((a/'Current14Carrier65DAGCore-compile.txt').read_text().split());assert all('Current14Carrier65DAG.'+n in core for n in ('topological','operation_count','addition_count','subtraction_count','multiplication_count','live_operation_count','all_inputs','all_ports')) and 'sorryAx' not in core and 'error:' not in core
v=(a/'Current14Carrier65DAGValue-compile.txt').read_text();assert 'error: unsolved goals' in v and '.getD' in v and 'sorryAx' in v and 'value_eq_carrier' in v
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':79111,'successful_stages':2,'failed_stage':'Current14Carrier65DAGValue','scope':'count/liveness of specified circuit only; semantic bridge failed'},indent=2))
