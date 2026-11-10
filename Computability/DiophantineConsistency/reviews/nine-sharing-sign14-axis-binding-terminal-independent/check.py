#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-axis-binding-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-axis-binding-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==70574 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and s['runner_sha256']==sha(p/'run.py')=='1243c4a1bb04e08e88ffa8d40e1864c0c761901d58f0998bc2f3fa76d97c4b37'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];pins={'Sign14AxisGenericDegree':'60d61cd2b2c5d90b7df6d170dcdc6f3b39dd9ea37c4edd14ab46f502114cbc98','Sign14DegreeCompose':'6f64deb7230882856d675da39cc82662a11f93a85f535c996ced2e96d28d378a'};warnings=0
for r,e in zip(s['rows'],rows):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 log=(a/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log;warnings+=log.count('warning:');pins[n]=r['object_sha256']
assert warnings==10
for n,th in [('Sign14AxisBindingBase',['shared07_axis']),('Sign14AxisBindingFactors',['shared31_axis','shared28_axis']),('Sign14AxisBindingRoot',['shared38_axis','shared42_axis'])]:
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(t in log for t in th) and log.count('[propext, Classical.choice, Quot.sound]')==len(th)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':70574,'stages':3,'warnings':warnings,'scope':'five actual staged root/scale axis bindings; lower/external binding separate'},indent=2))
