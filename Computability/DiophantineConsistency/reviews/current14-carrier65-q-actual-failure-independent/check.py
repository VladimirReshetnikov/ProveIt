#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-q-actual-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-q-actual-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==34247 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['exception']=="RuntimeError('compile failed Current14Carrier65QActual')"
for f in ('current14-carrier65-q-fields-terminal-independent','current14-carrier65-q-cancel-terminal-independent','current14-carrier65-q-degree-retry02-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
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
 for mod in e['imports']:
  d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
  if mod.endswith('QCancel'):assert d['sha256']==s['rows'][0]['object_sha256']
  if mod.endswith('QDegree'):assert d['sha256']==s['rows'][1]['object_sha256']
  if mod.endswith('QFields'):
   prior=json.loads((root/'research/current14-carrier65-q-fields-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][0]['object_sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/'Current14Carrier65QActual-compile.txt').read_text().split());assert log.count('error(lean.dependsOnNoncomputable)')==2 and all('QActual.'+z in log for z in ('values_degree','Q_degree_le')) and log.count('[propext, Classical.choice, Quot.sound]')==2 and 'sorryAx' not in log
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':34247,'scope':'two replay objects succeed; final noncomputable compilation failure has clean reports but no object'},indent=2))
