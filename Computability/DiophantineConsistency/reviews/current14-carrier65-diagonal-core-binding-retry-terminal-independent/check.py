#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-diagonal-core-binding-retry-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==16476 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS'
for f in ('current14-carrier65-diagonal-core-retry-terminal-independent','current14-carrier65-diagonal-binding-terminal-independent','current14-carrier65-diagonal-core-binding-failure-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
es=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(es)==len(s['rows'])==2
for i,(e,r) in enumerate(zip(es,s['rows'])):
 n=e['module'].split('.')[-1];assert n==r['module'] and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 for mod in e['imports']:
  d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
  if mod.endswith('DiagonalCore'):assert d['sha256']==s['rows'][0]['object_sha256']
  if mod.endswith('DiagonalBinding'):
   prior=json.loads((root/'research/current14-carrier65-diagonal-binding-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][0]['object_sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target

for n in ('Current14Carrier65DiagonalCore','Current14Carrier65DiagonalCoreBinding'):
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(n+'.'+z+'_degree' in log for z in ('c','a','H','delta')) and log.count('[propext, Classical.choice, Quot.sound]')==4 and 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':16476,'scope':'actual all-equal axis c/a/H/delta degrees 5/6/6/12 under p0 nonzero; whole polynomial separate'},indent=2))
