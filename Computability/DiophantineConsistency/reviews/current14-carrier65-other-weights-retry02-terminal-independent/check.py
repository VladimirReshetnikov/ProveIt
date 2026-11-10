#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-other-weights-retry02-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-other-weights-retry02-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==90300 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
for f in ('current14-carrier65-other-weights-failure-independent','current14-carrier65-other-weights-retry-failure-independent','current14-carrier65-q-inputs-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Current14Carrier65OtherWeights';assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
prior=json.loads((root/'research/current14-carrier65-dag-value-congr-diagnostic-check/attempt01/state.json').read_text());assert prior['status']=='PASS' and 'Init' in r['dependencies']
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
 if mod.endswith('QInputs'):
  old=json.loads((root/'research/current14-carrier65-q-inputs-retry-check/attempt01/state.json').read_text());assert d['sha256']==old['rows'][0]['object_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all('Current14Carrier65OtherWeights.'+z in log for z in ('delta_weight','P_weight','U_weight','W_weight','Z_weight')) and log.count('[propext]')==5 and log.count('[propext, Classical.choice, Quot.sound]')==0 and not any(x in log for x in ('warning:','error:','sorryAx'))
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':90300,'scope':'standalone non-Q syntax weights; actual factor degree separate'},indent=2))
