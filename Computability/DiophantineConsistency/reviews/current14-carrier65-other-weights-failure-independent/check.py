#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-other-weights-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-other-weights-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==27337 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['exception']=="RuntimeError('compile failed Current14Carrier65OtherWeights')" and len(s['rows'])==1
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Current14Carrier65OtherWeights';assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(0 if ph=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
assert not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists() and 'object_sha256' not in r and 'Init' in r['dependencies']
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
 if mod.endswith('QInputs'):
  prior=json.loads((root/'research/current14-carrier65-q-inputs-retry-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][0]['object_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'maximum number of heartbeats (200000)' in log and log.count('sorryAx')==1 and all(z+'_weight' in log for z in ('delta','P','U','W','Z'))
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':27337,'scope':'U_weight hit 200000 heartbeats; reports in failed module, no object'},indent=2))
