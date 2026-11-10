#!/usr/bin/env python3
"""Inspect sign18 failed coordinate attempt without Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign18-coordinate-retry01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign18-coordinate-retry01-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==75993 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256']
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign18Coordinate')" and s['runner_sha256']==sha(p/'run.py')=='7d1f5e098143ef1793dcd314f774ab20d5457d4798437b39ffc29adb2bea355a';r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign18Coordinate';assert r['module']==n and r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
for phase in ('deps','compile'):
 x=r[phase];assert x['exit']==(0 if phase=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];name=n+'-'+phase+'.txt';assert sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'SharingSign18Squares':'7bc43d3507686e928fcd5fc61f79ce8081ec587551aff97f59ec61a90e90e30c','SharingSign19Squares':'e41498f629b5f0a3f84e5294b500cae65da0d5661d22a56734df9ec1d34cade2'}
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=(a/(n+'-compile.txt')).read_text();assert log.count('error:')==2 and log.count('warning:')==0 and log.count('sorryAx')==1 and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists() and 'object_sha256' not in r
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':75993,'outer_exit':1,'guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'coordinate compile failed, no object or final postflight'},indent=2,sort_keys=True))
