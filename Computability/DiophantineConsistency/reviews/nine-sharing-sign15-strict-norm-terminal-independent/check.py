#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign15-strict-norm-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign15-strict-norm-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==82810 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='4b25095fce3c42e9d88eab0db910b6f87184eb927bc395123d47352e1380c235';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign15StrictNorm';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert 'error:' not in log and log.count('warning:')==1 and 'sorryAx' not in log and 'strict_of_seed' in log and '[propext, Classical.choice, Quot.sound]' in ' '.join(log.split()) and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='24211fc953daa52ccb029926fc598666eb1b6f5726fe6e082b362545ef0fe7e2'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign15MainNorm','f719babed11e9cbc15e112a8ad09514f271164df6005efa309cc6f405d004f10'),('Sign16StrictFactor','0919cfd8ae74c736dce44a0a1cbef10cba010ac75ec842b184816d3af849eed1')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':82810,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'strict norm from seed zero and represented beta; natural V lift separate'},indent=2,sort_keys=True))
