#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign16-v-lift-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign16-v-lift-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==89542 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign16VLift')" and s['runner_sha256']==sha(packet/'run.py')=='c277b896d6dfbda52b4c43af47acb9ea87964b1087e8503b4f5f26647039f8a7';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign16VLift';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',1)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert log.count('error:')==1 and log.count('warning:')==0 and 'nonneg_iff.mp' in log and 'sorryAx' in log and 'exists_v_of_seed' in log and not (out/'lib/DiophantineConsistency'/(name+'.olean')).exists() and 'object_sha256' not in row
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign16WindowAssembly','4cf8424258ec09609cba9fa8bc435a2d60663c0db777d45a242fd8b9dee20a44'),('Sign33InnerVRing','bb4c20461196accbd1e3e3914f9ab6637f2142f5366150e29caf3b037d3371da')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':89542,'outer_exit':1,'compile_exit':1,'errors':1,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'V representative proof failed on reversed equality and sorryAx; no object/postflight'},indent=2,sort_keys=True))
