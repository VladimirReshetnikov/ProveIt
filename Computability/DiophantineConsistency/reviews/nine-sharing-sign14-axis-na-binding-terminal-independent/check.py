#!/usr/bin/env python3
"""Audit failed generic sign15 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign14-axis-na-binding-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign14-axis-na-binding-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==35252 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='82befa93b86a47947627f8b04724cb1d0e09aa23d052ee9337e7b3993e6651b0';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign14AxisNaBinding';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(t in log for t in ('error:','sorryAx')) and log.count('warning:')==2 and all(t in log for t in ('row03_axis','row03_axis_degree')) and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==2 and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='d4cbe8458003e56641e5fb60760f12ae07bd4473dc2bd2d025b49b2b8a21c49d'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign14AxisInnerBinding','a360a8e2433a7822fbc3acdb0bae2c012e8add64e8675cea31c2eee6c7a98326'),('Sign14AxisGenericNaDegree','1f8361e6c38f13eda5ef393f695dd6547d2044a8650fe74139b91f41859a66e4')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':35252,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'actual staged Na row axis degree 62 under p0 nonzero; seed lower separate'},indent=2,sort_keys=True))
