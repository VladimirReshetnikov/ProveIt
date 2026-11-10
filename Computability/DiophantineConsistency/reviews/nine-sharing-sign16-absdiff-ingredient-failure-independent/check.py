#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign16-absdiff-ingredient-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign16-absdiff-ingredient-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==76015 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign16AbsDiffIngredient')" and s['runner_sha256']==sha(packet/'run.py')=='29311527647fafb13390150ec913c3fa05264457800051f5265357f0ce9bbb86';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign16AbsDiffIngredient';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',1)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert log.count('error:')==2 and 'error: unknown tactic' in log and 'error: unsolved goals' in log and 'sorryAx' in log and 'warning:' not in log and not (out/'lib/DiophantineConsistency'/(name+'.olean')).exists() and 'object_sha256' not in row
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
dep=row['dependencies']['DiophantineConsistency.Sign33AbsDiffSquare'];assert dep['sha256']=='f990f1d2f77896b6d52dab63e31e69a0af763c894c5a16d44dc7bb046bce3e65' and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':76015,'outer_exit':1,'compile_exit':1,'errors':2,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'single module failed, reports include sorryAx; no module proof or postflight'},indent=2,sort_keys=True))
