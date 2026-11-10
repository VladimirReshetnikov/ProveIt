#!/usr/bin/env python3
"""Audit failed generic sign15 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign15-shared-values-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign15-shared-values-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==39211 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='b85e49674b748ba58e6c0d9d2b9177a7c221b6ff56b3aaa8fed147d2c4300ebe';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign15SharedValues';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(x in log for x in ('error:','sorryAx')) and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='70205b94ead9a3289e832873adf19cace15abbbef8c89ef5302445c342bd3502'; joined=' '.join(log.split());assert joined.count('[propext, Classical.choice, Quot.sound]')==3 and all(x in joined for x in ('c_eval','root_eval','scale_eval')) and log.count('warning:')==0
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
dep=row['dependencies']['DiophantineConsistency.SharingSign15Squares'];assert dep['sha256']=='ecf997b0986535b95b1f3fe5534e7c94542fa5802db09aaad556852a3fd3ce4b' and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':39211,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'three natural shared evaluations under beta representation; no natural lift or bridge'},indent=2,sort_keys=True))
