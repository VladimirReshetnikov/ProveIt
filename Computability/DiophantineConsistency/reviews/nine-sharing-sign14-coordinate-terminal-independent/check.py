#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign14-coordinate-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign14-coordinate-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==1190 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='4053c50093e94e6b8a6a9a84989a857bcac7ef26813f40c342016010f15c1b4b';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign14Coordinate';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:')==47 and all(t in log for t in ('old_d_row','d_zero','lift_drop','old_gap')) and '[propext, Classical.choice, Quot.sound]' in log and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='9589d91da534643f5246ac13e49eba950a3701ab55e5865138d97511496698b0'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('SharingSign14Squares','07a14f712fdc50448837f6bbc63085c68180629aecb20873f06e76473b9f8d44'),('SharingSign15Squares','ecf997b0986535b95b1f3fe5534e7c94542fa5802db09aaad556852a3fd3ce4b')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':1190,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'conditional supplied-gap coordinate zero/recovery without port assumptions; no zero bridge'},indent=2,sort_keys=True))
