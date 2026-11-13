#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign15-other-rows-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign15-other-rows-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==37101 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='641180ef8fcc8911bcd4e534cfccd969eb62be9b31c44f029fc949eaaaef2c97';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign15OtherRows';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(x in log for x in ('error:','sorryAx')) and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='ff48b719302bb41fe60881a37944509803ff07032ace282aea6f460b08095513'; joined=' '.join(log.split());assert joined.count('[propext, Classical.choice, Quot.sound]')==4 and all('row'+i+'_of_seed' in joined for i in ('00','01','02','05')) and log.count('warning:')==0
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
dep=row['dependencies']['DiophantineConsistency.Sign15NaRow'];assert dep['sha256']=='cfbbdf2cd63ca665a595308c3d48b5beb9f018568ba5802106200160ef6ac8e6' and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':37101,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'four staged seed-zero row consequences with abstract shared evaluations; no natural lift or bridge'},indent=2,sort_keys=True))
