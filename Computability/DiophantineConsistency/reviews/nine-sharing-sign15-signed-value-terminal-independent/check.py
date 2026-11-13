#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign15-signed-value-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign15-signed-value-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==54120 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='089a4a7e90bb2b08b0dac632c65bf76a05c9b5f67c23415e632fc0e2c104d0b3';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign15SignedValue';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(x in log for x in ('error:','warning:','sorryAx')) and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='705038b1d6a94e0cc9550acf0bfb73c62044cb3a4e8629b991f6428155a38d6c'; joined=' '.join(log.split());assert joined.count('[propext, Classical.choice, Quot.sound]')==2 and 'inner_eval' in joined and 'signed_eval' in joined
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
dep=row['dependencies']['DiophantineConsistency.Sign15RankValue'];assert dep['sha256']=='7c3dd5d7f1909c7920967d12bf2450eaa57fe078f1475bbff709ac359a2424f9' and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':54120,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'signed inner/V evaluations under represented ports and q≥F; no natural witness or lift'},indent=2,sort_keys=True))
