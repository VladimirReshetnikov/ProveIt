#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign16-scalar-window-retry01-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign16-scalar-window-retry01-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==69390 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='2414bc53fc5714e30cf1b8a69060231d586437eadd03c7cf14a88f84f956eed5';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign16ScalarWindow';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(t in log for t in ('error:','warning:','sorryAx')) and 'q_bound_of_seed' in log and '[propext, Classical.choice, Quot.sound]' in log and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='70c001b4cc7328142729c567f7f8fd6b54bf37fa048411e2835b4c143ff9c6a5'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
dep=row['dependencies']['DiophantineConsistency.Sign16TransportRow'];assert dep['sha256']=='114409a7b08eea61d85276ed3e1d0ac38730d218c4b7844b0bb97da039fdbb73' and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
dep2=row['dependencies']['DiophantineConsistency.ArithmeticPellFirstIndex'];assert dep2['sha256']=='20d3769d891a42810c1985203768b122bf936884494d2829415e3140d6deb9c2' and row['direct_guard'][dep2['path']]=={'sha256':dep2['sha256'],'realpath':dep2['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':69390,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'conditional q ≥ F from seed-zero and explicit beta/port bounds; no V lift'},indent=2,sort_keys=True))
