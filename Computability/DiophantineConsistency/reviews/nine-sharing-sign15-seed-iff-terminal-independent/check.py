#!/usr/bin/env python3
"""Audit failed generic sign15 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign15-seed-iff-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign15-seed-iff-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==45350 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='cb9d45935179ba9cb4be6e35ed493cfffb2d51aa04075d27b104981974515d8f';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign15SeedExistential';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(t in log for t in ('error:','warning:','sorryAx')) and 'exists_same_input' in log and '[propext, Classical.choice, Quot.sound]' in log and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='0cf8225fb3069eaffc96a8773c923a5b97d3e0123124b2f3f45fc1171bf221f4'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign15ReverseBridge','52873056e92e02668feb88be3308436adba38f799ff03bdf27219d007f56e72f'),('Sign15InnerLift','447b4a4155705920a15aae9d3ec9410c52324b3f85e9d4816bf1032680cba762'),('Sign15SignedValue','705038b1d6a94e0cc9550acf0bfb73c62044cb3a4e8629b991f6428155a38d6c')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':45350,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'same-input existential seed iff under represented ports and bounds; current specialization and endpoint separate'},indent=2,sort_keys=True))
