#!/usr/bin/env python3
"""Audit failed generic sign15 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign14-seed-iff-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign14-seed-iff-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==96645 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='6df2d882009491af649726ba1bc7d4751c38f8735149622b15e052f2967b2832';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign14SeedExistential';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(t in log for t in ('error:','warning:','sorryAx')) and 'exists_same_input' in log and '[propext, Classical.choice, Quot.sound]' in log and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='880b4e2628c36e0fc9c1b196bedad9ff3cdd9e61512968076ed4d6e93dfc92f8'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign14ReverseBridge','7ea2b752484bef153bd60daa91fcf88abe9b31fea59cf4216e14068fdfbb1a61'),('Sign14TauLift','288b98404b5f8d44ddacb4ad2760089162b10f641aca8a5392e04f5ae36cc798')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':96645,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'same-input existential seed iff under represented ports and bounds; current specialization and endpoint separate'},indent=2,sort_keys=True))
