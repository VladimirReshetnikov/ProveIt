#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign14-tau-lift-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign14-tau-lift-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==94421 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='beb266f2f240c5c05145d6c87c0a154378f85880a4fe6bad35b529885b2a9291';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign14TauLift';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert not any(t in log for t in ('error:','warning:','sorryAx')) and 'exists_tau_of_seed' in log and '[propext, Classical.choice, Quot.sound]' in ' '.join(log.split()) and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='288b98404b5f8d44ddacb4ad2760089162b10f641aca8a5392e04f5ae36cc798'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign14ScalarWindow','54063b97772922cb16f200cbc6d0d04804111e410384076d352f03c9e3c89099'),('Sign14TauBound','a7aafc1a6eb30a85be6dfcfb90a94bc17acb12a2d8cf418858387fedde5186e3'),('Sign14TauValue','885c3eff61e9b8db39fc885cda4f32ac09f6871b871650e7ffe7714d597596a9')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':94421,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'natural deleted tau representative conditional on seed/port/bounds; no residual transfer or equivalence'},indent=2,sort_keys=True))
