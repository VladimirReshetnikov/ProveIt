#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-seed-root-recovery-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-seed-root-recovery-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='2d16a4676ee192bd1b57aeaec13c0fc126f31d0a8bb5031423dfdb287c83fbe2' and H(A/'outer-result.json')=='ac7a98ff9865662aeffcf21a35d418bb52a3e9b7fa2eced9f731bf2f3fba7e1e'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1060 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(13719,0) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='9842a39912fe33b6b31d2a035a66669256aa83b5d9cd1764f3391103873062fd'
r=s['rows'][0];n='Sign27SeedRootRecovery';assert r['module']==n and r['source_sha256']==json.loads((P/'source-manifest.json').read_text())['rows'][0]['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==100
for phase,exit in [('deps',0),('compile',0)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign27SeedRootRecovery.recover' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
assert r['object_sha256']=='27b27811d4aaf0588408034bed6405e76b500ff733794fd59a037aea854a0305'==H(O/'lib/DiophantineConsistency'/f'{n}.olean')
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign27RootRecovery','065b4474bc229207244e43a310e63755371e9e1d3679391d1b60cb8e78da2133')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
assert "'DiophantineConsistency.Sign27SeedRootRecovery.oldN1_row' depends on axioms: [propext]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign27-seed-root-recovery-prelaunch-frontier-independent/check.py';assert H(review)=='6bb9ad916736f2279b8f3974582062f85db56e2fbe591c307786456fb943799f'

print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':7548,'outer_exit':0,'lean_exit':0,'guards':100,'links':1060,'scope':'sign28 seed zero implies root predecessor and reconstruction only'},sort_keys=True,indent=2))
