#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-root-recovery-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-root-recovery-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='7329d41c7287432ed37741ff236c9e08543938c5e1e86879bfb068705b2fb379' and H(A/'outer-result.json')=='d166c2d83138c36f54e07e7efa2465504e39e5fce232b3a9fc29685563c6c44d'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1059 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(32826,0) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='4dd29b718953a2986978b008adaf78c9c18c1037b9947d163e828222e3e311dd'
r=s['rows'][0];n='Sign27RootRecovery';assert r['module']==n and r['source_sha256']==json.loads((P/'source-manifest.json').read_text())['rows'][0]['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==100
for phase,exit in [('deps',0),('compile',0)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign27RootRecovery.recover' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
assert r['object_sha256']=='065b4474bc229207244e43a310e63755371e9e1d3679391d1b60cb8e78da2133'==H(O/'lib/DiophantineConsistency'/f'{n}.olean')
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('SharingSign28Squares','942397e7cb222881da765f30804b2c4775673cba5a324cb58f0c51416d6c3f04')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign27-root-recovery-prelaunch-frontier-independent/check.py';assert H(review)=='00cef88c89575c5a0a443d906e327f59093f2a6e5fe088c16bfd29e3aa67341e'

print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':7548,'outer_exit':0,'lean_exit':0,'guards':100,'links':1059,'scope':'abstract root recovery from explicit embedded equation only'},sort_keys=True,indent=2))
