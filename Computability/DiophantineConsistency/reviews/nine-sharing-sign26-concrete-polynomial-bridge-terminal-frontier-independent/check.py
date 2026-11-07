#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-concrete-polynomial-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-concrete-polynomial-bridge-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='17330cbc2d93f3acf758b96ade59604a05ee5473de35b347905c942a49e978b6' and H(A/'outer-result.json')=='c9d2482a0cc09ac1680265feb5343c430e88c41ca11c30ee47a9e1bb218bc0b2';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(48627,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1365 and s['runner_sha256']==H(P/'run.py')=='a9c77fad95e3c9dc2d7b4109777552e0975e8036da18deb26b92023403d29a8b';r=s['rows'][0];n='Sign26DirectPolynomialBridge';assert r['module']==n and r['source_sha256']=='0fea3977a1d1a73afb5afc64745bf657b322a1a2f9f556332f44c34d74f2cbbc'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='6f528a24eb7309ad9cea14501f0160ea5c092d9b4c2bf6908a1e6b83aee2acc3'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign26ExpressionEquivalence','95ab5cfb52fb67f180484780fd2f45a109b13749a3f001994f6d36f4fac0df12'),('GenericPolynomialBridgeTransport','235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b'),('Sign27DirectPolynomialBridge','67fffa115363264cc4181c667ff2a0667493b9327708f58e6e500f00e7d24bb3')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign26DirectIPRA.polynomialBridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-concrete-polynomial-bridge-prelaunch-frontier-independent/check.py';assert H(pre)=='5b1c89f807c58d9c370bc9aefd4e80a8ddac2e40382d520975d24733230f5564';
for name,h in [('nine-sharing-sign26-expression-equivalence-terminal-frontier-independent','63d47049f3c9dffb25d6bd3cee3300f6cab1c9be6cd3b641a87d325f9caf7d9d'),('nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent','128c8689e3ab56ecdfb0bdada83eba33f01cd3f779935ab1b6712ee5d591f155'),('nine-sharing-sign27-concrete-polynomial-bridge-terminal-frontier-independent','67fac5489394738924d5023bd03b19624781cfc7f60c6fa2dc23bd404a8a8bce')]:
 up=D/'reviews'/name/'check.py';assert H(up)==h;subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':48627,'guards':200,'links':1365,'scope':'sign26 direct current-expression PolynomialBridge only; no iPRA endpoint'},sort_keys=True,indent=2))
