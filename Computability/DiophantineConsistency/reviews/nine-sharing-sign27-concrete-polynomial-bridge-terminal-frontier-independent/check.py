#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-concrete-polynomial-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-concrete-polynomial-bridge-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='d9ccb9754fddf8154718387e024e3bdc18b766fc080127afcbe04aea1c0d14c1' and H(A/'outer-result.json')=='1430744a8b7f7d46cc5ce3cdb9363f594f77b125c14664ea9cb18f95169782ac';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(24384,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1343 and s['runner_sha256']==H(P/'run.py')=='e4e1ccefdc6777a8bbbe73407ad35931dba6380fa3c97b18431fbfabb5397bcc';r=s['rows'][0];n='Sign27DirectPolynomialBridge';assert r['module']==n and r['source_sha256']=='047c01906cb3e0cbb7ab19701e4596849ef772cd4eb25b69d9cfde9e1cd23ec5'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='67fffa115363264cc4181c667ff2a0667493b9327708f58e6e500f00e7d24bb3'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign27ExpressionEquivalence','d50fd8e0c97401e207a88d1543725e96f951c86abf6dcd624146bb1bde9a8244'),('GenericPolynomialBridgeTransport','235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b'),('Sign28DirectPolynomialBridge','211972881dab16d1bb9be9c457b18a0e48b698be5199bdf2918d781d5e06ab07')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign27DirectIPRA.polynomialBridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-concrete-polynomial-bridge-prelaunch-frontier-independent/check.py';assert H(pre)=='43dd6c07e24df4998ac44eab1f0e70807b652c6768450391c0736bccbcb96308';up=D/'reviews/nine-sharing-sign27-expression-equivalence-terminal-frontier-independent/check.py';assert H(up)=='d83d8ab0288caa17c27eb288d3316011a009080d4744279e5d3f2432bb9db92b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':24384,'guards':200,'links':1343,'scope':'sign27 polynomialBridge transport only; no endpoint or degree theorem'},sort_keys=True,indent=2))
