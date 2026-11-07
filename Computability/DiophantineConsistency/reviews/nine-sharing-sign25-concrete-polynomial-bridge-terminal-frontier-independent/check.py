#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-concrete-polynomial-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-concrete-polynomial-bridge-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='56e28709b696263dae760913e55db17a216776a2c21ca4f43fe5685c45183094' and H(A/'outer-result.json')=='847c79114596c2ecff6d4e3e0d39d7951ba151a3a9cb6493c4fa847e08a6d34e';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(71841,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1381 and s['runner_sha256']==H(P/'run.py')=='53b5a24c764e7538529310f655a882225294b9e8c297a2c1f070ce35be365bc8';r=s['rows'][0];n='Sign25DirectPolynomialBridge';assert r['module']==n and r['source_sha256']=='fc12719961654883f1fa6abc7456e1c562b5565f07965342efd21476eb687ca8'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='b662728032c262f52f1bda8a52d9b29401129c6279a3f9d4e6f8e2924980f1ea'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('Sign25ExpressionEquivalence','37ed3cc6346eb68df0fb8d4bec90edd66801cb9ba61f25301811202e1c141683'),('GenericPolynomialBridgeTransport','235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b'),('Sign26DirectPolynomialBridge','6f528a24eb7309ad9cea14501f0160ea5c092d9b4c2bf6908a1e6b83aee2acc3')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log and "'DiophantineConsistency.Sign25DirectIPRA.polynomialBridge' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-concrete-polynomial-bridge-prelaunch-frontier-independent/check.py';assert H(pre)=='ccde6644b68b19d55c122503b4e572b362758f515d7915e163293f5a9975eb67';
for name,h in [('nine-sharing-sign25-expression-equivalence-terminal-frontier-independent','900f62f0d05eb5d4ec8640653fbadac54cdec024a96e0207e5a594375e436999'),('nine-sharing-generic-polynomial-bridge-transport-retry01-terminal-frontier-independent','128c8689e3ab56ecdfb0bdada83eba33f01cd3f779935ab1b6712ee5d591f155'),('nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent','fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e')]:
 up=D/'reviews'/name/'check.py';assert H(up)==h;subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':71841,'guards':200,'links':1381,'scope':'sign25 direct current-expression PolynomialBridge only; no iPRA endpoint'},sort_keys=True,indent=2))
