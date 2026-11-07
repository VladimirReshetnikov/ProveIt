#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-generic-polynomial-bridge-transport-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-generic-polynomial-bridge-transport-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='d604c3bf11c79dbcdab62d7d14ed57b2b91fceedbf17522c5168732367b02088' and H(A/'outer-result.json')=='aa621a499bf3478786272355c82574bd7a17ca6257f1f2f78ed5572b461dc9c8'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1078 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(7548,1) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='0bee6f49beb8265319ff928ead7e411bd46020606f90d3d940ae4bacde70aa02'
r=s['rows'][0];n='GenericPolynomialBridgeTransport';assert r['module']==n and r['source_sha256']=='b0dc3ab6322c0f3734f482ff7dcbb5d89c1effdd9831cba505964978a01aba00'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',1)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert 'unknown namespace `ModelDifferenceRing`' in log and 'Unknown identifier `ORingStructure`' in log and 'sorryAx' in log
assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('HAExpressionAssembly','d30b8e7061691488009f7e746f717daaaf649f6d2f92e393a83d036585fd98a5'),('AdaptiveEquationSyntax2011','09a6f3812f5169f0d71d4bd4d5604537c5e1b91d41dee5cf4b2cf212f1f4b473')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-generic-polynomial-bridge-transport-prelaunch-frontier-independent/check.py';assert H(review)=='dfa7c0b88fec853928d3f281df4406b2cc8f7667ea1b076c0840eb9dbb3f3b4d'
survey=P/'provider-survey.py';assert H(survey)=='6fa854001c4c55a5096fb7b373d3c1014a5c3a4a8f2b851de94ed63fb29226ef';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':7548,'outer_exit':1,'lean_exit':1,'guards':150,'links':1078,'scope':'error-contaminated report; no successful theorem or whole-run final postflight'},sort_keys=True,indent=2))
