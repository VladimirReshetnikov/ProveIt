#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-generic-polynomial-bridge-transport-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-generic-polynomial-bridge-transport-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='4751cdfc27a4f72a533f11c0b83b0db02acf6a14e2bff36186dc307ceffaa111' and H(A/'outer-result.json')=='ef35dae8397f85cd90489ae06fa4d91966d08bf7c787d94425f3638cd1948b5f'
s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1078 and (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(48356,0) and o['retained_state_sha256']==H(A/'state.json')
assert s['runner_sha256']==H(P/'run.py')=='73764ef195c6356fdc262f7f2c24292e90bedd1c8350cfa1c29d1f3f215b13dc'
r=s['rows'][0];n='GenericPolynomialBridgeTransport';assert r['module']==n and r['source_sha256']==json.loads((P/'source-manifest.json').read_text())['rows'][0]['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==150
for phase,exit in [('deps',0),('compile',0)]:
 v=r[phase];assert v['exit']==exit and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.GenericPolynomialBridgeTransport.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
assert r['object_sha256']=='235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b'==H(O/'lib/DiophantineConsistency'/f'{n}.olean')
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('HAExpressionAssembly','d30b8e7061691488009f7e746f717daaaf649f6d2f92e393a83d036585fd98a5'),('AdaptiveEquationSyntax2011','09a6f3812f5169f0d71d4bd4d5604537c5e1b91d41dee5cf4b2cf212f1f4b473')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-generic-polynomial-bridge-transport-retry01-prelaunch-frontier-independent/check.py';assert H(review)=='7f54d89f1404991c133301aa6353b0181e3f484e1e8e6a357d4c69ade6e74bbd'
survey=P/'provider-survey.py';assert H(survey)=='6fa854001c4c55a5096fb7b373d3c1014a5c3a4a8f2b851de94ed63fb29226ef';subprocess.run([sys.executable,'-I','-S','-B',str(survey)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':7548,'outer_exit':0,'lean_exit':0,'guards':150,'links':1078,'scope':'conditional generic bridge transfer only'},sort_keys=True,indent=2))
