#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-endpoint-import-diagnostic';R=D.parents[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9f6efabbfa3977b7f953c9fcfb1157241e6227145eaeebc9cf5f318da6110305','source-manifest.json':'14a359602ba3898938cd41f8cf3ac5607d77f33a3bfed53d8c4fc05274dd8ed5','framework-survey.py':'3acdde90d023ef49d04517d7094985add7050cf9adf05fdf2716fb088bb41e14'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==3
for e,suffix,imports in zip(m,['Framework','Bridge','Both'],[['DiophantineConsistency.IPRAExpressionNative'],['DiophantineConsistency.Sign26DirectPolynomialBridge'],['DiophantineConsistency.Sign26DirectPolynomialBridge','DiophantineConsistency.IPRAExpressionNative']]):
 name='Sign26Import'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';assert e['module']=='DiophantineConsistency.'+name and e['imports']==imports and H(p)==e['source_sha256']==H(R/e['source']);assert p.read_text()==''.join('import '+x+'\n' for x in imports)
for n,h in [('nine-sharing-sign26-endpoint-retry01-failure-frontier-independent','06be8a94e0868a0e4152fcba784004f1dbffda8aecba0a4260c20e65444d6892'),('nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent','fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e')]:
 q=D/'reviews'/n/'check.py';assert H(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],check=True,capture_output=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],check=True,capture_output=True,text=True,timeout=180);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'three bounded import-only tests: native framework, bridge, then both; no theorem or endpoint','failure_cause':'prior interpreter exception trigger unknown'},sort_keys=True,indent=2))
