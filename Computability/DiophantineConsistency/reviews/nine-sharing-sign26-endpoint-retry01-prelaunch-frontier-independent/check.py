#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-endpoint-retry01';Q=D/'research/nine-sharing-sign26-endpoint-check';R=D.parents[1];H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'adada33b8af36074033fca06ecdd345b853b2b24e74dbcfedbccd730bd50b49b','source-manifest.json':'b0545f5858304696f11f6bd5bf31e2865458b67f21908981e150335051a090cc','framework-survey.py':'3acdde90d023ef49d04517d7094985add7050cf9adf05fdf2716fb088bb41e14'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==3
for suffix,e in zip(['Native','Standard','Translated'],m):
 name='Sign26Direct'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=Q/'src/DiophantineConsistency'/f'{name}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(R/e['source']);before=old.read_text();after=p.read_text()
 if suffix=='Native':assert H(p)=='582aed56a2f0effc6f97b95929abc574dec4d2151c5ef06168a11e4b9668d277' and after==before.replace('  Sign26CurrentExpression.expression\n','  Sign26CurrentExpression.expression SharingSeed26Sextic.seed\n  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero\n')
 else:assert after==before
for n,h in [('nine-sharing-sign26-endpoint-failure-frontier-independent','4f73af1cc25ecc5a4b208475bac4de4871128352b69cdf66cfaca970d06027dd'),('nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent','fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e')]:
 q=D/'reviews'/n/'check.py';assert H(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],check=True,capture_output=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],check=True,capture_output=True,text=True,timeout=180);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'local irreducibility retry for native, standard and translated sign26 direct endpoints; success untested','failure_cause':'precise interpreter trigger unknown'},sort_keys=True,indent=2))
