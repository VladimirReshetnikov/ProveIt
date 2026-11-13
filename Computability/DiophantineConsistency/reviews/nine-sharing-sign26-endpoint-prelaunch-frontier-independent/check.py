#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-endpoint-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'2a2c5f2e74fdf83582b29da4232af9129b01a88c9a8fbcaa4e925fe31ceff5f2','source-manifest.json':'6f2b185b0bc74f42dec7a2e2a6b9ee0a5104d17486268e05b24dffe3d34178f9','framework-survey.py':'3acdde90d023ef49d04517d7094985add7050cf9adf05fdf2716fb088bb41e14'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['Native','Standard','Translated'],m):
 name='Sign26Direct'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-sharing-sign27-endpoint-check/src/DiophantineConsistency/Sign27Direct{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign26-endpoint-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Sign27','Sign26');ss.append(p.read_text())
a,b,c=ss
for x in ['abbrev expression := Sign26CurrentExpression.expression','nativeTheory ⊢','nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge']:assert x in a
for x in ['standardTheory ⊢','nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','(IPRAStandardTheory.provable_iff _).2 native_equivalence']:assert x in b
for x in ['standardTheory ⊢','nativeNoZero expression 🡘','(Semiformula.lMap embedding sourceSentence)ᴺ','IPRABoundedRhoZFC.zfcEquiv']:assert x in c
up=D/'reviews/nine-sharing-sign26-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(up)=='fd473ee75a9b02210da1c3d6d9b57d4fac253bfca1b64bae131fea5b009abd6e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'native, standard and translated arity26 direct endpoints; no Jones, degree, JSON binding or Lean replay'},sort_keys=True,indent=2))
