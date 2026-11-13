#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-endpoint-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'3f6c310edd5b967976a0c9dcbd0f73fb19bf54a7d5982765b9cf2439b6efe620','source-manifest.json':'343b395726171693df1a4c1e776b31801e7bbee9e4d857db9dfb17d968b6b6cf','framework-survey.py':'20bceb0b7631d230eac91deb2778690edb90a6d72c4af61a07e2bc4edc97c9a6'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign28DirectNative','Sign28DirectStandard','Sign28DirectTranslated'];assert [r['module'].split('.')[-1] for r in m]==names;ss=[]
imps=[['Sign28DirectPolynomialBridge','IPRAExpressionNative'],['Sign28DirectNative','IPRAStandardTheory'],['Sign28DirectStandard']]
for r,n,deps in zip(m,names,imps):
 f=P/'src/DiophantineConsistency'/f'{n}.lean';s=f.read_text();ss.append(s);assert H(f)==r['source_sha256'] and r['imports']==['DiophantineConsistency.'+x for x in deps]
a,b,c=ss
for x in ['abbrev expression := Sign28CurrentExpression.expression','nativeTheory ⊢','IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge']:assert x in a
for x in ['IPRAStandardTheory.standardTheory ⊢','IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','(IPRAStandardTheory.provable_iff _).2 native_equivalence']:assert x in b
for x in ['IPRAStandardTheory.standardTheory ⊢','(Semiformula.lMap embedding sourceSentence)ᴺ','IPRABoundedRhoZFC.zfcEquiv','standard_equivalence']:assert x in c
f=D/'reviews/nine-sharing-sign28-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(f)=='636f8d20637997f460a9a64577ed3d61d1fdeffd26c6527031c5519f5647e4c5';subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':3,'scope':'proposed direct Fin28 native/standard/translated endpoints; no degree or JSON claim'},sort_keys=True,indent=2))
