#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-endpoint-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'7c9dec8f519e297f98283bd6409a1387526ceb6ecfd743f67165da2f3007c39b','source-manifest.json':'f54a1d39ba701007f0ab66a3c2c092ec08391f35960b6a8c11a0a97403812c57','framework-survey.py':'975f8b88a368aec7b62c93f87cf8bda7ad59730321593e002215bceea17f284f'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['Native','Standard','Translated'],m):
 name='Sign27Direct'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-sharing-sign28-endpoint-retry01/src/DiophantineConsistency/Sign28Direct{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-sharing-sign27-endpoint-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Sign28','Sign27');ss.append(p.read_text())
a,b,c=ss
for x in ['abbrev expression := Sign27CurrentExpression.expression','nativeTheory ⊢','nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge']:assert x in a
for x in ['standardTheory ⊢','nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','(IPRAStandardTheory.provable_iff _).2 native_equivalence']:assert x in b
for x in ['standardTheory ⊢','nativeNoZero expression 🡘','(Semiformula.lMap embedding sourceSentence)ᴺ','IPRABoundedRhoZFC.zfcEquiv']:assert x in c
up=D/'reviews/nine-sharing-sign27-concrete-polynomial-bridge-terminal-frontier-independent/check.py';assert H(up)=='67fac5489394738924d5023bd03b19624781cfc7f60c6fa2dc23bd404a8a8bce';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'native, standard and translated arity27 direct endpoints; no Jones, degree, JSON binding or Lean replay'},sort_keys=True,indent=2))
