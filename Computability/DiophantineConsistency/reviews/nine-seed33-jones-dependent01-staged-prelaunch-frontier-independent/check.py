#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent01-staged-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='da7d4b187816c559f5fd65e2a7fb01ef10d9b16a9d05673ee3079edb90945b71' and H(P/'source-manifest.json')=='8e5ca177d7c959e70dbd814050577defbef03e01df4867df8250d9e92065db12'
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['Sign33MacroDependentU','Sign33MacroDependentY'];ss=[]
for row,n in zip(m,['U','Y']):
 f=P/'src/DiophantineConsistency'/f'Sign33MacroDependent{n}.lean';old=D/'research/nine-seed38-jones-dependent01-staged-check/src/DiophantineConsistency'/f'Norm38MacroDependent{n}.lean';s=f.read_text();assert s==old.read_text().replace('Norm38','Sign33') and H(f)==row['source_sha256'];ss.append(s)
a,b=ss;assert m[0]['imports']==['DiophantineConsistency.Sign33MacroLive18Group01'] and m[1]['imports']==['DiophantineConsistency.Sign33MacroDependentU']
assert 'd19.values a (Fin.last 18)' in a and 'd20.values a (Fin.last 19)' in b
for s,k in [(a,13),(b,12)]:assert 'd18.values a ((Fin.last 3)'+'.castSucc'*14+')' in s and f'd18.values a ((Fin.last {k})'+'.castSucc'*(17-k)+')' in s and '^ (2 : Nat)' in s
assert b.count('exact Sign33MacroCuts.snoc_previous a d18')==2
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'scope':'U/Y local d19/d20 equations only'},sort_keys=True,indent=2))
