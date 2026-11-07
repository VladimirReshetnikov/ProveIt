#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint29-41-q-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'cf3bfc18a5df1749168121ef7ce41ab77613191fad0663a676ca1a915ab1e44c','provider_preflight.py':'5b9354d9e6ea111f0cfdcdc90365294c41b95039b6a8ea09def8bbae4082a0c2','source-manifest.json':'40abf4bbcba2e44da338d2d12a03da7665757cf467ccf79cdab9c7a9938af22c'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroQValue','6d4797045e10282c480515ba44e69fe24614079fa6f56729d4f325f949675978',['Norm38MacroCValue','Norm38MacroDependentQ'],['d29_Q_value']),('Norm38MacroQPath','2f364886afb7e183db53363eaa8c4065e8661ffd4386b613d3c6051554aaf692',['Norm38MacroQValue','Norm38MacroCheckpoint34to41'],['path29_34','lookup29_34','d41_Q_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroQPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroQValue.lean').read_text();assert 'PrefixPath d29 d34' in path and path.count('PrefixPath.step')==5 and path.count('Dag.snoc')==5 and '(i : Fin 29)' in path
for x in ['prefix_Q','d28_W_carry, d28_C_carry, d26_W_value, d27_C_value','(⟨25, by decide⟩ : Fin 28)','(⟨26, by decide⟩ : Fin 28)','((3 : Int) : R)','((2 : Int) : R)']:assert x in v
assert v.split(':= by',1)[0].count('base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))')==3
for x in ['lookup34_41 a','lookup29_34 a (Fin.last 28)','d29_Q_value a','d11.values a (Fin.last 10)']:assert x in path
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(30,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 Q source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
