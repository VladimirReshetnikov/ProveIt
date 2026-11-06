#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint28-41-j-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'12a7b7f02a170718ac08eb77b18b4ddfe5affa65b8db491893da7a6a0c9984f6','provider_preflight.py':'8592ee4f5550d8d1b4268dd927db75c8f22ffec5aa2af8898b5929e974d37367','source-manifest.json':'0f721fb14c0c3c7851e30aa6d680a75c360c8cf4024c4d354b460476443021be'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroJValue','7d54944e7f8f6da38011ef23a961329dbb0ca5b3ceb59f8354904c20dede536f',['Norm38MacroAValue','Norm38MacroDependentJ'],['d28_J_value']),('Norm38MacroJPath','52283482f9db7a369383860e2aaf1d6e8ec69f53e1122f78feb26336e5a3ed90',['Norm38MacroJValue','Norm38MacroCheckpoint34to41'],['path28_34','lookup28_34','d41_J_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroJPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroJValue.lean').read_text();assert 'PrefixPath d28 d34' in path and path.count('PrefixPath.step')==6 and path.count('Dag.snoc')==6 and '(i : Fin 28)' in path
for x in ['prefix_J','d27_A_value','(⟨23, by decide⟩ : Fin 27)','((4 : Int) : R)','((5 : Int) : R)']:assert x in v
for x in ['lookup34_41 a','lookup28_34 a (Fin.last 27)','d28_J_value a','d11.values a (Fin.last 10)']:assert x in path
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(29,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 J source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
