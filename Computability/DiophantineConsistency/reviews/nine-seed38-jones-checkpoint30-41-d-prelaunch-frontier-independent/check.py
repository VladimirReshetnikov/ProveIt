#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint30-41-d-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'8fd5687acbe4528dd940ec65237bcacda82317c03e404cef689b2f9b70653976','provider_preflight.py':'93994e3f07d372bae98a0688bdefe00a38552174545fc6eb23225ca5bed2e304','source-manifest.json':'680d996e459b774cdad7ca0c7010707f4c2a0724ba733c93e24a2084c68605df'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDValue','89f84475000478fd9112a8f76a599b5f5aa49413a765a23c797c70ecf180ee45',['Norm38MacroQPath','Norm38MacroAValue','Norm38MacroDependentD'],['d29_A_from_d27','d30_D_value']),('Norm38MacroDPath','d8118d169de7ff5769816971817b78787bb3f1335bba2ac86709f3073279b53e',['Norm38MacroDValue','Norm38MacroCheckpoint34to41'],['path30_34','lookup30_34','d41_D_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroDPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroDValue.lean').read_text();assert 'PrefixPath d30 d34' in path and path.count('PrefixPath.step')==4 and path.count('Dag.snoc')==4 and '(i : Fin 30)' in path
for x in ['prefix_D','d29_A_from_d27, d29_C_carry, d27_A_value, d27_C_value','(⟨23, by decide⟩ : Fin 29)','(⟨26, by decide⟩ : Fin 29)','d11.values a (Fin.last 10)']:assert x in v
for x in ['lookup34_41 a','lookup30_34 a (Fin.last 29)','d30_D_value a','d11.values a (Fin.last 10)']:assert x in path
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(31,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
assert 'def d30 : Dag 30 := .snoc d29 (.add (.mul (.sub (.pow (.ref ⟨23, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨26, by decide⟩) (.lit 2))) (.constant (1 : Int)))' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 D source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
