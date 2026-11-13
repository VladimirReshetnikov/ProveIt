#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint33-41-gprime-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'60588e33e7c5afa33fdae84cd75d282c9870c95d20a76470028f79ee29291ce5','provider_preflight.py':'561c8942b0bba1b28a4b022ac54f7d9668d08794cf780782a2acae2d4607f7bd','source-manifest.json':'52d7871e097e9e823474bf1af912d9c78666b1e139049451c8ca925c90f5af18'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroGprimeValue','08bd07a6fa7a50daf39de9af961b67cdab9b6e83d5d8dc56cfb8605315e9b39c',['Norm38MacroFPath','Norm38MacroDependentGprime'],['d32_A_value','d33_Gprime_value']),('Norm38MacroGprimePath','d9a62e147f8c962f453da82a0e273fd3463d1b65efb20d5d28070a6e1d197df6',['Norm38MacroGprimeValue','Norm38MacroCheckpoint34to41'],['path33_34','lookup33_34','d41_Gprime_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroGprimePath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroGprimeValue.lean').read_text();assert 'PrefixPath d33 d34' in path and path.count('PrefixPath.step')==1 and path.count('Dag.snoc')==1 and '(i : Fin 33)' in path
for x in ['prefix_Gprime','d32_A_value, d32_F_value, d32_C_carry, d32_D_carry, d27_C_value, d30_D_value','d11.values a (Fin.last 10)','a ⟨6, by decide⟩']:assert x in v
for x in ['lookup34_41 a','lookup33_34 a (Fin.last 32)','d33_Gprime_value a','d11.values a (Fin.last 10)']:assert x in path
lhs=v.split('theorem d33_Gprime_value',1)[1].split(':= by',1)[0].split('=',1)[1];rhs=path.split('theorem d41_Gprime_value',1)[1].split(':= by',1)[0].split('=',1)[1];assert ''.join(lhs.split())==''.join(rhs.split())
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d33 : Dag 33 := .snoc d32 (.add (.ref ⟨23, by decide⟩) (.mul (.ref ⟨31, by decide⟩) (.sub (.add (.mul (.ref ⟨26, by decide⟩) (.ref ⟨29, by decide⟩)) (.constant (1 : Int))) (.ref ⟨23, by decide⟩))))' in nodes
for j in range(34,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 Gprime source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
