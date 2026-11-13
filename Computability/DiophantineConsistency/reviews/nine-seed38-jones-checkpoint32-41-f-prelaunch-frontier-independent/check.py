#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint32-41-f-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'4a132a5b8f05bf9db03d249050f9ca93db3dc8070894a790b32ae93cf31b9e5f','provider_preflight.py':'477c2b7932888e2335aa6ac0f8f2e275140df4657bfb2867093a4d36ae499e0a','source-manifest.json':'552945db404dd3d96749441abc9c0b1167fbe96566a085351f1b56ff01a08cd1'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroFValue','b31037e2de33c6fd1cd46943c7270ff3c158855670659e7ef250a4a69589140c',['Norm38MacroEPath','Norm38MacroDependentF'],['d31_A_from_d29','d32_F_value']),('Norm38MacroFPath','1c15372232f2b09fde8e5ed51330557800cd4dfb6c19c0b3f02f3a3adc57d6c3',['Norm38MacroFValue','Norm38MacroCheckpoint34to41'],['path32_34','lookup32_34','d41_F_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroFPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroFValue.lean').read_text();assert 'PrefixPath d32 d34' in path and path.count('PrefixPath.step')==2 and path.count('Dag.snoc')==2 and '(i : Fin 32)' in path
for x in ['prefix_F','d31_A_from_d29, d29_A_from_d27, d27_A_value, d31_E_value','d11.values a (Fin.last 10)','a ⟨6, by decide⟩']:assert x in v
for x in ['lookup34_41 a','lookup32_34 a (Fin.last 31)','d32_F_value a','d11.values a (Fin.last 10)']:assert x in path
lhs=v.split('theorem d32_F_value',1)[1].split(':= by',1)[0].split('=',1)[1];rhs=path.split('theorem d41_F_value',1)[1].split(':= by',1)[0].split('=',1)[1];assert ''.join(lhs.split())==''.join(rhs.split())
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d32 : Dag 32 := .snoc d31 (.add (.mul (.sub (.pow (.ref ⟨23, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨30, by decide⟩) (.lit 2))) (.constant (1 : Int)))' in nodes
for j in range(33,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 F source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
