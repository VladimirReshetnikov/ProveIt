#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint31-41-e-retry01';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'72e7797acdb47e94ad936e92748fdbbe60a26988f0e5bd0153e882c3868b8dbf','provider_preflight.py':'a8a207ffce9e66ca94e04fc2cec6d6868571a13295ed96fba0647f3f717ee45c','source-manifest.json':'4e9ce2475448c1d56bf1cf6c643b1cae9b29bfbb8986c573cc203ad552891ccd'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroEValue','f9055712fdec655180442edb8fe843a8fdfc7679cd072b10a2931abe9b043809',['Norm38MacroDPath','Norm38MacroDependentE','Norm38MacroLive18Group04','Norm38MacroPrefixInputsB','Norm38MacroJValue'],['d30_i_value','d31_E_value']),('Norm38MacroEPath','c9e0519b4dee63ac8ec19ca7c113ae747e3da4a916dddf2bfedeef7830541dd8',['Norm38MacroEValue','Norm38MacroCheckpoint34to41'],['path31_34','lookup31_34','d41_E_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroEPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroEValue.lean').read_text();assert 'PrefixPath d31 d34' in path and path.count('PrefixPath.step')==3 and path.count('Dag.snoc')==3 and '(i : Fin 31)' in path
for x in ['d30_i_carry, d24_i_carry, d18_i_carry, Norm38MacroPrefixGroup04.prefix_i','prefix_E','d30_i_value, d30_J_carry, d30_C_carry, d28_J_value, d30_D_value, d27_C_value','d11.values a (Fin.last 10)','a ⟨6, by decide⟩']:assert x in v
for x in ['lookup34_41 a','lookup31_34 a (Fin.last 30)','d31_E_value a','d11.values a (Fin.last 10)']:assert x in path
lhs=v.split('theorem d31_E_value',1)[1].split(':= by',1)[0].split('=',1)[1];rhs=path.split('theorem d41_E_value',1)[1].split(':= by',1)[0].split('=',1)[1];assert ''.join(lhs.split())==''.join(rhs.split())
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(32,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
assert 'def d31 : Dag 31 := .snoc d30 (.mul (.mul (.mul (.ref ⟨15, by decide⟩) (.ref ⟨27, by decide⟩)) (.ref ⟨29, by decide⟩)) (.pow (.ref ⟨26, by decide⟩) (.lit 2)))' in nodes


old=d/'research/nine-seed38-jones-checkpoint31-41-e-check'
ov=(old/'src/DiophantineConsistency/Norm38MacroEValue.lean').read_text()
assert ov.count('d18_i_carry, prefix_i]')==1
assert ov.replace('d18_i_carry, prefix_i]', 'd18_i_carry, Norm38MacroPrefixGroup04.prefix_i]')==v
assert (old/'src/DiophantineConsistency/Norm38MacroEPath.lean').read_text()==path
provider=(d/'research/nine-seed38-jones-prefix-group04-staged-check/src/DiophantineConsistency/Norm38MacroPrefixInputsB.lean').read_text()
assert 'namespace DiophantineConsistency.Norm38MacroPrefixGroup04' in provider and 'theorem prefix_i' in provider
run_old=(old/'run.py').read_text(); run_new=(p/'run.py').read_text()
for a,b in [('checkpoint31-41-e-check-20261106','checkpoint31-41-e-retry01-20261106'),('checkpoint31-41-e-draft','checkpoint31-41-e-retry01-draft'),('d2510ec44441cdcd46e231343944659c876312a5798dc692b7fbfa368107e16f','f9055712fdec655180442edb8fe843a8fdfc7679cd072b10a2931abe9b043809'),('02912152ff539ade311f0850257b7891ed92555aa679755ec926e2ba5c0761af','a8a207ffce9e66ca94e04fc2cec6d6868571a13295ed96fba0647f3f717ee45c'),('5c9454633f2880b08315ab7da0fee0a0324b2f67cfc63343618fcbd775d136bd','4e9ce2475448c1d56bf1cf6c643b1cae9b29bfbb8986c573cc203ad552891ccd')]: run_old=run_old.replace(a,b)
assert run_old==run_new
surv_old=(old/'provider_preflight.py').read_text().replace('checkpoint31-41-e-draft','checkpoint31-41-e-retry01-draft').replace('d2510ec44441cdcd46e231343944659c876312a5798dc692b7fbfa368107e16f','f9055712fdec655180442edb8fe843a8fdfc7679cd072b10a2931abe9b043809')
assert surv_old==(p/'provider_preflight.py').read_text()

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 E source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
