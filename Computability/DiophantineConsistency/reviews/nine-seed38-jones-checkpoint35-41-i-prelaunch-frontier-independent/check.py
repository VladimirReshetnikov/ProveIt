#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint35-41-i-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'91cfb695bfb0f55bede4a7e5b28026867f76abb3b3829a49d95b3abbc1845fe3','provider_preflight.py':'7054af0cbb1b8c8dad0e1d3a039e66361ca5ea289c46d855f4a89318bdc1250a','source-manifest.json':'d424b35793d0fe74265f24c2f0fd8e3b40bb75704f6f0d23ffb4989525a1c7a8'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroIValue','b8b667a072ac2dc69c5318554b887592f08ba1a2b161760ece81204832b43c99',['Norm38MacroHPath','Norm38MacroDependentI'],['d35_I_value']),('Norm38MacroIPath','c817dc8334bb95f2eabd7d0660d5522fcbdfc407b7df1a179b6fc59557d78179',['Norm38MacroIValue'],['path35_41','lookup35_41','d41_I_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroIPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroIValue.lean').read_text()
for x in ['prefix_I','d34_Gprime_carry, d33_Gprime_value, d34_H_value','d11.values a (Fin.last 10)']:assert x in v
for x in ['PrefixPath d35 d41','lookup35_41 a','d35_I_value a','d11.values a (Fin.last 10)']:assert x in path
assert path.count('PrefixPath.step')==6 and path.count('Dag.snoc')==6 and '(i : Fin 35)' in path
lhs=v.split('theorem d35_I_value',1)[1].split(':= by',1)[0].split('=',1)[1];rhs=path.split('theorem d41_I_value',1)[1].split(':= by',1)[0].split('=',1)[1];assert ''.join(lhs.split())==''.join(rhs.split())
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d35 : Dag 35 := .snoc d34 (.add (.mul (.sub (.pow (.ref ⟨32, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨33, by decide⟩) (.lit 2))) (.constant (1 : Int)))' in nodes
for j in range(36,42):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 I source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
