#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint24-27-a-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'ecb8ee48bee1d8bef38fa496e5db61bb1d4014aedfb9d44854d10c9ff24aadb7','provider_preflight.py':'b2da72482d3971c334cf1d8176e7a56d1ff9cff2d881740b425d49676270f5b0','source-manifest.json':'b6c782011816c40b9f05a8b42b0506a85e86574163d55dc01de5e81f907cd5c5'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroAPath','cbbe657413312903eca6f947477b05a7f92ad4fc2b817f8bb7feec0d56463fed',['Norm38MacroMValue'],['path24_27','lookup24_27']),('Norm38MacroAValue','4422b046d07d41e4c94a001b025e6c9f191e184f260788047bd029956710c495',['Norm38MacroAPath','Norm38MacroDependentA'],['d27_A_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroAPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroAValue.lean').read_text();assert 'PrefixPath d24 d27' in path and path.count('PrefixPath.step')==3 and path.count('Dag.snoc')==3 and '(i : Fin 24)' in path
for x in ['prefix_A a','d23_M_carry','d23_U_carry','(lookup21_27 a (Fin.last 20)).symm','d27_M_value, d27_U_value','d11.values a (Fin.last 10)','a ⟨3, by decide⟩','a ⟨4, by decide⟩']:assert x in v
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(25,28):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d27 A source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
