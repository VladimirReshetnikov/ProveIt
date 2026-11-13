#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint21-27-m-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'6268cea030254ce801b2bfd99b25bda4d16e7cc1d0d3153df528bb3fdd6acb41','provider_preflight.py':'a30bb545ed7be024afbff1df18e61f3f8599dd0e0c21e906b42174320eb16c6e','source-manifest.json':'89c959ee05c6a159cf85e84d20bbb54a1fe1bfb7e4fe8238a312acab5536e36f'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroMPath','a011200fa1d21b58d2986763cc4e6a0651160bb220e5fdf8635123a542b6229e',['Norm38MacroUYValues'],['path21_27','lookup21_27']),('Norm38MacroMValue','01e3005d2546431cc995315ea20170c174b12b5d39c93c956afd14ff1ba0e9a4',['Norm38MacroMPath','Norm38MacroDependentM','Norm38MacroLive18Group02'],['d27_M_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroMPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroMValue.lean').read_text();assert 'PrefixPath d21 d27' in path and path.count('PrefixPath.step')==6 and path.count('Dag.snoc')==6 and '(i : Fin 21)' in path
for x in ['d11.values a (Fin.last 10)','prefix_M a','d20_R_carry, d18_R_carry','(lookup20_27 a (Fin.last 19)).symm.trans (d27_Y_value a)','((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)','a ⟨3, by decide⟩']:assert x in v
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(22,28):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d27 M source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
