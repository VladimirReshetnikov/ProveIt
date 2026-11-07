#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint36-41-a0-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'f938be8a89b94f848f40931a3ac97fecba21e6e1d47715630070d9376a28883e','provider_preflight.py':'a44baa8b135feaee832601ca38ed28937c06f95064f4de8b1faa7907accb3bb1','source-manifest.json':'04a987032fe4a37c3d012084f0bdb9fb35d0283dbc7143028b86a992a4057bf8'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroPKPaths','46c57452feae35e9c7f7d515778c22ad229c47aef1dbe9ffb6560b18a0cbd1c4',['Norm38MacroKValue'],['path22_27','lookup22_27','path23_27','lookup23_27']),('Norm38MacroA0Value','2d3c033a4407197c7692d680414292ff4d91025a600c50bea098b83c5e4db9e4',['Norm38MacroPKPaths','Norm38MacroDependentA0'],['d35_P_value','d35_K_value','d36_A0_value']),('Norm38MacroA0Path','49344aea80f0f8d8bfe75c6aca4f8e9af5936ee8dc0be16852f107f3aa00d932',['Norm38MacroA0Value'],['path36_41','lookup36_41','d41_A0_value'])];assert len(rows)==3
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
a=(p/'src/DiophantineConsistency/Norm38MacroPKPaths.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroA0Value.lean').read_text();path=(p/'src/DiophantineConsistency/Norm38MacroA0Path.lean').read_text()
for x in ['PrefixPath d22 d27','PrefixPath d23 d27','(i : Fin 22)','(i : Fin 23)']:assert x in a
assert a.count('PrefixPath.step')==9 and a.count('Dag.snoc')==9
for x in ['d35_P_carry','d35_K_carry','lookup22_27','lookup23_27','d22_P_value','d23_K_value','prefix_A0','rw [hiP, hiK, d35_P_value, d35_K_value]']:assert x in v
for x in ['PrefixPath d36 d41','lookup36_41 a','d36_A0_value a']:assert x in path
assert path.count('PrefixPath.step')==5 and path.count('Dag.snoc')==5
lhs=v.split('theorem d36_A0_value',1)[1].split(':= by',1)[0].split('=',1)[1];rhs=path.split('theorem d41_A0_value',1)[1].split(':= by',1)[0].split('=',1)[1];assert ''.join(lhs.split())==''.join(rhs.split())
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d36 : Dag 36 := .snoc d35 (.add (.mul (.sub (.pow (.ref ⟨21, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨22, by decide⟩) (.lit 2))) (.constant (1 : Int)))' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=900);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'symbolic A0 checkpoint with opaque d11 rank; no Lean replay'},indent=2,sort_keys=True))
