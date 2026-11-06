#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint20-27-uy-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'3ec115e548ab360c9f325eb6329c1d84d77789080f496bd20088c2ec49efadb7','provider_preflight.py':'c77142b6c18a5587ad494014b9b44e6c781e3cbcca5aa937bdc4b7c191d6448f','source-manifest.json':'90bba579de38156f2e710d1e2a889b226936924e1a90519aaeb7b41fcb5b0732'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroUYInputs','091748e2df9a1dfc57fe7f8cbbcbbd05eb0e3b897c9c47018d88e801a20f3638',['Norm38MacroCheckpoint41to45','Norm38MacroLive18Group01','Norm38MacroLive18Group03','Norm38MacroPrefixInputsA','Norm38MacroPrefixQNCarry'],['d18_N_value','d18_s_value','d18_w_value']),('Norm38MacroUYPath','6a7c59a748175f3f2de5b4caac2e5e25b4b050490fcfb59c9d06d2fdaefafeb8',['Norm38MacroUYInputs'],['path20_27','lookup20_27']),('Norm38MacroUYValues','26a2652103e1bae571844c29f7cbfb0e27819cc3add1bf57e20a6ff837c88c14',['Norm38MacroUYPath','Norm38MacroDependentY'],['d27_U_value','d27_Y_value'])];assert len(rows)==3
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
i=(p/'src/DiophantineConsistency/Norm38MacroUYInputs.lean').read_text();path=(p/'src/DiophantineConsistency/Norm38MacroUYPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroUYValues.lean').read_text()
for x in ['d18_N_carry a','d10_N a','d18_s_carry a','prefix_s a','d18_w_carry a','prefix_w a','((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)']:assert x in i
assert 'PrefixPath d20 d27' in path and path.count('PrefixPath.step')==7 and path.count('Dag.snoc')==7
for x in ['lookup20_27','prefix_U a','prefix_Y a','d18_N_value, d18_w_value','d18_N_value, d18_s_value','a ⟨4, by decide⟩','a ⟨3, by decide⟩']:assert x in v
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(21,28):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'d27 U/Y source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
