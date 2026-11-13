#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint34-41-h-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'edf34f36d2666d1e2751fc05954c0cf6bdbf134a9df0d1e6af98ba54196c9f40','provider_preflight.py':'c857ac5dcea73d072baf3e5767b329b958cb0c3c1f8928b6e12e3339509b5b1c','source-manifest.json':'19e953aaad381236b9c3632534751303526e99969fdae16f3b87095597b6da3c'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroHValue','38c4fe586e7402168a26593eac5748b07f01a2b2053bc7587c61a52698f9e04e',['Norm38MacroGprimePath','Norm38MacroDependentH','Norm38MacroLive18Group04','Norm38MacroPrefixInputsB'],['d33_j_value','d33_Bprime_value','d34_H_value']),('Norm38MacroHPath','b149c812956a3bcd8cfd4cae5bd87ab7d1c2e8936dd0fc1d53477d2cdf2fa49c',['Norm38MacroHValue','Norm38MacroCheckpoint34to41'],['d41_H_value'])];assert len(rows)==2
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
path=(p/'src/DiophantineConsistency/Norm38MacroHPath.lean').read_text();v=(p/'src/DiophantineConsistency/Norm38MacroHValue.lean').read_text()
for x in ['prefix_H','d33_Bprime_value, d33_j_value, d33_C_carry, d27_C_value','d33_j_carry, d25_j_carry, d18_j_carry, Norm38MacroPrefixGroup04.prefix_j','d11.values a (Fin.last 10)']:assert x in v
for x in ['lookup34_41 a','d34_H_value a','d11.values a (Fin.last 10)']:assert x in path
lhs=v.split('theorem d34_H_value',1)[1].split(':= by',1)[0].split('=',1)[1];rhs=path.split('theorem d41_H_value',1)[1].split(':= by',1)[0].split('=',1)[1];assert ''.join(lhs.split())==''.join(rhs.split())
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d34 : Dag 34 := .snoc d33 (.add (.ref ⟨24, by decide⟩) (.mul (.ref ⟨16, by decide⟩) (.ref ⟨26, by decide⟩)))' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'d41 H source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
