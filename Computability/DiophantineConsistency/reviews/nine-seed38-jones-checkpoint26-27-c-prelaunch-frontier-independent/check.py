#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint26-27-c-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'0d8903c8281e24f21d7a0da6604ce691c253c54e8adede4af224f6989fcd6129','provider_preflight.py':'d380f02bd217a9a57f056696376fb2bf3b28f27dc0619a32b32d1853e35cf71b','source-manifest.json':'839596518187d1a05fa44550337dbe701428bdba19cbe99feccd21472f051fc0'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroCInputs','c437c72394fcd4f78e5fc2d354e43e2b68bb4ea2088f88e8f9407d649003739c',['Norm38MacroJPath','Norm38MacroLive18Group01','Norm38MacroLive18Group03','Norm38MacroPrefixInputsB','Norm38MacroPrefixGlarge'],['d18_b_value','d18_phi_value']),('Norm38MacroCBW','0e08969e782a06ad9aa4b1d7750e8a60d035a1c83564dc32efe2e5c338c4258c',['Norm38MacroCInputs','Norm38MacroDependentW','Norm38MacroLive18Group02','Norm38MacroUYInputs'],['d26_Bprime_value','d26_W_value']),('Norm38MacroCValue','230c3642fbf7a9b36a1a45dd887ab4a20c734ad5e9cff4709c990e93276a85cb',['Norm38MacroCBW','Norm38MacroDependentC'],['d27_C_value'])];assert len(rows)==3
for row,(n,h,imports,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
i=(p/'src/DiophantineConsistency/Norm38MacroCInputs.lean').read_text();bw=(p/'src/DiophantineConsistency/Norm38MacroCBW.lean').read_text();c=(p/'src/DiophantineConsistency/Norm38MacroCValue.lean').read_text()
for x in ['d18_b_carry a','d9_b a','d18_phi_carry a','prefix_phi a']:assert x in i
for x in ['prefix_Bprime a','d24_R_carry, d18_R_carry','prefix_W','d25_b_carry, d25_w_carry, d18_b_value, d18_w_value','((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)','base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))']:assert x in bw
for x in ['prefix_C','d26_Bprime_value, d26_W_value, d26_phi_carry, d18_phi_value','a ⟨5, by decide⟩']:assert x in c
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d27 : Dag 27 := .snoc d26 ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'d27 C source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
