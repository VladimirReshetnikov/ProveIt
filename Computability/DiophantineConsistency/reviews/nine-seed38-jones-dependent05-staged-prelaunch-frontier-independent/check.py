#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent05-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'3256098836dea5f7cf2efcc8571b58c5f80ec576b6e5c7a561d3a56df8559ae4','provider_preflight.py':'fae07b0a7ad7f9bc0be9f7c72157d218a5132c51d2ccd3a8f7e1319a15afc6b7','source-manifest.json':'44d2ba4777407650001e225e70ffbc5f69d24269fca2940f618f5d94345590ae'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDependentIcarry','7fcdddc9b330d21af36451580d0ae84071b9f60d7599bb5e08f3c3a777d26d93','Norm38MacroDependentD',['d24_i_carry']),('Norm38MacroDependentE','fbf201b90ba60749ab0296f78fb187934b5abc254c0f364b839965b23dbdbdfc','Norm38MacroDependentIcarry',['d30_i_carry','d30_J_carry','d30_C_carry','prefix_E']),('Norm38MacroDependentF','092e73eb39f9bd08c4e21ee0b82fe0fcc85ceb18cd5f2bab7505c87f2d3aa79e','Norm38MacroDependentE',['d31_A_carry','prefix_F'])];assert len(rows)==3
for row,(n,sha,imp,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
E=(p/'src/DiophantineConsistency/Norm38MacroDependentE.lean').read_text();F=(p/'src/DiophantineConsistency/Norm38MacroDependentF.lean').read_text()
assert 'd30.values a ⟨15, by decide⟩ * d30.values a ⟨27, by decide⟩ *' in E and 'd30.values a ⟨29, by decide⟩ * (d30.values a ⟨26, by decide⟩) ^ (2 : Nat)' in E
assert 'd31.values a ⟨23, by decide⟩) ^ (2 : Nat)' in F and 'd31.values a ⟨30, by decide⟩) ^ (2 : Nat)' in F
named=(d/'research/nine-seed38-jones-named-prefix-draft/Norm38MacroPrefixes.lean').read_text();lines=named.splitlines();expected_nodes=['def d31 : Dag 31 := .snoc d30 (.mul (.mul (.mul (.ref ⟨15, by decide⟩) (.ref ⟨27, by decide⟩)) (.ref ⟨29, by decide⟩)) (.pow (.ref ⟨26, by decide⟩) (.lit 2)))','def d32 : Dag 32 := .snoc d31 (.add (.mul (.sub (.pow (.ref ⟨23, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨30, by decide⟩) (.lit 2))) (.constant (1 : Int)))'];assert all(x in lines for x in expected_nodes)
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled E/F prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
