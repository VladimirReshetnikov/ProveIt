#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent06-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'f7a3596b73f59d077e54386c01e611394d82af8a381fce47d4cc33d677640acf','provider_preflight.py':'9fd536b830ad86e09f126dd50692ab3d9804e7225e2102306676a97e60451e54','source-manifest.json':'c6164eeb03cd42108e989c0c5ca769b0d28b0d4903b69fe6af63bb52cdf7a872'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDependentJcarry','5e864344f5860ee5bd75714b659e7ab98c3612bbb1b24518a111a74ef58dab14','Norm38MacroDependentF',['d25_j_carry']),('Norm38MacroDependentGprime','c8d711411765540c03e40c2b4f63d42c2d3869bf172c9d77e7ee60b1a6a5e103','Norm38MacroDependentJcarry',['d32_A_carry','d32_C_carry','d32_D_carry','prefix_Gprime']),('Norm38MacroDependentHcarry','ffb70f75f4a4dee7ba85515ad2390c27523bb9eb44e25de15a456984de41e577','Norm38MacroDependentGprime',['d33_j_carry','d33_Bprime_carry']),('Norm38MacroDependentH','3e6b8036faeb1bfd631ebc3439868f7e9ed332920edf38c7898e8df8e993fad9','Norm38MacroDependentHcarry',['d33_C_carry','prefix_H'])];assert len(rows)==4
for row,(n,sha,imp,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
G=(p/'src/DiophantineConsistency/Norm38MacroDependentGprime.lean').read_text();H=(p/'src/DiophantineConsistency/Norm38MacroDependentH.lean').read_text()
assert 'd32.values a ⟨23, by decide⟩ +' in G and 'd32.values a ⟨31, by decide⟩ * (d32.values a ⟨26, by decide⟩ *' in G and 'd32.values a ⟨29, by decide⟩ + ((1 : Int) : R) - d32.values a ⟨23, by decide⟩' in G
assert 'd33.values a ⟨24, by decide⟩ +' in H and 'd33.values a ⟨16, by decide⟩ * d33.values a ⟨26, by decide⟩' in H
named=(d/'research/nine-seed38-jones-named-prefix-draft/Norm38MacroPrefixes.lean').read_text();lines=named.splitlines();expected_nodes=['def d33 : Dag 33 := .snoc d32 (.add (.ref ⟨23, by decide⟩) (.mul (.ref ⟨31, by decide⟩) (.sub (.add (.mul (.ref ⟨26, by decide⟩) (.ref ⟨29, by decide⟩)) (.constant (1 : Int))) (.ref ⟨23, by decide⟩))))','def d34 : Dag 34 := .snoc d33 (.add (.ref ⟨24, by decide⟩) (.mul (.ref ⟨16, by decide⟩) (.ref ⟨26, by decide⟩)))'];assert all(x in lines for x in expected_nodes)
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==4
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled Gprime/H prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
