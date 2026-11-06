#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent02-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'7da668b8830ca460b9a9d1245cad50e8417ef41477953425faa5eb28403db2fa','provider_preflight.py':'2f5e6e2be96948867b5b6a53732860a4720dac5299d0765328bab94497c0f92f','source-manifest.json':'5c9d066fd10c4912a0a80394f19e987ab5f7600ef485b248db03813c4377656a'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDependentM','be513db9d34caa379a6b6e8d82132bb7cc160eda825ff0d08f42c1dc471db4cd','Norm38MacroDependentY',['d20_R_carry','prefix_M']),('Norm38MacroDependentP','9269263c385f49d15b17ea935a29c1f9ef29887526a7c8f6ac26150da233085d','Norm38MacroDependentM',['d21_U_carry','prefix_P']),('Norm38MacroDependentK','edcdeb31d604966e84461cf1b5fa466383c49392040ebb915a6551eaf07e5498','Norm38MacroDependentP',['d22_R_carry','d22_h_carry','prefix_K'])];assert len(rows)==3
for row,(n,sha,imp,ts) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
named=(d/'research/nine-seed38-jones-named-prefix-draft/Norm38MacroPrefixes.lean').read_text();lines=named.splitlines();expected_nodes=['def d21 : Dag 21 := .snoc d20 (.mul (.ref ⟨10, by decide⟩) (.ref ⟨19, by decide⟩))','def d22 : Dag 22 := .snoc d21 (.mul (.mul (.constant (2 : Int)) (.pow (.ref ⟨20, by decide⟩) (.lit 2))) (.ref ⟨18, by decide⟩))','def d23 : Dag 23 := .snoc d22 (.add (.add (.ref ⟨10, by decide⟩) (.constant (1 : Int))) (.mul (.ref ⟨11, by decide⟩) (.sub (.ref ⟨21, by decide⟩) (.constant (1 : Int)))))'];assert all(x in lines for x in expected_nodes)
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==3
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled M/P/K prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
