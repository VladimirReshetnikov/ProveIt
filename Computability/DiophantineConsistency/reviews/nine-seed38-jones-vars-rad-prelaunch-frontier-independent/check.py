#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-rad-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'1e2a86647e018c8b21734f8603296cdb9c771f7bf253895f75708382dad2e2a0','provider_preflight.py':'8cfb88efcc47e8e56129cf0dfb25a7a8a40facb5c4a50410ca6f3e21ded8d900','source-manifest.json':'bcffaad7abea1584fd47239c483bc6934294e1e37fc02c082d9876b631119dd0'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];want=[('Norm38MacroVarsRad0','15b8415073861f7ff7f32a25804fcc3c8c22163aa710bccc633d04dfaf7036c7','Norm38MacroVarsCd','d41_A0_eq_rad0',35),('Norm38MacroVarsRad1','402cdf6d0bde2f0f0cbb14e28942a92f2ed50aa48b03c7465a1d54de8d221c5a','Norm38MacroVarsRad0','d41_A1_eq_rad1',36)];assert len(rows)==2
for i,(r,(n,h,im,t,index)) in enumerate(zip(rows,want)):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and r['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==[t]==re.findall(r'^#print axioms (\w+)',s,re.M)
 assert f'd41.values a ⟨{index}, by decide⟩ = (vars a).rad {i}' in s and f'd41_A{i}_value' in s and 'Int.cast_one' in s
 if i==0:assert '((vars a).P ^ 2 - 1) * (vars a).K ^ 2 + 1' in s
 else:assert '(vars a).D * (vars a).F * (vars a).I' in s
core=(D/'Lean/DiophantineConsistency/JonesSyntaxCore.lean').read_text();assert 'def rad : Fin 2 → R := ![(v.P ^ 2 - 1) * v.K ^ 2 + 1, v.D * v.F * v.I]' in core
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d36 : Dag 36 := .snoc d35 (.add (.mul (.sub (.pow (.ref ⟨21, by decide⟩) (.lit 2)) (.constant (1 : Int))) (.pow (.ref ⟨22, by decide⟩) (.lit 2))) (.constant (1 : Int)))' in nodes and 'def d37 : Dag 37 := .snoc d36 (.mul (.mul (.ref ⟨29, by decide⟩) (.ref ⟨31, by decide⟩)) (.ref ⟨34, by decide⟩))' in nodes
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'symbolic A0/A1 = vars.rad 0/1 only; no Lean or named-formula equality'},indent=2,sort_keys=True))
