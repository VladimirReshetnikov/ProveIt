#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint40-41-bdcd-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ca935170c5c323d99a73e8114d4c477542f473731e2e7614761fb0697618b09c','provider_preflight.py':'665c7f722aa7661c0567ff56d8bd3da441eb63b4c77a02f8b48d7d0322e067b9','source-manifest.json':'1f7d0616a876c0aa48cf2ba1a15f246f87d1bd187f804da36c0d7782b0cbbea8'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];expect=[('Norm38MacroBdCdPaths','c6a94c2fd8de8ba867e19584545f81c603e18f0a85e838a8f1be5b19e7784a4e',['Norm38MacroV1Value','Norm38MacroCheckpoint27to34','Norm38MacroCheckpoint34to41'],['lookup39_41','lookup40_41','d41_C_value']),('Norm38MacroBdValue','5e940e74c66e180d39493ea872279676628087f802cb4f792a0f7e7c56d18a4d',['Norm38MacroBdCdPaths','Norm38MacroDependentBdCd'],['d40_Bd_value']),('Norm38MacroCdValue','b715d04d238e6b4ab467764120749e64b06fa8c93baedad9c9541e2c56519b36',['Norm38MacroBdValue'],['d41_Cd_value'])];assert len(rows)==3
for r,(n,h,im,ts) in zip(rows,expect):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n
 assert re.findall(r'^import ([\w.]+)$',s,re.M)==r['imports']==['DiophantineConsistency.'+x for x in im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==ts and re.findall(r'^#print axioms (\w+)',s,re.M)==ts
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
def rhs(p,n):return ''.join(p.read_text().split('theorem '+n,1)[1].split(':= by',1)[0].split('=',1)[1].split())
vals=[]
for f,n in [('checkpoint28-41-j-check','J'),('checkpoint29-41-q-check','Q'),('checkpoint32-41-f-check','F'),('checkpoint34-41-h-check','H')]:
 p=D/f'research/nine-seed38-jones-{f}/src/DiophantineConsistency/Norm38Macro{n}Path.lean';vals.append((n,rhs(p,f'd41_{n}_value')))
p=D/'research/nine-seed38-jones-checkpoint26-27-c-check/src/DiophantineConsistency/Norm38MacroCValue.lean';vals.append(('C',rhs(p,'d27_C_value')))
for n,t,want in [('Norm38MacroBdValue','d40_Bd_value','((J)*(F))^(2:Nat)'),('Norm38MacroCdValue','d41_Cd_value','((Q)*(F)+(J)*((H)-(C)))^(2:Nat)')]:
 v=rhs(P/'src/DiophantineConsistency'/f'{n}.lean',t)
 for k,x in sorted(vals,key=lambda z:-len(z[1])):v=v.replace(x,k)
 assert v==want
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d40 : Dag 40 := .snoc d39 (.pow (.mul (.ref ⟨27, by decide⟩) (.ref ⟨31, by decide⟩)) (.lit 2))' in nodes
assert 'def d41 : Dag 41 := .snoc d40 (.pow (.add (.mul (.ref ⟨28, by decide⟩) (.ref ⟨31, by decide⟩)) (.mul (.ref ⟨27, by decide⟩) (.sub (.ref ⟨33, by decide⟩) (.ref ⟨26, by decide⟩)))) (.lit 2))' in nodes
p=(P/'src/DiophantineConsistency/Norm38MacroBdCdPaths.lean').read_text();assert 'PrefixPath d39 d41' in p and 'PrefixPath d40 d41' in p and 'lookup27_34' in p and 'lookup34_41' in p
print(json.dumps({'status':'PASS_STATIC','scope':'Bd=(J*F)^2 and Cd=(Q*F+J*(H-C))^2 with short prefix lookups; no Lean or full-output claim'},indent=2,sort_keys=True))
