#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint42-dm-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'fcdec63095f78da4ad4e6f44b64d062634d04d4165b9bd317b6ce5ba4e96bea6','provider_preflight.py':'ce29de1cdbe88a95c34499fd85a28bf1796aa5ab1068ca6708223153a12b0555','source-manifest.json':'d30d9b9366b48152267239e7dd51fad446cc62af32e1e44ed602e1900701ab75'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDmInputs','06d62b29d3c043dab0b50c94953774d5a53358af62709c09100748533f86dfca',['Norm38MacroCdValue','Norm38MacroCheckpoint41to45'],['d41_K_value','d41_Y_value']),('Norm38MacroDmValue','f10360f9d27362cfb8c4ae8c0f17f760c6e1316084508862af01607f982b1e9b',['Norm38MacroDmInputs','Norm38MacroDependentDmKc'],['d42_Dm_value'])];assert len(rows)==2
for r,(n,h,im,ts) in zip(rows,expected):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n and re.findall(r'^import ([\w.]+)$',s,re.M)==r['imports']==['DiophantineConsistency.'+x for x in im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==ts==re.findall(r'^#print axioms (\w+)',s,re.M)
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
def rhs(p,n):return ''.join(p.read_text().split('theorem '+n,1)[1].split(':= by',1)[0].split('=',1)[1].split())
inputs=P/'src/DiophantineConsistency/Norm38MacroDmInputs.lean'
for k,prior,theorem in [('K','checkpoint22-23-pk-check/src/DiophantineConsistency/Norm38MacroKValue.lean','d23_K_value'),('Y','checkpoint20-27-uy-check/src/DiophantineConsistency/Norm38MacroUYValues.lean','d27_Y_value')]:assert rhs(inputs,f'd41_{k}_value')==rhs(D/f'research/nine-seed38-jones-{prior}',theorem)
vals=[]
for k,p in [('K',inputs),('Y',inputs),('C',D/'research/nine-seed38-jones-checkpoint40-41-bdcd-check/src/DiophantineConsistency/Norm38MacroBdCdPaths.lean'),('g',D/'research/nine-seed38-jones-checkpoint41-45-check/src/DiophantineConsistency/Norm38MacroCheckpoint41to45.lean'),('G',D/'research/nine-seed38-jones-checkpoint41-45-check/src/DiophantineConsistency/Norm38MacroCheckpoint41to45.lean')]:vals.append((k,rhs(p,f'd41_{k}_value')))
v=rhs(P/'src/DiophantineConsistency/Norm38MacroDmValue.lean','d42_Dm_value')
for k,x in sorted(vals,key=lambda z:-len(z[1])):v=v.replace(x,k)
assert v=='(K)^(2:Nat)*(G)-((4:Int):R)*((C)-(K)*(Y))^(2:Nat)*(G)-((8:Int):R)*(g)*(K)^(2:Nat)'
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text();assert 'def d42 : Dag 42 := .snoc d41 (.sub (.sub (.mul (.pow (.ref ⟨22, by decide⟩) (.lit 2)) (.ref ⟨9, by decide⟩)) (.mul (.mul (.constant (4 : Int)) (.pow (.sub (.ref ⟨26, by decide⟩) (.mul (.ref ⟨22, by decide⟩) (.ref ⟨19, by decide⟩))) (.lit 2))) (.ref ⟨9, by decide⟩))) (.mul (.mul (.constant (8 : Int)) (.ref ⟨7, by decide⟩)) (.pow (.ref ⟨22, by decide⟩) (.lit 2))))' in nodes
print(json.dumps({'status':'PASS_STATIC','scope':'short-prefix Dm=K²G−4(C−KY)²G−8gK² with symbolic inputs; no Lean or full-output claim'},indent=2,sort_keys=True))
