#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-checkpoint38-39-v-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'99f864dd5ddb181240277fb1f97f639ab1d764c27071dc64e2ba3d85687fd5ef','provider_preflight.py':'67eaeafa9ec29b62b9a2ae2d14a4a94b8ec19d93fcc926db74e3a7eaced61c6b','source-manifest.json':'e32ca7d35dcea79f5012a1ac5cbe7c7844eda06eb24dbc318166f4516464223c'}.items():assert sha(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(rows)==2
def rhs(p,n):return ''.join(p.read_text().split('theorem '+n,1)[1].split(':= by',1)[0].split('=',1)[1].split())
for i,(r,h,im) in enumerate(zip(rows,['fa3a273626982de1411960918b2a4041684efd3e887fe7f6343e263d1c523154','970afa5a77f7c2e196c26da778a8645fb2946a019c68eae74c327625cb81bd1a'],[['Norm38MacroA1Path','Norm38MacroDependentV'],['Norm38MacroV0Value','Norm38MacroDependentV']])):
 n=f'Norm38MacroV{i}Value';p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();assert sha(p)==r['source_sha256']==h and r['module']=='DiophantineConsistency.'+n
 assert re.findall(r'^import ([\w.]+)$',s,re.M)==r['imports']==['DiophantineConsistency.'+x for x in im]
 assert re.findall(r'^theorem (\w+)',s,re.M)==[f'd{38+i}_V{i}_value']
 a=D/'research'/f'nine-seed38-jones-checkpoint3{6+i}-41-a{i}-check/src/DiophantineConsistency'/f'Norm38MacroA{i}Value.lean';av=rhs(a,f'd{36+i}_A{i}_value'); assert rhs(p,f'd{38+i}_V{i}_value').replace(av,'A')=='(A)^(2:Nat)+((2:Int):R)'
 assert f'd{37+i}_A{i}_carry' in s and f'd{36+i}_A{i}_value' in s and f'prefix_V{i}' in s
nodes=(D/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for i in [0,1]:assert f'def d{38+i} : Dag {38+i} := .snoc d{37+i} (.add (.pow (.ref ⟨{35+i}, by decide⟩) (.lit 2)) (.constant (2 : Int)))' in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=300,check=True);assert not r.stderr;pre=json.loads(r.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stage_count']==2
print(json.dumps({'status':'PASS_NO_LEAN','preflight':pre,'scope':'symbolic V0=(A0)^2+2 and V1=(A1)^2+2 at immediate prefixes, not full-output identity'},indent=2,sort_keys=True))
