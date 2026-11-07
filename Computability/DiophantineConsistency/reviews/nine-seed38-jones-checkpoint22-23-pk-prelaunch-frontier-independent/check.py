#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-checkpoint22-23-pk-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'8ec1a17818078284a8e38bcf74973ad2eac9d5b1253aec10ad91bfe1802d7e80','provider_preflight.py':'125e2542c87f5bbe2ea29a6797dc9b65fcdc7f0b70da707eea9433e9b8eec4d4','source-manifest.json':'65a8ac625e988c787e5dceb8fdd63a2d037f06056b172984336e2fffc951c799'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroPValue','3dd46907a518cc86c3c5358c0fbfd39148c77ccbbc18cd3ae37accaa3edd4483',['Norm38MacroIPath','Norm38MacroDependentP'],'d22_P_value'),('Norm38MacroKValue','be84244546ef29c4859396e233f6a86137f7a8f14cf42da6dff6d61fc3deb036',['Norm38MacroPValue','Norm38MacroDependentK','Norm38MacroLive18Group02','Norm38MacroPrefixInputsA'],'d23_K_value')];assert len(rows)==2
for row,(n,h,imports,t) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports] and re.findall(r'^theorem (\w+)',s,re.M)==[t] and re.findall(r'^#print axioms (\w+)',s,re.M)==[t]
 for a,b,c in re.findall(r'd(\d+)\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s):assert int(a)==int(b)+1+c.count('.castSucc')
a=(p/'src/DiophantineConsistency/Norm38MacroPValue.lean').read_text();b=(p/'src/DiophantineConsistency/Norm38MacroKValue.lean').read_text()
for x in ['prefix_P','lookup21_27 a (Fin.last 20)','d27_M_value a','d21_U_carry','lookup20_27 a ((Fin.last 18).castSucc)','d27_U_value a','rw [hiM, hiU, hM, hU]']:assert x in a
for x in ['prefix_K','d22_R_carry, d18_R_carry, d22_h_carry, d18_h_carry, Norm38MacroPrefixGroup04.prefix_h, d22_P_value','d11.values a (Fin.last 10)','a ⟨2, by decide⟩']:assert x in b
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for x in ['def d22 : Dag 22 := .snoc d21 (.mul (.mul (.constant (2 : Int)) (.pow (.ref ⟨20, by decide⟩) (.lit 2))) (.ref ⟨18, by decide⟩))','def d23 : Dag 23 := .snoc d22 (.add (.add (.ref ⟨10, by decide⟩) (.constant (1 : Int))) (.mul (.ref ⟨11, by decide⟩) (.sub (.ref ⟨21, by decide⟩) (.constant (1 : Int)))))']:assert x in nodes
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=600);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'symbolic P/K local nodes with opaque d11 rank; no Lean replay'},indent=2,sort_keys=True))
