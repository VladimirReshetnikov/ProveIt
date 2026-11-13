#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint36-41-a0-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'e0665fb48b916a29fc1b9d722256d46052e6bcf8e51bbd52a262a076d52d4fa8','source-manifest.json':'edde39c59ae0bdaf18c994cd7f6a1c52abd6edb4e97f34d5025461a0d8e8129e','values-survey.py':'631a0e5edb7ec827274c9f904e0f3c9c81c6fe0f53a682f4e509427367081c54'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==3;ss=[]
for suffix,e in zip(['PKPaths','A0Value','A0Path'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint36-41-a0-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint36-41-a0-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b,c=ss
for name,steps in [('path22_27',5),('path23_27',4)]:
 st=a.split('theorem '+name+' ',1)[1].split(':= by',1)[0];pr=a.split('theorem '+name+' ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert st.count('.castSucc')==steps and pr.count('PrefixPath.step')==steps
assert all(x in b for x in ['d35_P_value','d35_K_value','d36_A0_value','prefix_A0','⟨21, by decide⟩ : Fin 35','⟨22, by decide⟩ : Fin 35','rw [hiP, hiK, d35_P_value, d35_K_value]'])
st=c.split('theorem path36_41 ',1)[1].split(':= by',1)[0];pr=c.split('theorem path36_41 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert st.count('.castSucc')==5 and pr.count('PrefixPath.step')==5 and all(x in c for x in ['lookup36_41','d41_A0_value','d36_A0_value a'])
up=D/'reviews/nine-seed33-jones-checkpoint22-23-pk-terminal-frontier-independent/check.py';assert H(up)=='7750fb217a5ab3eb62c56d17dbe0fec634126909a63f79103b4455676c85c862';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'P/K paths and symbolic A0 d36/d41 only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
