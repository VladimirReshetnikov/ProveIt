#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint37-41-a1-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'fe9e43d862de849c377e446f5eaef425adf01052445030a3d777b3b50e46c208','source-manifest.json':'57338c0d0f20d20e985a8d62623d84d1bea4468c4ad94b909a9380b1124f268f','values-survey.py':'18f915a0541d3212d3baa6043c20a366a782274f210fd29d6a6701e5c860de64'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['A1Value','A1Path'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint37-41-a1-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint37-41-a1-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d37_A1_value','prefix_A1','⟨29, by decide⟩ : Fin 36','⟨31, by decide⟩ : Fin 36','⟨34, by decide⟩ : Fin 36','d36_D_carry, d36_F_carry, d36_I_carry, d30_D_value, d32_F_value, d35_I_value']);st=b.split('theorem path37_41 ',1)[1].split(':= by',1)[0];pr=b.split('theorem path37_41 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert st.count('.castSucc')==4 and pr.count('PrefixPath.step')==4 and all(x in b for x in ['lookup37_41','d41_A1_value','d37_A1_value a'])
up=D/'reviews/nine-seed33-jones-checkpoint36-41-a0-terminal-frontier-independent/check.py';assert H(up)=='9130ac2985209a82b48723044ce7f5529646212cd28c10738f55442d7228e6d7';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic A1 at d37 and d41; four-step d37→d41 path only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
