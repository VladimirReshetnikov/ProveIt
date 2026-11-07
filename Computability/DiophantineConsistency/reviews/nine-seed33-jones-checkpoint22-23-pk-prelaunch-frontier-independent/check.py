#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint22-23-pk-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9f35a26f501a9b3b680a985237b2481baf418c2d5df7663dbc06648ea1a6153c','source-manifest.json':'3fe82683cdbc2cfa4cb30dbe9062be1bb93dd2ec5d37845226c826e5291d40b1','values-survey.py':'e5800716957bfa510b22455806e36c19e1cd2eb3a292c1993f2b5c2691ca8d4d'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['PValue','KValue'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint22-23-pk-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint22-23-pk-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d22_P_value','prefix_P','⟨20, by decide⟩ : Fin 21','⟨18, by decide⟩ : Fin 21','rw [hiM, hiU, hM, hU]']);assert all(x in b for x in ['d23_K_value','prefix_K','⟨10, by decide⟩ : Fin 22','⟨11, by decide⟩ : Fin 22','⟨21, by decide⟩ : Fin 22','d22_P_value'])
up=D/'reviews/nine-seed33-jones-checkpoint35-41-i-terminal-frontier-independent/check.py';assert H(up)=='3b8dd8d5c2c68a084f00d7cdde8f2f08a76c7f08b4565a8aba50d48e73d340a2';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic P at d22 and K at d23 only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
