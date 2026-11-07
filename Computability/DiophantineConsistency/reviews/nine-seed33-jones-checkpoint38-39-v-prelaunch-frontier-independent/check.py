#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint38-39-v-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'81c81209fefd1bad01a1f49f5e870ed3620acecca10b36ad1b04e7eb9be0c65b','source-manifest.json':'c7b0fe13f47aafb5b1fe11375781c4f49936f255b4b1d0b942ab72075e2d9393','values-survey.py':'124dc621e2dbe561a16d44483f0ba2fdc2a6eb7a204d28c5017b9307e8dd1535'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['V0Value','V1Value'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint38-39-v-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint38-39-v-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d38_V0_value','prefix_V0','⟨35, by decide⟩ : Fin 37','d37_A0_carry, d36_A0_value']);assert all(x in b for x in ['d39_V1_value','prefix_V1','⟨36, by decide⟩ : Fin 38','d38_A1_carry, d37_A1_value'])
up=D/'reviews/nine-seed33-jones-checkpoint37-41-a1-terminal-frontier-independent/check.py';assert H(up)=='6f7ddff2156a7e4d937d4228c0f4a333fb0659d5f929fbee2d49878e3353f7dd';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic V0 d38 and V1 d39 only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
