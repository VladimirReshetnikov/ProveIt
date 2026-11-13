#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint34-41-h-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'aef426e38733a4964df7ebdb3e2de6ef752dd663658abfa42501c5a74f1b33d2','source-manifest.json':'cb6c06a0ea21d6a72b4175a58a5187af87ac6ffc274dfb78ec2cb5376648b986','values-survey.py':'f141dd8862bc86e8ac73b13da720dc0dc8f1248389f68a815b58dc4a5392b3c8'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['HValue','HPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint34-41-h-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint34-41-h-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d33_j_value','d33_Bprime_value','d34_H_value','prefix_H','⟨24, by decide⟩ : Fin 33','⟨16, by decide⟩ : Fin 33','⟨26, by decide⟩ : Fin 33','d33_Bprime_value, d33_j_value, d33_C_carry, d27_C_value']);assert all(x in b for x in ['d41_H_value','lookup34_41 a (Fin.last 33)','d34_H_value a'])
up=D/'reviews/nine-seed33-jones-checkpoint33-41-gprime-terminal-frontier-independent/check.py';assert H(up)=='e9f0341efd830145bc7efcc2d1a15ea9358c9c5aa14ec47b0666657b7f480d15';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'H=Bprime+j*(Bprime+C) at d34 and carried to d41; rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
