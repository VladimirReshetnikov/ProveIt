#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint32-41-f-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'79d9930e4240da3594b096d870534b98f01678035a6b30357733e66b4dd1193a','source-manifest.json':'a1ca479f610cc79654886d55821c2ada90d62fadf937ed9d4209c2820680ed29','values-survey.py':'4cec79f6d462ecfd78e9c22f8d2728e15870d6c312f927b9f8b7954de616af48'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['FValue','FPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint32-41-f-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint32-41-f-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d31_A_from_d29','d32_F_value','prefix_F','⟨23, by decide⟩ : Fin 31','⟨30, by decide⟩ : Fin 31','d31_A_from_d29, d29_A_from_d27, d27_A_value, d31_E_value','5 ^ 34']);statement=b.split('theorem path32_34 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path32_34 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==2 and proof.count('PrefixPath.step')==2 and '(i : Fin 32)' in b
assert all(x in b for x in ['d41_F_value','lookup34_41','lookup32_34','d32_F_value','Fin.last 31'])
up=D/'reviews/nine-seed33-jones-checkpoint31-41-e-terminal-frontier-independent/check.py';assert H(up)=='84c51316ab51223a4a30dc48d0e2ddc059d2119185aebc2e2ee203b2790ec426';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'F=(A²−1)E²+1 at d32 and carried to d41, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
