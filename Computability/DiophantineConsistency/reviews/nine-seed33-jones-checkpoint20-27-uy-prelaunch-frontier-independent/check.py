#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint20-27-uy-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'41cd5e6e1fad7b7dfadc3f5877cd905a9169717894a670b5e920a72aa10b401d','source-manifest.json':'3049d75278d3ff6a96371ba43915fb2f591a724730e08e04d6b047ea414117f1','values-survey.py':'8c492a917bd91ba257ad7c0fc77061ea9b6b887e852f11e16d965dd7fa461122'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['UYInputs','UYPath','UYValues'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint20-27-uy-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint20-27-uy-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34');ss.append(p.read_text())
a,b,c=ss
for x in ['d18_N_value','5 ^ 34','d18_N_carry','d10_N','d18_s_value','d18_w_value','a ⟨3, by decide⟩','a ⟨4, by decide⟩']:assert x in a
statement=b.split('theorem path20_27 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path20_27 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==7 and proof.count('PrefixPath.step')==7 and '(i : Fin 20)' in b
for x in ['d27_U_value','d27_Y_value','lookup20_27','prefix_U','prefix_Y','d18_N_value','d18_w_value','d18_s_value','5 ^ 34']:assert x in c
up=D/'reviews/nine-seed33-jones-checkpoints27-45-staged-terminal-frontier-independent/check.py';assert H(up)=='2d33d03b58de071f6c0a2b28afe041d708e07a1c1e850632cabe3e13fce92a66';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'d27 symbolic U/Y and d20→d27 lookup only; no output semantics or Lean replay'},sort_keys=True,indent=2))
