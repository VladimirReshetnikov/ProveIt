#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint21-27-m-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'64b935ceec156108b125dbb4dffb6f0b6f9cf47db3b2a0ca30c801c92a26e3af','source-manifest.json':'887f72d88768dd721e821ed04d46c17142876d46909ef3cfef8aec0207711097','values-survey.py':'5ae6cb060b4ef3be706915456fca7c0c949a0915b437cb4494ba23ae255cd3d7'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['MPath','MValue'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint21-27-m-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint21-27-m-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;statement=a.split('theorem path21_27 ',1)[1].split(':= by',1)[0];proof=a.split('theorem path21_27 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==6 and proof.count('PrefixPath.step')==6 and '(i : Fin 21)' in a
for x in ['d27_M_value','d11.values a (Fin.last 10)','d20.values a ⟨10, by decide⟩ * d20.values a ⟨19, by decide⟩','d20_R_carry, d18_R_carry','(lookup20_27 a (Fin.last 19)).symm.trans (d27_Y_value a)','prefix_M a','5 ^ 34']:assert x in b
up=D/'reviews/nine-seed33-jones-checkpoint20-27-uy-terminal-frontier-independent/check.py';assert H(up)=='499b586380e0a79fc23fef946781ef746757d3d90ce543dc7fb80051d8051ede';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'d27 M as opaque d11 rank times symbolic Y and d21→d27 lookup only; no output semantics or Lean replay'},sort_keys=True,indent=2))
