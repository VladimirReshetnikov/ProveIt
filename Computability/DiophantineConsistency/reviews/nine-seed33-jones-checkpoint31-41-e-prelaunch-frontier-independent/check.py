#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint31-41-e-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6221d32b9819cd10d90c1b1ec3e913cc042d482b1391a3e55e0ec9c1201c9ba8','source-manifest.json':'26238b5df161f2818223d1a8976dc36b3b46c6cfd3eeae5eae69058018aed420','values-survey.py':'cc6aa0bd788075a3070e2093d7b704c8db3ab3700aabfd928ca604bc43b32f0e'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['EValue','EPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint31-41-e-retry01/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint31-41-e-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d30_i_value','d31_E_value','Sign33MacroPrefixGroup04.prefix_i','prefix_E','⟨15, by decide⟩ : Fin 30','⟨27, by decide⟩ : Fin 30','⟨29, by decide⟩ : Fin 30','⟨26, by decide⟩ : Fin 30','d30_i_value, d30_J_carry, d30_C_carry, d28_J_value, d30_D_value, d27_C_value']);statement=b.split('theorem path31_34 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path31_34 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==3 and proof.count('PrefixPath.step')==3 and '(i : Fin 31)' in b
assert all(x in b for x in ['d41_E_value','lookup34_41','lookup31_34','d31_E_value','Fin.last 30'])
up=D/'reviews/nine-seed33-jones-checkpoint30-41-d-terminal-frontier-independent/check.py';assert H(up)=='fa5394913755ce7df8c8d4d5ab5af007546eb24a703e9a042540f939da9d6185';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'E=i·J·D·C² at d31 and carried to d41, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
