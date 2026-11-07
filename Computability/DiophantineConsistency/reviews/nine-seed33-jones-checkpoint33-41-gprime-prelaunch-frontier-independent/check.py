#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint33-41-gprime-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'2497374e9b1756deb436cf09027245866c652e9b64b482b518e8c5d33c4450ba','source-manifest.json':'e60ff667f610af20df69137030ef927084b051c9b350bf39400d6fc725c1fbaa','values-survey.py':'c6f9cc6119e4018a1a14e28a55ce42439be77be4c2bea62a9ae98b9f964cbaea'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['GprimeValue','GprimePath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint33-41-gprime-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint33-41-gprime-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d32_A_value','d33_Gprime_value','prefix_Gprime','⟨23, by decide⟩ : Fin 32','⟨31, by decide⟩ : Fin 32','⟨26, by decide⟩ : Fin 32','⟨29, by decide⟩ : Fin 32','d32_A_value, d32_F_value, d32_C_carry, d32_D_carry, d27_C_value, d30_D_value']);statement=b.split('theorem path33_34 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path33_34 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==1 and proof.count('PrefixPath.step')==1 and '(i : Fin 33)' in b
assert all(x in b for x in ['d41_Gprime_value','lookup34_41','lookup33_34','d33_Gprime_value','Fin.last 32'])
up=D/'reviews/nine-seed33-jones-checkpoint32-41-f-terminal-frontier-independent/check.py';assert H(up)=='17a85a79deb8593bbd52aae352e9d47437af2b9fa56eac85e2604951234e0a9b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'Gprime=A+F(CD+1−A) at d33 and carried to d41, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
