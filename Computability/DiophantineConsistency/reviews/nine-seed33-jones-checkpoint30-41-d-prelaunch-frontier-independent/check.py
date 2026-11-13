#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint30-41-d-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'aeedfdc389465190d0ada74cd885af0ed2ab0609c5a9985dfebd7fb83991cfb5','source-manifest.json':'f0688217048b61edf2d745c87396f50c6d181ea2626cc1b7fad0b5c739a56e18','values-survey.py':'20c0e83fdb5df7793547cc84aa549c0645accab4f43491eadc17a34c66ab10b7'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['DValue','DPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint30-41-d-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint30-41-d-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d29_A_from_d27','d30_D_value','prefix_D','⟨23, by decide⟩ : Fin 29','⟨26, by decide⟩ : Fin 29','d29_A_from_d27, d29_C_carry, d27_A_value, d27_C_value','5 ^ 34']);statement=b.split('theorem path30_34 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path30_34 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==4 and proof.count('PrefixPath.step')==4 and '(i : Fin 30)' in b
assert all(x in b for x in ['d41_D_value','lookup34_41','lookup30_34','d30_D_value','Fin.last 29'])
up=D/'reviews/nine-seed33-jones-checkpoint29-41-q-terminal-frontier-independent/check.py';assert H(up)=='a8c8746ca9abb84c0d9d0f18f6db85145d862a68be849793a19cd9ce1dabe15f';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'D=(A²−1)C²+1 at d30 and carried to d41, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
