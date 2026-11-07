#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint28-41-j-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'36cf7a0098033d89fa13b00e73fa7d942840f8b9665997ad9945dea6114c10aa','source-manifest.json':'b1ed62546e6bda115adf3b1eccd40ad8e93741040cd2f93bded93cb8a9579ab5','values-survey.py':'538848badb990f0b037d0b5c788db5cebe1e9671ad036f3ded483778ae9caa3c'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['JValue','JPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint28-41-j-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint28-41-j-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d28_J_value','prefix_J','⟨23, by decide⟩ : Fin 27','d27_A_value','((4 : Int) : R)','((5 : Int) : R)','5 ^ 34']);statement=b.split('theorem path28_34 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path28_34 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==6 and proof.count('PrefixPath.step')==6 and '(i : Fin 28)' in b
assert all(x in b for x in ['d41_J_value','lookup34_41','lookup28_34','d28_J_value','Fin.last 27'])
up=D/'reviews/nine-seed33-jones-checkpoint24-27-a-terminal-frontier-independent/check.py';assert H(up)=='8d524a4ea8e64118dc49758df0eb14ba59217f3942b352cdd214870efbc82d92';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'J=4A−5 at d28 and carried to d41, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
