#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint29-41-q-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'ceee06de03cbf50e818009b19916cb1467406c362f17edfb7a5142c9400cbe81','source-manifest.json':'38b2917a68fb0b582ace2f15a545a635879c93641daf01bf19abb3b0bbfd2056','values-survey.py':'af012706c5255e541a172d5d707f19f2a8cb2539667ccd01ef460884f166ba85'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['QValue','QPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint29-41-q-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint29-41-q-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d29_Q_value','prefix_Q','⟨25, by decide⟩ : Fin 28','⟨26, by decide⟩ : Fin 28','d28_W_carry, d28_C_carry, d26_W_value, d27_C_value','((3 : Int) : R)','((2 : Int) : R)']);statement=b.split('theorem path29_34 ',1)[1].split(':= by',1)[0];proof=b.split('theorem path29_34 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==5 and proof.count('PrefixPath.step')==5 and '(i : Fin 29)' in b
assert all(x in b for x in ['d41_Q_value','lookup34_41','lookup29_34','d29_Q_value','Fin.last 28'])
up=D/'reviews/nine-seed33-jones-checkpoint26-27-c-terminal-frontier-independent/check.py';assert H(up)=='7a3f2f1374387246c434d048cb451dc999664387ee830048728a696b768097be';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'Q=3WC−2(W²−1) at d29 and carried to d41, rank opaque; no output semantics or Lean replay'},sort_keys=True,indent=2))
