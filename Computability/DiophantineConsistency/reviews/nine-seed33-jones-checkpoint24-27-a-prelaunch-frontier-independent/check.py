#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint24-27-a-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'78592a7af12911d4247a1116a22944091cd681955eeeafd7f21548cd18a580de','source-manifest.json':'b79bc7f92778d82230b0cbc06d3694608bc28afc7eb106a8f2aa8c30a81fd141','values-survey.py':'9ad91d867775251befcccc0208506cf2d4aa3f569c83f0155d400ff3ed3d85b7'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];ss=[]
for suffix,e in zip(['APath','AValue'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint24-27-a-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint24-27-a-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;statement=a.split('theorem path24_27 ',1)[1].split(':= by',1)[0];proof=a.split('theorem path24_27 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert statement.count('.castSucc')==3 and proof.count('PrefixPath.step')==3 and '(i : Fin 24)' in a
for x in ['d27_A_value','d11.values a (Fin.last 10)','d23.values a ⟨20, by decide⟩ * (d23.values a ⟨18, by decide⟩','d23_M_carry','d23_U_carry','lookup21_27','lookup20_27','d27_M_value, d27_U_value','prefix_A a','5 ^ 34']:assert x in b
up=D/'reviews/nine-seed33-jones-checkpoint21-27-m-terminal-frontier-independent/check.py';assert H(up)=='e5c0fa27c0ddf5604f2174210b5a37263327260ea1f85afbf014a9bc7c74b1ef';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'d27 A as checked M times (U+1), rank opaque, and d24→d27 lookup only; no output semantics or Lean replay'},sort_keys=True,indent=2))
