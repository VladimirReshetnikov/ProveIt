#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint35-41-i-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'a05af617176c4af55661bd08d9a14229094a773b9f8e2b67dcc3ce08cb5de72e','source-manifest.json':'add32fdb25e0b36bab038cde3ca0be8c4c23de328598d2ebb3d3b02b007eae32','values-survey.py':'d656b28d8c49bd71facae3ab5ea2169f3220424c5c9c89fb2437b1c2fc4a7548'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['IValue','IPath'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint35-41-i-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint35-41-i-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d35_I_value','prefix_I','⟨32, by decide⟩ : Fin 34','⟨33, by decide⟩ : Fin 34','d34_Gprime_carry, d33_Gprime_value, d34_H_value']);st=b.split('theorem path35_41 ',1)[1].split(':= by',1)[0];pr=b.split('theorem path35_41 ',1)[1].split(':= by',1)[1].split('\ntheorem',1)[0];assert st.count('.castSucc')==6 and pr.count('PrefixPath.step')==6 and all(x in b for x in ['lookup35_41','d41_I_value','lookup35_41 a (Fin.last 34)','d35_I_value a'])
up=D/'reviews/nine-seed33-jones-checkpoint34-41-h-terminal-frontier-independent/check.py';assert H(up)=='ee494cb033aee437a66bd900f7b29f4b8aaff2600d0d03e3e82a7a8c65f6e9b1';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic I at d35 and d41; six-step d35→d41 path only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
