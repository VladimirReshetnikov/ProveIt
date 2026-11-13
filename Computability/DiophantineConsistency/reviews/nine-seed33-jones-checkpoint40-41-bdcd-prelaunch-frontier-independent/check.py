#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint40-41-bdcd-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'c76c3c5a58ce51c690865bb09fbf62e249dc4bd24157a36cccdb052c0f2e1b7a','source-manifest.json':'802b215b7b7cf059efb6edd75e1a14a81b1c1003d38a4d7a6716217a5e22e589','values-survey.py':'57102a552b1423798b8578654ff8a99fb1b938be979bb7abcafdd7d62d8db784'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==3;ss=[]
for suffix,e in zip(['BdCdPaths','BdValue','CdValue'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint40-41-bdcd-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint40-41-bdcd-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b,c=ss;assert all(x in a for x in ['lookup39_41','lookup40_41','d41_C_value','PrefixPath.step (PrefixPath.step (PrefixPath.base d39) _) _','PrefixPath.step (PrefixPath.base d40) _']);assert all(x in b for x in ['d40_Bd_value','prefix_Bd','d39.values a ⟨27, by decide⟩','d39.values a ⟨31, by decide⟩','rw [h27, h31]']);assert all(x in c for x in ['d41_Cd_value','prefix_Cd','d40.values a ⟨28, by decide⟩','d40.values a ⟨31, by decide⟩','d40.values a ⟨27, by decide⟩','d40.values a ⟨33, by decide⟩','d40.values a ⟨26, by decide⟩','rw [h28, h31, h27, h33, h26]'])
up=D/'reviews/nine-seed33-jones-checkpoint38-39-v-terminal-frontier-independent/check.py';assert H(up)=='ae37ffb06bd358cec3d3462647d602d89528600cccecf134927d50c37f9b221b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic Bd d40/Cd d41 and checkpoint lookups only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
