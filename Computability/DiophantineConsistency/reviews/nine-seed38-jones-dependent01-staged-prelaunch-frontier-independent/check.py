#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent01-staged-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'5f141a574562eea654b76e677535d49f3e206ac02263f4836656f2381f6e34d1','provider_preflight.py':'82ccd654d4d1c1cef12fa0fac044ccaa3e8bcbab58db9a3390c1dcda039558a1','source-manifest.json':'2e9a9e0a281572d608412540e5443abea674cf66936b532b18e48d15d9c5a063'}.items():assert h(p/n)==v
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Norm38MacroDependentU','50e264ce517b48c99515708bb30e2931ed5a0dcdc62f4d8a47c1c68eed270c42','Norm38MacroLive18Group01','prefix_U',[3,13]),('Norm38MacroDependentY','286f4da18de300f3c4c0e62010e003c331ae06b742d0ab6c3a596c637c393864','Norm38MacroDependentU','prefix_Y',[3,12])];assert len(rows)==2
for row,(n,sha,imp,t,indices) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';assert h(q)==sha==row['source_sha256'];s=q.read_text();assert row['module']=='DiophantineConsistency.'+n;assert row['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+imp];assert re.findall(r'^theorem (\w+)',s,re.M)==[t] and re.findall(r'^#print axioms (\w+)',s,re.M)==[t]
 concl=s.split(':= by',1)[0];vs=re.findall(r'd18\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',concl);assert [int(i) for i,_ in vs]==indices and all(int(i)+1+c.count('.castSucc')==18 for i,c in vs)
named=(d/'research/nine-seed38-jones-named-prefix-draft/Norm38MacroPrefixes.lean').read_text();assert 'def d19 : Dag 19 := .snoc d18 (.mul (.pow (.ref ⟨3, by decide⟩) (.lit 2)) (.ref ⟨13, by decide⟩))' in named;assert 'def d20 : Dag 20 := .snoc d19 (.mul (.pow (.ref ⟨3, by decide⟩) (.lit 2)) (.ref ⟨12, by decide⟩))' in named
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled U/Y prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
