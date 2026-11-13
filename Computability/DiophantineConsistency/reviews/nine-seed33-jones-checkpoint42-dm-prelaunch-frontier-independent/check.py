#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint42-dm-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'5c250d60f2f68f18bea2bdb45f4d1adf8d518aeb42c0665f00d13ed9d48dc827','source-manifest.json':'600e313df03db266f5294e171e30b5fd5af807183daa2c53c11e9f4ea10ac957','values-survey.py':'083944152b4764e7250f613b4c681ee17dce35f0a50ae2472c1a0725c6b7d237'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==2;ss=[]
for suffix,e in zip(['DmInputs','DmValue'],m):
 name='Sign33Macro'+suffix;p=P/'src/DiophantineConsistency'/f'{name}.lean';old=D/f'research/nine-seed38-jones-checkpoint42-dm-check/src/DiophantineConsistency/Norm38Macro{suffix}.lean';assert e['module']=='DiophantineConsistency.'+name and H(p)==e['source_sha256']==H(D/f'research/nine-seed33-jones-checkpoint42-dm-draft/{name}.lean');assert p.read_text()==old.read_text().replace('Norm38','Sign33').replace('5 ^ 39','5 ^ 34').replace('5 ^ 38','5 ^ 33');ss.append(p.read_text())
a,b=ss;assert all(x in a for x in ['d41_K_value','d41_Y_value','lookup']);assert all(x in b for x in ['d42_Dm_value','prefix_Dm','⟨22, by decide⟩ : Fin 41','⟨9, by decide⟩ : Fin 41','⟨26, by decide⟩ : Fin 41','⟨19, by decide⟩ : Fin 41','⟨7, by decide⟩ : Fin 41','d41_K_value, d41_G_value, d41_C_value, d41_Y_value, d41_g_value'])
up=D/'reviews/nine-seed33-jones-checkpoint40-41-bdcd-terminal-frontier-independent/check.py';assert H(up)=='a3caeb4ec40667b1924730943938ef08bc5222282a24c24136dd945df44d8bfb';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'d41 K/Y carries and symbolic Dm d42 only; rank opaque, no full output semantics'},sort_keys=True,indent=2))
