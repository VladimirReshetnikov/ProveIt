#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-seed-squares-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'37f082f9de588a448e3d6af489180aa6aef64a5836390c7feb7a3eb6cf94557c','source-manifest.json':'4155263bb913f73d20b2ed3d0f36f77a406dab3622d4aa1c1f48c1fdf9f10423'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['SharingSeed26Sextic','SharingSign26Squares']
for e in m:
 n=e['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']
s=(P/'src/DiophantineConsistency/SharingSign26Squares.lean').read_text()
for x in ['[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℤ) (v : Fin 27 → V)','InternalZero (SharingSeed26Sextic.seed p) v ↔','SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p','SharingSign33Squares.squareSum_zero_iff']:assert x in s
plan=(D/'research/nine-sharing-sign26-lean-bridge-plan/README.md').read_text();suffix='\nThe [independent source review](../../reviews/nine-sharing-sign26-lean-bridge-plan-frontier-independent/README.md) passed for this plan.\n';assert plan.endswith(suffix) and hashlib.sha256(plan.removesuffix(suffix).encode()).hexdigest()=='43f9733a995e420af214b12ca9de35b8e43efad518375a2ea6598f25ac42f4e3'
up=D/'reviews/nine-sharing-sign26-sextic-lean-draft-frontier-independent/check.py';assert H(up)=='dd7245fdd987b83e21e4fa2462db16213921dc758ad528248a2f4676b3cbddd9';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'sign26 symbolic seed and generic 17-row square-sum extraction only; historical plan README appendix documented; no Lean replay'},sort_keys=True,indent=2))
