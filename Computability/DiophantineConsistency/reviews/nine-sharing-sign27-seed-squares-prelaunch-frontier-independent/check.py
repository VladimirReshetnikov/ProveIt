#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-seed-squares-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'run.py')=='91f0c3e857dda29836ab4c5f364d4d1d38e161450096d2a5a245832377e73f18' and H(P/'source-manifest.json')=='70aa31cc08d878959f5f0ad52fc5a3478fd7ee73477acd439c412538768b15b1'
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['SharingSeed27Sextic','SharingSign27Squares'];assert [r['module'].split('.')[-1] for r in m]==names;assert [r['imports'] for r in m]==[['DiophantineConsistency.NineFreshJones'],['DiophantineConsistency.SharingSeed27Sextic','DiophantineConsistency.SharingSign33Squares']]
for row,n in zip(m,names):assert H(P/'src/DiophantineConsistency'/f'{n}.lean')==row['source_sha256']
s=(P/'src/DiophantineConsistency/SharingSign27Squares.lean').read_text()
for x in ['(p : Fin 4 → ℤ) (v : Fin 28 → V)','𝗜𝚺₁','SharingSeed27Sextic.firstResidual p :: SharingSeed27Sextic.remainingResiduals p','SharingSign33Squares.squareSum_zero_iff','SharingSeed27Sextic.seed']:assert x in s
f=D/'reviews/nine-sharing-sign27-lean-bridge-plan-frontier-independent/check.py';assert H(f)=='3d9dcda88462c3b687ff83727b3a68cc50065e75a6aaf7668286fefe609e38d7'
plan=D/'research/nine-sharing-sign27-lean-bridge-plan/README.md';s=plan.read_text();suffix='\nThe [independent source review](../../reviews/nine-sharing-sign27-lean-bridge-plan-frontier-independent/README.md) passed for this plan and the accompanying source-only syntax/bridge draft.\n';assert s.endswith(suffix) and hashlib.sha256(s[:-len(suffix)].encode()).hexdigest()=='b5698aeb200a37fe72066d38f6a2e3e99c20a141fe52e118a6edc72fc7e905d5'
for script in ('check.py','check_bridge.py'):
 f=D/'research/nine-sharing-sign27-sextic-lean-draft'/script;subprocess.run([sys.executable,'-I','-S','-B',str(f)],check=True,capture_output=True,timeout=60)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','stages':2,'scope':'symbolic Fin28 syntax and 18-residual square-zero equivalence only'},sort_keys=True,indent=2))
