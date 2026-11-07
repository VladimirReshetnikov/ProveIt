#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-seed-squares-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'6a6cc8c6477be7ce730633685883b9a72635296e745776f4a84896aef61532de','source-manifest.json':'d76a52041fa73d940c0f2e884c3f6e487f929305511db33915c02886492740a9'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert [r['module'].split('.')[-1] for r in m]==['SharingSeed25Octic','SharingSign25Squares']
for e in m:
 n=e['module'].split('.')[-1];p=P/'src/DiophantineConsistency'/f'{n}.lean';assert H(p)==e['source_sha256']==H(D.parents[1]/e['source'])
assert H(P/'src/DiophantineConsistency/SharingSeed25Octic.lean')=='25f4c55e4f9587db295d4fe95908ef6866202c9690204b9dfa88c27b7ea547ec' and H(P/'src/DiophantineConsistency/SharingSign25Squares.lean')=='0da4087927e0fbde58171997b1e0cbb092dbbd5fc175e79b9c66bf85de523e95'
s=(P/'src/DiophantineConsistency/SharingSign25Squares.lean').read_text()
for x in ['[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(p : Fin 4 → ℤ) (v : Fin 26 → V)','InternalZero (SharingSeed25Octic.seed p) v ↔','SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p','SharingSign33Squares.squareSum_zero_iff']:assert x in s
up=D/'reviews/nine-sharing-sign25-octic-lean-draft-frontier-independent/check.py';assert H(up)=='330bf6c64dd09963d4b07a2cc3e56e3510e6c442d97e05111a88146122c1ff10';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'symbolic sign25 seed and generic 16-row square-sum extraction only; no bridge, degree or endpoint','syntax_heartbeat_option':4000000},sort_keys=True,indent=2))
