#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-seed-iff-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'a10f6965e87b77d375df176c376d32c4df1a67115e83139c72edd759be6e8863','source-manifest.json':'24490fe1c8d2b63d1045c75fdcb7a7f53a9b37c70f5592772792a1f28d9cf7f5','src/DiophantineConsistency/Sign27SeedExistential.lean':'f04c523c353bd9bd37067b1146265f6231b19caacb93a6f4924a257c56f8de2a'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign27ReverseBridge'];s=(P/'src/DiophantineConsistency/Sign27SeedExistential.lean').read_text();assert H(D/'research/nine-sharing-sign27-seed-iff-draft/Sign27SeedExistential.lean')==m[0]['source_sha256']
for x in ['[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(∃ v : Fin 28 → V, v 0 = x ∧ InternalZero (SharingSeed27Sextic.seed p) v) ↔','(∃ v : Fin 29 → V, v 0 = x ∧ InternalZero (SharingSeed28Sextic.seed p) v)','Sign27ZeroBridge.forward p v hz','Sign27ZeroBridge.backward p v hz','⟨Sign27FirstCut.lift v,','⟨Sign27ZeroBridge.drop u v,']:assert x in s
up=D/'reviews/nine-sharing-sign27-zero-bridge-terminal-frontier-independent/check.py';assert H(up)=='d51c419c3a31336f928536ff392fef4bf86ad7a552c75038f458841a1714224e';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'same-input existential seed zero equivalence under IΣ₁; no endpoint or Lean replay'},sort_keys=True,indent=2))
