#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-seed-iff-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'64da796c356227c630158c688c2a739b3e42a47d734655a7561e4c00fcda24d4','source-manifest.json':'87aeac1ed42fc1b6646106e998ac865a119522cbabe52e6ac751b4f8e617890b','src/DiophantineConsistency/Sign25SeedExistential.lean':'60edcbb246cf89ad2719492c71ceed7b2f1c681cd7b14f05b15cec1c450d47c7'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.Sign25ReverseBridge'];s=(P/'src/DiophantineConsistency/Sign25SeedExistential.lean').read_text();assert H(D/'research/nine-sharing-sign25-seed-iff-draft/Sign25SeedExistential.lean')==m[0]['source_sha256']
for x in ['[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','∃ v : Fin 26 → V, v 0 = x ∧ InternalZero (SharingSeed25Octic.seed p) v','∃ v : Fin 27 → V, v 0 = x ∧ InternalZero (SharingSeed26Sextic.seed p) v','Sign25ZeroBridge.forward p v hz','Sign25ZeroBridge.backward p v hz','⟨Sign25FirstCut.lift v,','⟨Sign25CoordinateRecover.drop v,']:assert x in s
up=D/'reviews/nine-sharing-sign25-zero-assembly-terminal-frontier-independent/check.py';assert H(up)=='617b1d0fb214ceb49bd75695f3b99b01b01a6aeb57b9f9165c22e9c8634d8cc7';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'same-input existential sign25/sign26 seed zero iff under IΣ₁ for symbolic ports; no endpoint or Lean replay'},sort_keys=True,indent=2))
