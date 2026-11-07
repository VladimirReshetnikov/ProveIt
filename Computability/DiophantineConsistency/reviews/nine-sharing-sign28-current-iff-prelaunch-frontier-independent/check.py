#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-current-iff-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'88bf40031a8d22e658eef74136c7dc75c5f0e65c29d52d66e4136091510fda53','source-manifest.json':'e818c610eb4b45693f29c8de80156bf04d62f588a1e12f35051429e61b3dfe87','port-survey.py':'15b06192778ba22a020e656fe6e2937f4653d60978ff87606daebe1b39d03a98','src/DiophantineConsistency/Sign28CurrentSeedIff.lean':'d12c11c33c2aa008e9c3f4700c788c158327f3a858ca8421cd6edda9bf1058a0'}.items():assert H(P/n)==h
rows=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['imports']==['DiophantineConsistency.Sign28SeedExistential','DiophantineConsistency.CurrentKernelData2011'];s=(P/'src/DiophantineConsistency/Sign28CurrentSeedIff.lean').read_text()
for x in ['CurrentWindowCarry2011.ports 0 = (CurrentMasks2011.beta : ℤ)','Int.cast_natCast, map_natCast','Sign28SeedIff.pointwise CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) v port0','Sign28SeedIff.exists_same_input CurrentWindowCarry2011.ports (CurrentMasks2011.beta : V) x port0','𝗜𝚺₁']:assert x in s
assert '∃ v : Fin 29 → V, v 0 = x' in s and '∃ v : Fin 32 → V, v 0 = x' in s
r=D/'reviews/nine-sharing-sign28-seed-iff-terminal-frontier-independent/check.py';assert H(r)=='21864a3d4163554dac9e77a3530c699b5b1130a4afe1ee05b5f22a7def12d313';subprocess.run([sys.executable,'-I','-S','-B',str(r)],check=True,capture_output=True,timeout=30)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'proposed current-port sign28/sign31 pointwise and same-input existential seed iff in IΣ₁'},sort_keys=True,indent=2))
