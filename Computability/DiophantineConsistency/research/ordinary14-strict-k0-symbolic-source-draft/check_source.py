#!/usr/bin/env python3
"""Pin the symbolic-K0 proof route, without Lean or external bytes."""
from pathlib import Path
import hashlib, json
P=Path(__file__).resolve().parent
D=P.parents[1]
base=D/'Lean/DiophantineConsistency/Compact44'
pins={
 P/'StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
 base/'CompactKernelSplit.lean':'3614e342fd80f60feab91e0f5da514b2d266a3cfba800a270380a1855a3a6420',
 base/'CompactSymbolicKernel.lean':'9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55',
 base/'CompactSymbolicKernelOpaque.lean':'8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615',
 base/'CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
 base/'CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
}
sources={}
for path,sha in pins.items():
    b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path)
    sources[path.name]=b.decode()
s=sources['StrictK0Symbolic.lean']
for x in ('theorem kernel_nat_pos','theorem kernel_model_pos',
          'theorem port_one_representation','theorem port_one_pos',
          'CompactKernelSplit.kernel_split_generic','Nat.cast_pos (α:=V)',
          '(CompactSymbolicModelIff.p 1 : DiffRing V)',
          'ι (paramKernel rho : V)'):
    assert x in s,x
assert 'sorry' not in s and 'admit' not in s
assert 'theorem kernel_split_generic (r : ℕ) : paramKernel r = r ^ 8849 + lowerKernelAt r' in sources['CompactKernelSplit.lean']
assert 'def rho : ℕ := 2^67' in sources['CompactSymbolicKernel.lean']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in sources['CompactSymbolicPorts.lean']
assert 'ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in sources['CompactSymbolicModelIff.lean']
print(json.dumps({'scope':'pinned source shape only; no Lean, semantic or byte binding',
                  'pinned_files':len(pins),'symbolic_port':1,'strict_model_positivity_drafted':True},sort_keys=True,indent=2))
