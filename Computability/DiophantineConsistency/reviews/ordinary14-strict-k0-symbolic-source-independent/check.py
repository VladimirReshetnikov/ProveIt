#!/usr/bin/env python3
"""Independent bounded signature review; no Lean evaluation or byte binding."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
'Lean/DiophantineConsistency/Compact44/CompactKernelSplit.lean':'3614e342fd80f60feab91e0f5da514b2d266a3cfba800a270380a1855a3a6420',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean':'9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean':'8ae9ed11d9e7408e4fd71555569181b0fb785f24f3177facc6c6c997d0d5e615',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'Lean/DiophantineConsistency/ArithmeticMachineTape215.lean':'b160b6c6133942e3b7100a282f13678bccf265deacc79d11854c2c133e7a30b9'}
s={}
for path,h in files.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path
 s[path.rsplit('/',1)[-1]]=b.decode()
k=s['StrictK0Symbolic.lean']; split=s['CompactKernelSplit.lean'];rho=s['CompactSymbolicKernel.lean']; ports=s['CompactSymbolicPorts.lean']; p=s['CompactSymbolicModelIff.lean']; diff=s['ModelDifferenceRing.lean']; previous=s['ArithmeticMachineTape215.lean']
assert 'def rho : ℕ := 2^67' in rho
assert 'def lowerKernelAt (r : ℕ) : ℕ' in split
assert 'theorem kernel_split_generic (r : ℕ) : paramKernel r = r ^ 8849 + lowerKernelAt r' in split
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
assert 'ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in p
assert 'theorem ι_lt_ι {a b : V} : ι a < ι b ↔ a < b' in diff
assert 'namespace DiophantineConsistency.StrictK0SymbolicDraft' in k
for decl in ('kernel_nat_pos','kernel_model_pos','port_one_representation','port_one_pos'):
 assert re.search(r'\btheorem\s+'+decl+r'\b',k)
assert k.count('[ORingStructure V]')==3 and k.count('[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]')==3
assert '(paramKernel rho : V)' in k and '(CompactSymbolicModelIff.p 1 : DiffRing V)' in k
assert 'CompactKernelSplit.kernel_split_generic' in k and 'Nat.cast_pos (α:=V)' in k and 'ι_lt_ι.mpr' in k
# Prior source uses the same Nat.cast_pos application with the same model
# assumptions; this is supporting evidence, not proof of the new elaboration.
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in previous
assert 'Nat.cast_pos (α:=V)' in previous
# A positive natural top term is enough regardless of the remaining natural summand.
assert 2**67>0 and (2**67)**8849>0
print(json.dumps({'scope':'bounded source signatures and elementary positivity argument; no Lean or physical bytes',
 'pinned_sources':len(files),'symbolic_port':1,'natural_top_term_positive':True,
 'same_model_cast_pattern_observed_elsewhere':True},sort_keys=True,indent=2))
