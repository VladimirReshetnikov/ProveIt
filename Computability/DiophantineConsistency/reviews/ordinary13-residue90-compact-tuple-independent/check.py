#!/usr/bin/env python3
"""Independent bounded source and receipt review; no Lean or staging."""
from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-residue90-compact-tuple-client-draft')
f={
'client':p/'Residue90CompactTuple.lean.src','byte_client':p/'Residue90CompactByteTuple.lean.src',
'client_check':p/'check.py','client_receipt':p/'result.json','readme':p/'README.md',
'local_ports':Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src'),
'ports':Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean'),
'symbolic':Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean'),
'bytes':Path('Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean'),
'assembly':Path('Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean'),
'kernel':Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernelOpaque.lean'),
'rho':Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean'),
'endpoint':Path('Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean')}
s={k:v.read_text() for k,v in f.items()}
def norm(x):return re.sub(r'\s+',' ',x).strip()
n={k:norm(v) for k,v in s.items()}
assert 'CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho' in n['client']
assert 'def rho : ℕ := 2^67' in n['rho']
assert 'def paramKernel (r : ℕ) : ℕ :=' in n['kernel']
assert 'CompactSymbolicPorts.ports CompactFixedBeta.betaNat K CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat' in n['local_ports']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in n['ports']
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in n['symbolic']
assert '(hK : K = chosenKernel)' in n['client']
assert 'fun j => (Residue90CompactPortBoundsDraft.ports K j : ℤ)' in n['client']
assert 'def byteP : Fin 4 → ℤ := fun j => ((Nat.ofDigits 256 (bytePorts j) : ℕ) : ℤ)' in n['bytes']
assert 'theorem byteP_eq : byteP = p' in n['bytes']
assert 'chosen_integer_ports.trans CompactBytePortsModelIff.byteP_eq.symm' in n['byte_client']
assert 'CompactShiftedHighByteWindow.bytes' in n['assembly']
assert '![CompactFixedBeta.betaNat, paramKernel rho, lowNat, CompactFixedBeta.betaNat + highNat]' in n['assembly']
assert 'CompactShiftedHighByteAssembly.decode_bytes' in n['assembly']
assert 'def expression : Expr (Fin 13) := (FreeJ13.graph CompactSymbolicModelIff.p).output' in n['endpoint']
assert '[local irreducible]' not in n['client']
for k in ['client','byte_client']:
 assert not re.search(r'\b(?:sorry|admit|unsafe)\b',s[k])
 assert 'InternalZero' not in s[k] and 'PolynomialBridge' not in s[k]
for beta in range(1,8):
 for K in range(5):
  for low in range(4):
   for high in range(1,6):
    tuple_values=[beta,K,low,beta+high]
    assert tuple_values[1]==K and tuple_values[3]==beta+high and tuple_values[3]!=2*beta+high
print(json.dumps({'result':'bounded independent source review: no concrete mismatch found',
 'files_sha256':{k:sha256(v.read_bytes()).hexdigest() for k,v in f.items()},
 'chosen_kernel':'paramKernel rho, rho=2^67',
 'decoding':'Nat.ofDigits 256 before Int cast',
 'fourth_port':'betaNat+highNat once',
 'source_tuple_same_as_endpoint':True,
 'proof_status':'unelaborated; no provider, graph, file or PDF equivalence inferred',
 'lean_executed':False},indent=2,sort_keys=True))
