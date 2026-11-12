#!/usr/bin/env python3
"""Pin inert tuple clients and exact source interfaces; no Lean execution."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,digest):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b.decode()
files={
'first':('research/ordinary13-residue90-compact-tuple-client-draft/Residue90CompactTuple.lean.src','590ca64f723e1f3df85e4aafe99a826facc0c8265960db121fcbec3413541ab2'),
'second':('research/ordinary13-residue90-compact-tuple-client-draft/Residue90CompactByteTuple.lean.src','f2e3b0fd650b368aedda0e87d72bc29402f0dc01e99d2dc51cdb113eb0bf6223'),
'draftports':('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src','11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a'),
'ports':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'),
'symbolic':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),
'byteiff':('Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean','6a6a15e046bf82817c28e0df884b24f52c0741e24d92149e485fe33836db042d'),
'assembly':('Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean','3f863dde2c2c5bc3b5dd9789d2e2f5ae70c5856482979b577a4e405f6d7c019e'),
'endpoint':('Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean','c6b54e6098062be18966a9fd5891284909bd1454d6d6ee8b0db26e808045a735'),
'prior':('reviews/ordinary13-residue90-compact-port-provenance-audit/result.json','515a9be58df51869c67058af2a54aec8284932d44894998d88ceb8ca8eb49e4c')}
s={k:pin(*v) for k,v in files.items()}
for k,terms in {'first':['import Residue90CompactPortBounds','import DiophantineConsistency.Compact44.CompactSymbolicModelIff','CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho','Residue90CompactPortBoundsDraft.ports K j : ℤ','theorem chosen_integer_ports','theorem integer_ports_of_kernel','(hK : K = chosenKernel)'], 'second':['import Residue90CompactTuple','import DiophantineConsistency.Compact44.CompactBytePortsModelIff','CompactBytePortsModelIff.byteP','CompactBytePortsModelIff.byteP_eq.symm'], 'draftports':['CompactSymbolicPorts.ports CompactFixedBeta.betaNat K','CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat'], 'ports':['def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]'], 'symbolic':['def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)'], 'byteiff':['def byteP : Fin 4 → ℤ := fun j => ((Nat.ofDigits 256 (bytePorts j) : ℕ) : ℤ)','theorem byteP_eq : byteP = p'], 'assembly':['theorem decode_ports','ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat'], 'endpoint':['def expression : Expr (Fin 13) := (FreeJ13.graph CompactSymbolicModelIff.p).output','theorem native_equivalence']}.items():
 for term in terms:assert term in s[k],(k,term)
for src in (s['first'],s['second']):
 assert not re.search(r'\b(?:sorry|admit|unsafe)\b',src)
assert s['first'].count('#print axioms')==2 and s['second'].count('#print axioms')==1
assert 'InternalZero' not in s['first']+s['second'] and 'PolynomialBridge' not in s['first']+s['second']
prior=json.loads(s['prior']);assert prior['P72_P115_four_gzip_and_raw_payloads_identical'] and prior['MF_shifted_once']
print(json.dumps({'scope':'pinned source-only symbolic/closed-Lean-byte tuple clients; no Lean','sources':2,'arbitrary_K_requires_explicit_equality':True,'byte_decoding_in_naturals':True,'MF_shift_exactly_once':True,'same_tuple_as_retained_87_endpoint_source':True,'graph_bridge_filesystem_PDF_and_providers_not_proved':True,'lean_elaborated':False},sort_keys=True,indent=2))
