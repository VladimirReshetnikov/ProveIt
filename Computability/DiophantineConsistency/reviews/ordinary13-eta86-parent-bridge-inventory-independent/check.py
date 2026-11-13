#!/usr/bin/env python3
"""Independent inventory and conditional bridge audit; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta86-parent-bridge-inventory/Eta86ConditionalBridge.lean.src':'abb8d7d3d7613bd733e90dbbaf602948474931f59c37913a41b18cada623a081',
'research/ordinary13-eta86-parent-bridge-inventory/README.md':'6db29631eb88a0f2d6dd80f4d3d9737e2092a23c46d747870339389b5309eb12',
'research/ordinary13-residue90-compact-tuple-client-draft/Residue90CompactTuple.lean.src':'590ca64f723e1f3df85e4aafe99a826facc0c8265960db121fcbec3413541ab2',
'Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean':'c6b54e6098062be18966a9fd5891284909bd1454d6d6ee8b0db26e808045a735',
'Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean':'1476d90741c9cae95b164c4de25dcbdf43399347eee97b9031684f9b1a916ce1',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src':'1cbd2cdd357df688806a70f771d8a2a199290bf5e887a38b0b677ea25c845aab',
'research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src':'a11a673c36c9967e30c3fa68c9ef89b7f8470a64b0ca5d7e1c9bc0113fe0e5ae',
'research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src':'ac7efbd0c75ecd15ccb19d638ee21806bff9284f092830d074d93c8954d621c5',
'research/ordinary13-natural-forced-w86/candidate.json':'75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50',
'research/ordinary13-natural-forced-gamma87/candidate.json':'e753c7c5f8110b9f15e84c9f0da88847a54486f442b60b11812ca3688ca55e21',
'research/ordinary13-natural-unit-product88/candidate.json':'95fdd3495b777a0bdf64c95f6dd24cda660dee42f0508c76fdb081da21f42a5a',
'research/ordinary13-natural-unit-product89/candidate.json':'1d865512c2c78580af0d6a5285c009e5fa03deb141dc711dc5e3adb0b268938d',
'research/ordinary13-unit-product80/candidate.json':'449adf0f03f08cbb73b4ca8c823cb88b79111243c93705b5404f89d18568a22b',
'research/ordinary13-residue-first81/candidate.json':'067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352',
'research/ordinary13-qcube-main83/candidate.json':'d19de596305c838c4b58f011a7fd233fedc4f7a7a87923cca60d00f46b408789',
'research/ordinary13-qcube-unscale84/candidate.json':'2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77',
'research/ordinary13-aux-root87-36/candidate.json':'abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta86-parent-bridge-inventory/Eta86ConditionalBridge.lean.src']
for x in ['def K : ℕ := Residue90CompactTupleDraft.chosenKernel',
 'Residue90CompactTupleDraft.chosen_integer_ports',
 '(h86 : SameNoZero (EtaShifted86GraphDraft.literal (fun j => (ports K j:ℤ)))',
 '(positiveShift IPRAOrdinary13.expression))',
 'IPRAOrdinary12.bridge_of_positive _ IPRAOrdinary13.positiveBridge',
 'HAExpressionNoZeroEquiv.bridge _ _ h86',
 '(heta : EtaUnshift85TransportDraft.ForcedEta K)',
 'EtaUnshift85TransportDraft.polynomialBridge K heta (parent_bridge h86)',
 'IPRAExpressionNative.equivalence_of_bridge _ (child_bridge h86 heta)']:
 assert x in d,x
ret=s['Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean']
assert 'def expression : Expr (Fin 13) := (FreeJ13.graph CompactSymbolicModelIff.p).output' in ret
assert 'theorem positiveBridge : PositiveModelBridge expression' in ret
ip=s['Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean']
assert 'theorem bridge_of_positive {n : ℕ} (e : Expr (Fin n)) (hp : PositiveModelBridge e)' in ip
assert 'PolynomialBridge (positiveShift e)' in ip
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in s['Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean']
t=s['research/ordinary13-residue90-compact-tuple-client-draft/Residue90CompactTuple.lean.src']
assert 'CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho' in t
assert 'integerPorts chosenKernel = CompactSymbolicModelIff.p' in t
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in s['Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean']
for path,term in [('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src','theorem parent86_bridge'),('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src','theorem bridge87'),('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src','theorem bridge88')]:assert term in s[path]
paths=['ordinary13-natural-forced-w86','ordinary13-natural-forced-gamma87','ordinary13-natural-unit-product88','ordinary13-natural-unit-product89','ordinary13-unit-product80','ordinary13-residue-first81','ordinary13-qcube-main83','ordinary13-qcube-unscale84','ordinary13-aux-root87-36']
g=[json.loads(s['research/'+n+'/candidate.json']) for n in paths]
assert [len(x['source']) for x in g]==[86,87,88,89,80,81,83,84,87]
for child,parent,name,var in [(g[0],g[1],'w','n_w'),(g[1],g[2],'gamma','n_gamma'),(g[2],g[3],'J','n_J')]:
 assert child['witnesses']==parent['witnesses'] and child['fixed_numerals']==parent['fixed_numerals']
 assert [[var if z==name else z for z in row] for row in parent['source'] if row!=[name,'+',var,1]]==child['source']
print(json.dumps({'source_sha256':pins,'retained_endpoint_and_tuple_interfaces_checked':True,'exact_initial_shift_edits':3,'conditional_86_bridge_argument_order_checked':True,'lean_executed':False,'scope':'bounded source inventory; no all-model graph chain, source replay, provider build, physical binding or iPRA proof'},sort_keys=True,indent=2))
