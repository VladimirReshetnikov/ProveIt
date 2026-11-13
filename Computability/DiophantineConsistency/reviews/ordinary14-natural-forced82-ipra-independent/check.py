#!/usr/bin/env python3
"""Bounded endpoint signature and selected source import-path review. No Lean."""
import hashlib, json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
files={
 'endpoint':('research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean','2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b'),
 'model82':('research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean','e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854'),
 'pred':('research/ordinary14-natural-forced82-predecessor-draft/GraphPredecessors82.lean','7972ddb132643d0fd46bfd66e200bdf80a48e5d0df1b75f719b9c4ef5db5de54'),
 'endpoint86':('research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean','f3755518938e8d3bf4bcb1d33e2dbbfcdc6f2458a414921b1d03ac244503f47c'),
 'i12':('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean','1476d90741c9cae95b164c4de25dcbdf43399347eee97b9031684f9b1a916ce1'),
 'unconditional':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelUnconditionalIff.lean','ea2dbe86aaebf241d233a1cde5860157da34cf2e20ae943aef42516c659888aa'),
 'projection':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPortProjections.lean','afcd2404ad66cd22843ae936d8a70cc64399cce762c8deb7adfe16be6a01516e'),
 'betaCast':('Lean/DiophantineConsistency/Compact44/CompactSymbolicBetaCast.lean','6785e0211e5e754e42451bfeeea948a96b3d9cc0c08833562f35c14526db29fb'),
 'fixedBeta':('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean','bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'),
 'genericProjection':('Lean/DiophantineConsistency/Compact44/CompactGenericPortProjections.lean','435970e3b2a01c766d2b71f3dbe145c036a59070ec84cb4fe058ae4cb79fa217'),
 'ports':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'),
 'symbolic':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),
 'bridge':('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean','d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06'),
 'native':('Lean/DiophantineConsistency/IPRAExpressionNative.lean','f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8'),
 'standard':('Lean/DiophantineConsistency/IPRAStandardTheory.lean','c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120'),
 'reference':('Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean','e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9'),
}
s={}
for name,(path,h) in files.items():
 data=(D/path).read_bytes(); assert hashlib.sha256(data).hexdigest()==h, path
 s[name]=data.decode()
# Selected lexical import paths to the declarations used for p, ports and beta.
prefix='DiophantineConsistency.Compact44.'
edges=[('endpoint','GraphPredecessors82'),('endpoint','Natural86Endpoint'),
 ('endpoint86',prefix+'IPRAOrdinary12'),('i12',prefix+'CompactSymbolicModelUnconditionalIff'),
 ('unconditional',prefix+'CompactSymbolicModelIff'),('unconditional',prefix+'CompactSymbolicPortProjections'),
 ('projection',prefix+'CompactSymbolicBetaCast'),('betaCast',prefix+'CompactFixedBeta'),
 ('projection',prefix+'CompactGenericPortProjections'),('genericProjection',prefix+'CompactSymbolicPorts')]
for src,dest in edges: assert f'import {dest}\n' in s[src], (src,dest)
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in s['symbolic']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in s['ports']
assert 'def betaNat : ℕ := 2^(67*8807)-1' in s['fixedBeta']
assert 'theorem bounds (J : V) (hJ : 0<J)' in s['fixedBeta']
assert '0<β ∧ L<β' in s['fixedBeta']
assert '(predecessors : ∀ v, InternalZero (P82NaturalForced.graph p).output v →' in s['model82']
assert '(∃ v, InternalZero (P82NaturalForced.graph p).output v) ↔' in s['model82']
assert '∃ w, InternalZero (P86NaturalCancel.graph p).output w' in s['model82']
assert '(hbeta : (p 0 : DiffRing V) = ι beta) (hb : 0 < beta)' in s['pred']
assert 'theorem predecessors_of_zero' in s['pred']
e=s['endpoint']
for token in (
 '(P82NaturalForced.graph CompactSymbolicModelIff.p).output',
 '(CompactSymbolicModelIff.p 0 : DiffRing V) = ι (CompactFixedBeta.betaNat : V)',
 '((CompactFixedBeta.betaNat : ℤ) : DiffRing V) = ι (CompactFixedBeta.betaNat : V)',
 'CompactFixedBeta.bounds (V:=V) 1 (by simp)',
 'SameNoZero expression Natural86EndpointDraft.expression',
 'symbolic_beta_representation symbolic_beta_positive hv',
 'obtain ⟨v, hv⟩ := he.mpr ⟨w, hw⟩', 'exact h v hv',
 'obtain ⟨w, hw⟩ := he.mp ⟨v, hv⟩', 'exact h w hw',
 'HAExpressionNoZeroEquiv.bridge expression Natural86EndpointDraft.expression',
 'sameNoZero Natural86EndpointDraft.polynomialBridge',
 'IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge',
 '(IPRAStandardTheory.provable_iff _).2 native_equivalence',
 'IPRAReferenceInductionConversion.nativeToReference native_equivalence',
): assert token in e, token
assert 'theorem bridge {n m : ℕ}' in s['bridge'] and '(h : SameNoZero e f) (hf : PolynomialBridge f)' in s['bridge']
assert 'theorem polynomialBridge : PolynomialBridge expression' in s['endpoint86']
assert 'theorem equivalence_of_bridge' in s['native']
assert 'standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in s['standard']
assert '(h : IPRANativeTheory.nativeTheory ⊢ σ) : referenceTheory ⊢ erase σ' in s['reference']
for name in ('sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert f'#print axioms DiophantineConsistency.Natural82EndpointDraft.{name}' in e
print(json.dumps({'scope':'bounded source names, signatures and selected lexical import paths only; no Lean or axiom execution',
 'pinned_sources':len(files),'selected_import_edges':len(edges),
 'existence_to_nozero_directions_checked':True,'axiom_print_commands':5},sort_keys=True,indent=2))
