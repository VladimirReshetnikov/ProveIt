#!/usr/bin/env python3
"""Independent bounded endpoint signature/transport inspection; never invokes Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
files={
 'endpoint':('research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'wpos':('research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293'),
 'wshift':('research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1'),
 'parent':('research/ordinary14-natural-forced-gamma80-ipra-draft/Natural80Endpoint.lean','8266ca2bbbb442b7e9ccd298f5586b2c7e92d1a61a07a8a26f5eef685df3a8fc'),
 'beta':('research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean','2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b'),
 'K':('research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean','7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a'),
 'porttuple':('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean','0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414'),
 'portmap':('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),
 'fixedbeta':('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean','bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea'),
 'transport':('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean','d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06'),
 'native':('Lean/DiophantineConsistency/IPRAExpressionNative.lean','f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8'),
 'standard':('Lean/DiophantineConsistency/IPRAStandardTheory.lean','c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120'),
 'reference':('Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean','e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9'),
}
x={n:pin(p,h) for n,(p,h) in files.items()};s=x['endpoint']
imports=[l.split()[1] for l in s.splitlines() if l.startswith('import ')]
assert imports==['Natural79ZeroWDivisibility','Natural79WShift','Natural80Endpoint','Natural82Endpoint','StrictK0Symbolic','DiophantineConsistency.HAExpressionNoZeroEquiv','DiophantineConsistency.IPRAExpressionNative','DiophantineConsistency.IPRAStandardTheory','DiophantineConsistency.IPRAReferenceInductionConversion']
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in x['porttuple']
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in x['portmap']
assert 'def betaNat : ℕ := 2^(67*8807)-1' in x['fixedbeta']
for text in ('theorem symbolic_beta_representation','theorem symbolic_beta_positive','(CompactSymbolicModelIff.p 0 : DiffRing V) = ι (CompactFixedBeta.betaNat : V)'):assert text in x['beta']
assert 'theorem port_one_representation' in x['K'] and '(CompactSymbolicModelIff.p 1 : DiffRing V) = ι (paramKernel rho : V)' in x['K']
assert '(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)' in x['wpos']
assert '(hb : 0<beta) (hz : InternalZero (P79NaturalForcedW.graph p).output v) : 0<v 6' in x['wpos']
assert '(positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6)' in x['wshift']
assert '(∃ v, InternalZero (P79NaturalForcedW.graph p).output v) ↔' in x['wshift'] and '∃ w, InternalZero (P80NaturalForcedGamma.graph p).output w' in x['wshift']
assert '(∀ v : Fin n → V, ¬InternalZero e v) ↔ ∀ v : Fin m → V, ¬InternalZero f v' in x['transport']
assert 'theorem bridge {n m : ℕ} (e : Expr (Fin n)) (f : Expr (Fin m))' in x['transport']
assert 'theorem equivalence_of_bridge' in x['native'] and 'nativeTheory ⊢ nativeNoZero e 🡘 ∼mappedNativeRefutation embedding' in x['native']
assert 'standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in x['standard']
assert '(h : IPRANativeTheory.nativeTheory ⊢ σ) : referenceTheory ⊢ erase σ' in x['reference']
for t in ('(P79NaturalForcedW.graph CompactSymbolicModelIff.p).output','Natural82EndpointDraft.symbolic_beta_representation','Natural82EndpointDraft.symbolic_beta_positive','StrictK0SymbolicDraft.port_one_representation','Natural79WShiftDraft.exists_zero_iff_of_positive','Natural79ZeroWDivisibilityDraft.w_pos_of_zero','v hbeta hK hb hv','obtain ⟨v,hv⟩ := he.mpr ⟨w,hw⟩','obtain ⟨w,hw⟩ := he.mp ⟨v,hv⟩','HAExpressionNoZeroEquiv.bridge expression Natural80EndpointDraft.expression','sameNoZero Natural80EndpointDraft.polynomialBridge','IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge','IPRAStandardTheory.provable_iff','IPRAReferenceInductionConversion.nativeToReference'):assert t in s
for n in ('sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):assert '#print axioms DiophantineConsistency.Natural79EndpointDraft.'+n in s
print(json.dumps({'scope':'bounded source signatures, symbolic ports and witness directions; no Lean, provider or iPRA proof','pinned_files':len(files),'direct_imports':len(imports),'symbolic_beta_exponent':67*8807,'same_no_zero_directions_checked':2,'axiom_reports_unexecuted':5},sort_keys=True,indent=2))
