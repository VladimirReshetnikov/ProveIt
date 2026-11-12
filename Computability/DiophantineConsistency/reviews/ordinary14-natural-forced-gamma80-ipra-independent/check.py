#!/usr/bin/env python3
"""Bounded source interface, port and no-zero-direction check; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural-forced-gamma80-ipra-draft/Natural80Endpoint.lean':'8266ca2bbbb442b7e9ccd298f5586b2c7e92d1a61a07a8a26f5eef685df3a8fc',
'research/ordinary14-natural-forced-gamma80-ipra-draft/check_source.py':'13de5af57ce9864a7949210bbd2de4afd9fb594e3cd2cc8e953ec49388b849f7',
'research/ordinary14-natural-forced-gamma80-ipra-draft/result.json':'af204b23a7de7ff2f253a54d5da62ad72482573a63e1a441f09d5414218c661e',
'research/ordinary14-natural80-gamma-shift-model-draft/Natural80GammaShift.lean':'150871559ad8be8ac689135c8021b8e488af138e68f929b878632d13d99c216a',
'research/ordinary14-natural-forcedj81-ipra-draft/Natural81Endpoint.lean':'6b235dfcbc279f4d1110e323ead83aefa6c1f650ac6eaf1539a3cec65b8e79be',
'research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean':'2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b',
'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean':'fb35a320b1521b3005feb597ace302ea9779304839a952b9590f6e0b9a6b4fa4',
'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
'research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean':'015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/HAExpressionAssembly.lean':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'Lean/DiophantineConsistency/IPRAStandardTheory.lean':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
'Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean':'e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9',
'Lean/DiophantineConsistency/IPRAOrderErasure.lean':'d14c6b50d1ee5c09bc6f3673d3bd9b3715ca2d9aba21c403a154fb6ff5da21d6',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean':'0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
}
s={}
for path,h in files.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path;s[Path(path).name]=b.decode()
a=s['Natural80Endpoint.lean'];g=s['Natural80GammaShift.lean'];b=s['Natural81Endpoint.lean'];c=s['Natural82Endpoint.lean']
def signature(text,name):
 m=re.search(r'\btheorem\s+'+re.escape(name)+r'\b(.*?)(?=\s+:=\s*by\b)',text,re.S);assert m,name
 return re.sub(r'\s+',' ',m.group(1)).strip()
def stmt(text,name):
 m=re.search(r'\btheorem\s+'+name+r'\s*:\s*(.*?)\s*:=',text,re.S);assert m,name
 return ' '.join(m.group(1).split())
# Named declarations and their lexical direct imports; no compiled resolution.
for name in ('Natural80GammaShift','Natural81Endpoint','CompactPortBoundsSlim','StrictK0Symbolic',
 'DiophantineConsistency.HAExpressionNoZeroEquiv','DiophantineConsistency.IPRAExpressionNative',
 'DiophantineConsistency.IPRAStandardTheory','DiophantineConsistency.IPRAReferenceInductionConversion'):
 assert re.search(r'^import '+re.escape(name)+r'$',a,re.M),name
assert re.search(r'^import Natural82Endpoint$',b,re.M)
assert re.search(r'^import DiophantineConsistency.Compact44.CompactSymbolicModelIff$',s['StrictK0Symbolic.lean'],re.M)
assert re.search(r'^import DiophantineConsistency.Compact44.CompactSymbolicPorts$',s['CompactPortBoundsSlim.lean'],re.M)
assert '(P80NaturalForcedGamma.graph CompactSymbolicModelIff.p).output' in a
assert '(P81NaturalForcedJ.graph CompactSymbolicModelIff.p).output' in b
assert '(P82NaturalForced.graph CompactSymbolicModelIff.p).output' in c
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in s['CompactSymbolicPorts.lean']
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in s['CompactSymbolicModelIff.lean']
assert 'def betaNat : ℕ := 2^(67*8807)-1' in s['CompactFixedBeta.lean']
# Port cast statements and bound assumptions are checked as declarations, not evaluated numerals.
assert '(CompactSymbolicModelIff.p 0 : DiffRing V) = ι (CompactFixedBeta.betaNat : V)' in signature(c,'symbolic_beta_representation')
k1=signature(s['StrictK0Symbolic.lean'],'port_one_representation')
assert '(CompactSymbolicModelIff.p 1 : DiffRing V) = ι (paramKernel rho : V)' in k1
assert '0 < (paramKernel rho : V)' in signature(s['StrictK0Symbolic.lean'],'kernel_model_pos')
assert '(CompactSymbolicModelIff.p 2 : DiffRing V)=ι (lowNat : V)' in signature(a,'port_two_representation')
assert '(CompactSymbolicModelIff.p 3 : DiffRing V)=ι ((CompactFixedBeta.betaNat+highNat : ℕ) : V)' in signature(a,'port_three_representation')
for n in ('port_two_representation','port_three_representation'):
 assert 'simp only [Int.cast_natCast,map_natCast]' in a
bounds=signature(s['CompactPortBoundsSlim.lean'],'port_bounds')
for tok in ('(hB : (B : V) + 1 = Exp.exp ((67 : V) * 8807))','(hL : L = lowNat)','(hH : H = highNat)', '0 < (ports B K L H 0 : V)','(ports B K L H 2 : V) < (ports B K L H 0 : V)','(ports B K L H 3 : V) < 2 * (ports B K L H 0 : V)'):
 assert tok in bounds,tok
assert 'CompactFixedBeta.beta_identity rfl rfl' in a
for tok in ('have hb : 0<(CompactFixedBeta.betaNat : V)', 'have hMC : (lowNat : V)<(CompactFixedBeta.betaNat : V)', 'have hMF : ((CompactFixedBeta.betaNat+highNat : ℕ) : V)<2*(CompactFixedBeta.betaNat : V)', 'Natural82EndpointDraft.symbolic_beta_representation port_one_representation', 'port_two_representation port_three_representation hb kernel_model_pos hMC hMF'):
 assert tok in a,tok
# Inspect existential orientation and no-zero conversion, not same-input equality.
sg=signature(g,'exists_zero_iff')
for tok in ('(hbeta : (p 0 : DiffRing V)=ι beta)', '(hK : (p 1 : DiffRing V)=ι K)', '(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)', '(hb : 0<beta)', '(hKpos : 0<K)', '(hMCbound : MC<beta)', '(hMFbound : MF<2*beta)', '(∃ v, InternalZero (P80NaturalForcedGamma.graph p).output v) ↔ ∃ w, InternalZero (P81NaturalForcedJ.graph p).output w'):
 assert tok in sg,tok
assert 'SameNoZero expression Natural81EndpointDraft.expression' in a
assert 'obtain ⟨v,hv⟩ := he.mpr ⟨w,hw⟩\n    exact h v hv' in a
assert 'obtain ⟨w,hw⟩ := he.mp ⟨v,hv⟩\n    exact h w hw' in a
nz=s['HAExpressionNoZeroEquiv.lean'];assert '(∀ v : Fin n → V, ¬InternalZero e v) ↔ ∀ v : Fin m → V, ¬InternalZero f v' in nz
assert '(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in nz
assert 'HAExpressionNoZeroEquiv.bridge expression Natural81EndpointDraft.expression' in a and 'sameNoZero Natural81EndpointDraft.polynomialBridge' in a
# The three targets are textually identical to the prior local-expression endpoints.
for n in ('native_equivalence','standard_equivalence','reference_equivalence'):assert stmt(a,n)==stmt(b,n),n
assert 'theorem equivalence_of_bridge {n : ℕ}' in s['IPRAExpressionNative.lean']
assert '(IPRAStandardTheory.provable_iff _).2 native_equivalence' in a
assert 'standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in s['IPRAStandardTheory.lean']
assert 'IPRAReferenceInductionConversion.nativeToReference native_equivalence' in a
assert '(h : IPRANativeTheory.nativeTheory ⊢ σ) : referenceTheory ⊢ erase σ' in s['IPRAReferenceInductionConversion.lean']
for n in ('port_two_representation','port_three_representation','sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert '#print axioms DiophantineConsistency.Natural80EndpointDraft.'+n in a
print(json.dumps({'scope':'bounded source interface, selected symbolic ports and no-zero directions only; no Lean/iPRA theorem','pinned_sources':len(files),'symbolic_port_slots':4,'zero_map_directions':2,'endpoint_signatures_compared':3,'axiom_prints_executed':False},sort_keys=True,indent=2))
