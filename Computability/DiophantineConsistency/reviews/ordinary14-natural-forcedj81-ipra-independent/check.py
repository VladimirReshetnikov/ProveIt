#!/usr/bin/env python3
"""Independent source-interface and witness-direction checks, not Lean."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural-forcedj81-ipra-draft/Natural81Endpoint.lean':'6b235dfcbc279f4d1110e323ead83aefa6c1f650ac6eaf1539a3cec65b8e79be',
'research/ordinary14-natural81-jshift-model-draft/Natural81JShift.lean':'f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6',
'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
'research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean':'2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/HAExpressionAssembly.lean':'15a4c07b1538fa1d9d3d6d5e7d6ab21d9ff9b6c9d80fa10218641fad2ba6b56e',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'Lean/DiophantineConsistency/IPRAStandardTheory.lean':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
'Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean':'e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9'}
s={}
for path,h in files.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path
 s[path.rsplit('/',1)[-1]]=b.decode()
a=s['Natural81Endpoint.lean'];b=s['Natural82Endpoint.lean'];j=s['Natural81JShift.lean'];k=s['StrictK0Symbolic.lean'];n=s['HAExpressionNoZeroEquiv.lean']
for name in ('Natural81JShift','StrictK0Symbolic','Natural82Endpoint'):
 assert re.search(r'^import '+name+r'$',a,re.M)
assert '(P81NaturalForcedJ.graph CompactSymbolicModelIff.p).output' in a
assert '(P82NaturalForced.graph CompactSymbolicModelIff.p).output' in b
assert '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)' in j
assert '(CompactSymbolicModelIff.p 1 : DiffRing V) = ι (paramKernel rho : V)' in k
assert '0 < (paramKernel rho : V)' in k
assert '(paramKernel rho : V) port_one_representation kernel_model_pos' in a
assert 'v81 0 = v82 0 + 1' in j and 'theorem exists_zero_iff' in j
assert re.search(r'\(∃ v, InternalZero \(P81NaturalForcedJ.graph p\).output v\) ↔\s*∃ w, InternalZero \(P82NaturalForced.graph p\).output w',j)
assert 'SameNoZero expression Natural82EndpointDraft.expression' in a
assert 'obtain ⟨v, hv⟩ := he.mpr ⟨w, hw⟩\n    exact h v hv' in a
assert 'obtain ⟨w, hw⟩ := he.mp ⟨v, hv⟩\n    exact h w hw' in a
assert 'def SameNoZero' in n and 'theorem bridge' in n
assert 'HAExpressionNoZeroEquiv.bridge expression Natural82EndpointDraft.expression' in a
assert 'sameNoZero Natural82EndpointDraft.polynomialBridge' in a
assert 'open AdaptiveEquationSyntax2011 HAExpressionAssembly HAExpressionNoZeroEquiv' in a
# Compare the endpoint statement text, whose local expression name is distinct
# in each namespace, and check source references to the existing adapters.
def stmt(src,name):
 m=re.search(r'\btheorem\s+'+name+r'\s*:\s*(.*?)\s*:=',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
for name in ('native_equivalence','standard_equivalence','reference_equivalence'):
 assert stmt(a,name)==stmt(b,name),name
for token in ('IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge',
 '(IPRAStandardTheory.provable_iff _).2 native_equivalence',
 'IPRAReferenceInductionConversion.nativeToReference native_equivalence'):
 assert token in a
for name in ('sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert '#print axioms DiophantineConsistency.Natural81EndpointDraft.'+name in a
print(json.dumps({'scope':'bounded source interface/direction audit, no Lean or axiom replay',
 'pinned_sources':len(files),'symbolic_port':1,'zero_map_directions_checked':2,
 'endpoint_signatures_compared':3,'axiom_commands_unexecuted':5},sort_keys=True,indent=2))
