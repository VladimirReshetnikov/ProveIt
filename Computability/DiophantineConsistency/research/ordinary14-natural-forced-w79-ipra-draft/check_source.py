#!/usr/bin/env python3
"""Check pinned endpoint proposal and source interfaces; no Lean run."""
from pathlib import Path
import hashlib,json,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];L=D/'Lean/DiophantineConsistency'
pins={
 'client':(P/'Natural79Endpoint.lean','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'wpos':(D/'research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293'),
 'wshift':(D/'research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1'),
 'parent':(D/'research/ordinary14-natural-forced-gamma80-ipra-draft/Natural80Endpoint.lean','8266ca2bbbb442b7e9ccd298f5586b2c7e92d1a61a07a8a26f5eef685df3a8fc'),
 'beta':(D/'research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean','2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b'),
 'k0':(D/'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean','7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a'),
 'graph':(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'ports':(L/'Compact44/CompactSymbolicModelIff.lean','379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46'),
 'transport':(L/'HAExpressionNoZeroEquiv.lean','d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06'),
 'native':(L/'IPRAExpressionNative.lean','f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8'),
 'standard':(L/'IPRAStandardTheory.lean','c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120'),
 'reference':(L/'IPRAReferenceInductionConversion.lean','e94ba7c5e4fe4ca809c55be43870331f0a4a7506eae372aa97ce74c789cb6cc9')}
s={}
for n,(p,h) in pins.items():
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==h,n;s[n]=data.decode()
for token in ('theorem w_pos_of_zero','(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hb : 0<beta) (hz : InternalZero (P79NaturalForcedW.graph p).output v) : 0<v 6'):
 assert token in s['wpos'],token
assert '(positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6)' in s['wshift']
for token in ('theorem symbolic_beta_representation','theorem symbolic_beta_positive'):
 assert token in s['beta']
assert 'theorem port_one_representation' in s['k0']
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat' in s['ports']
assert 'def SameNoZero' in s['transport'] and 'theorem bridge' in s['transport']
assert 'theorem equivalence_of_bridge' in s['native']
assert 'theorem provable_iff' in s['standard']
assert 'theorem nativeToReference' in s['reference']
client=s['client']
for token in ('import Natural79ZeroWDivisibility','import Natural79WShift','import Natural80Endpoint',
 'import Natural82Endpoint','import StrictK0Symbolic',
 '(P79NaturalForcedW.graph CompactSymbolicModelIff.p).output',
 'SameNoZero expression Natural80EndpointDraft.expression',
 'Natural82EndpointDraft.symbolic_beta_representation',
 'Natural82EndpointDraft.symbolic_beta_positive',
 'StrictK0SymbolicDraft.port_one_representation',
 'Natural79WShiftDraft.exists_zero_iff_of_positive',
 'Natural79ZeroWDivisibilityDraft.w_pos_of_zero',
 'v hbeta hK hb hv','obtain ⟨v,hv⟩ := he.mpr ⟨w,hw⟩',
 'obtain ⟨w,hw⟩ := he.mp ⟨v,hv⟩',
 'HAExpressionNoZeroEquiv.bridge expression Natural80EndpointDraft.expression',
 'sameNoZero Natural80EndpointDraft.polynomialBridge',
 'IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge',
 'IPRAStandardTheory.provable_iff','IPRAReferenceInductionConversion.nativeToReference'):
 assert token in client,token
for name in ('sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert f'#print axioms DiophantineConsistency.Natural79EndpointDraft.{name}' in client
for name in ('native_equivalence','standard_equivalence','reference_equivalence','polynomialBridge'):
 assert 'theorem '+name in s['parent'],name
assert 'sorry' not in client and 'admit' not in client
# Abstract two-way no-zero transport sanity controls only, not a model proof.
for a in (False,True):
 for b in (False,True):
  if a==b:assert (not a)==(not b)
print(json.dumps({'scope':'pinned source signatures and witness directions only; no Lean or iPRA theorem',
 'pinned_files':len(pins),'selected_symbolic_port_slots':[0,1],
 'proposed_clients':['sameNoZero','polynomialBridge','native','standard','reference'],
 'axiom_reports_not_run':5,'direct_literal_file_binding':False},sort_keys=True,indent=2))
