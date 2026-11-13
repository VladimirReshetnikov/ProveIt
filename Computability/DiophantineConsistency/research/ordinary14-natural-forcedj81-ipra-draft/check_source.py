#!/usr/bin/env python3
"""Pin proposed endpoint clients and dependencies without running Lean."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 P/'Natural81Endpoint.lean':'6b235dfcbc279f4d1110e323ead83aefa6c1f650ac6eaf1539a3cec65b8e79be',
 D/'research/ordinary14-natural81-jshift-model-draft/Natural81JShift.lean':'f8e6436236c850e013ea9b9f9bbfe2ce48c45625a1d58ac1865e0413d96a5ca6',
 D/'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
 D/'research/ordinary14-natural-forced82-ipra-draft/Natural82Endpoint.lean':'2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b',
}
sources={}
for path,sha in pins.items():
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);sources[path.name]=b.decode()
s=sources['Natural81Endpoint.lean']
for x in ('import Natural81JShift','import StrictK0Symbolic','import Natural82Endpoint',
          '(P81NaturalForcedJ.graph CompactSymbolicModelIff.p).output',
          'SameNoZero expression Natural82EndpointDraft.expression',
          'Natural81JShiftDraft.exists_zero_iff',
          '(paramKernel rho : V) port_one_representation kernel_model_pos',
          'HAExpressionNoZeroEquiv.bridge expression Natural82EndpointDraft.expression',
          'Natural82EndpointDraft.polynomialBridge',
          'IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge',
          'IPRAStandardTheory.provable_iff','IPRAReferenceInductionConversion.nativeToReference'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
for n in ('sameNoZero','polynomialBridge','native_equivalence','standard_equivalence','reference_equivalence'):
 assert '#print axioms DiophantineConsistency.Natural81EndpointDraft.'+n in s
assert 'theorem J_pos_of_zero' in sources['Natural81JShift.lean']
assert 'theorem port_one_representation' in sources['StrictK0Symbolic.lean']
assert 'theorem polynomialBridge : PolynomialBridge expression' in sources['Natural82Endpoint.lean']
print(json.dumps({'scope':'pinned source only; no Lean, iPRA or byte binding',
                  'pinned_files':len(pins),'strict_symbolic_k0_used':True,'axiom_print_commands':5,
                  'proposed_clients':['sameNoZero','polynomialBridge','native','standard','reference']},sort_keys=True,indent=2))
