#!/usr/bin/env python3
"""Pin the proposed natural-80 endpoint source without invoking Lean."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 P/'Natural80Endpoint.lean':'8266ca2bbbb442b7e9ccd298f5586b2c7e92d1a61a07a8a26f5eef685df3a8fc',
 D/'research/ordinary14-natural-forcedj81-ipra-draft/Natural81Endpoint.lean':'6b235dfcbc279f4d1110e323ead83aefa6c1f650ac6eaf1539a3cec65b8e79be',
 D/'research/ordinary14-natural80-gamma-shift-model-draft/Natural80GammaShift.lean':'150871559ad8be8ac689135c8021b8e488af138e68f929b878632d13d99c216a',
 D/'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean':'fb35a320b1521b3005feb597ace302ea9779304839a952b9590f6e0b9a6b4fa4',
 D/'research/ordinary14-strict-k0-symbolic-source-draft/StrictK0Symbolic.lean':'7b694e0aa874a1d321cc348db26d2aa56a6dc6509b331b6bb3dfdd9c1d6ce31a',
}
sources={}
for p,h in pins.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);sources[p.name]=b.decode()
s=sources['Natural80Endpoint.lean']
for x in ('import Natural80GammaShift','import Natural81Endpoint','import CompactPortBoundsSlim','import StrictK0Symbolic',
          '(P80NaturalForcedGamma.graph CompactSymbolicModelIff.p).output',
          'theorem port_two_representation','theorem port_three_representation',
          'Natural82EndpointDraft.symbolic_beta_representation port_one_representation',
          'port_two_representation port_three_representation hb kernel_model_pos hMC hMF',
          'SameNoZero expression Natural81EndpointDraft.expression',
          'Natural80GammaShiftDraft.exists_zero_iff','CompactPortBoundsSlimDraft.port_bounds',
          'HAExpressionNoZeroEquiv.bridge expression Natural81EndpointDraft.expression',
          'IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge',
          'IPRAStandardTheory.provable_iff','IPRAReferenceInductionConversion.nativeToReference'):
 assert x in s,x
for n in ('port_two_representation','port_three_representation','sameNoZero','polynomialBridge',
          'native_equivalence','standard_equivalence','reference_equivalence'):
 assert '#print axioms DiophantineConsistency.Natural80EndpointDraft.'+n in s
assert 'sorry' not in s and 'admit' not in s
assert 'theorem exists_zero_iff' in sources['Natural80GammaShift.lean']
assert 'theorem port_bounds' in sources['CompactPortBoundsSlim.lean']
assert 'theorem kernel_model_pos' in sources['StrictK0Symbolic.lean']
assert 'theorem polynomialBridge : PolynomialBridge expression' in sources['Natural81Endpoint.lean']
print(json.dumps({'scope':'pinned source interfaces only; no Lean, iPRA or byte binding',
                  'pinned_sources':len(pins),'all_four_symbolic_ports_explicit':True,
                  'proposed_clients':['sameNoZero','polynomialBridge','native','standard','reference'],
                  'axiom_print_commands_not_executed':7},sort_keys=True,indent=2))
