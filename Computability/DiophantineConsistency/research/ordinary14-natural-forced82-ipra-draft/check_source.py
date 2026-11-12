#!/usr/bin/env python3
"""Pin and inspect proposed endpoint clients; this does not run Lean."""
from pathlib import Path
import hashlib, json
P = Path(__file__).resolve().parent
D = P.parents[1]
pins = {
    P / 'Natural82Endpoint.lean': '2985f570497227742b56097bbbc184563ae7aa136b8da89e6e201db141a8e13b',
    D / 'research/ordinary14-natural-forced82-predecessor-draft/GraphPredecessors82.lean': '7972ddb132643d0fd46bfd66e200bdf80a48e5d0df1b75f719b9c4ef5db5de54',
    D / 'research/ordinary14-natural-forced82-ring-bridge-draft/Natural82Model.lean': 'e10b5e7dcc6169fd4730f3bf4e9058081efa1ac4e628de382dcbfc2dcf244854',
    D / 'research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean': 'f3755518938e8d3bf4bcb1d33e2dbbfcdc6f2458a414921b1d03ac244503f47c',
    D / 'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean': '379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
    D / 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean': 'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea',
}
sources = {}
for path, digest in pins.items():
    b = path.read_bytes()
    assert hashlib.sha256(b).hexdigest() == digest, str(path)
    sources[path.name] = b.decode()
s = sources['Natural82Endpoint.lean']
for needle in (
    'import GraphPredecessors82', 'import Natural86Endpoint',
    '(P82NaturalForced.graph CompactSymbolicModelIff.p).output',
    'theorem symbolic_beta_representation', '(CompactSymbolicModelIff.p 0 : DiffRing V)',
    'ι (CompactFixedBeta.betaNat : V)', 'theorem symbolic_beta_positive',
    'CompactFixedBeta.bounds (V:=V) 1',
    'SameNoZero expression Natural86EndpointDraft.expression',
    'exists_zero_iff_of_predecessors', 'predecessors_of_zero',
    'symbolic_beta_representation symbolic_beta_positive hv',
    'HAExpressionNoZeroEquiv.bridge expression Natural86EndpointDraft.expression',
    'sameNoZero Natural86EndpointDraft.polynomialBridge',
    'IPRAExpressionNative.equivalence_of_bridge expression polynomialBridge',
    'IPRAStandardTheory.provable_iff', 'IPRAReferenceInductionConversion.nativeToReference',
): assert needle in s, needle
for theorem in ('sameNoZero', 'polynomialBridge', 'native_equivalence',
                'standard_equivalence', 'reference_equivalence'):
    assert f'#print axioms DiophantineConsistency.Natural82EndpointDraft.{theorem}' in s
assert 'sorry' not in s and 'admit' not in s
assert 'def betaNat : ℕ := 2^(67*8807)-1' in sources['CompactFixedBeta.lean']
assert 'def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat' in sources['CompactSymbolicModelIff.lean']
assert 'theorem predecessors_of_zero' in sources['GraphPredecessors82.lean']
assert 'theorem exists_zero_iff_of_predecessors' in sources['Natural82Model.lean']
assert 'theorem polynomialBridge : PolynomialBridge expression' in sources['Natural86Endpoint.lean']
print(json.dumps({'scope': 'source shape and pinned dependencies only; no Lean or endpoint proof',
                  'pinned_files': len(pins), 'selected_symbolic_beta': '2^(67*8807)-1',
                  'proposed_clients': ['sameNoZero', 'polynomialBridge', 'native', 'standard', 'reference'],
                  'predecessor_link_is_source_only': True}, sort_keys=True, indent=2))
