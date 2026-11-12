#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json

p = Path(__file__).resolve().parent
d = p.parents[1]
files = {
    'adapter': p / 'Natural86RecipePorts.lean',
    'endpoint': d / 'research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean',
    'byte_tuple': d / 'Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean',
    'decode_ports': d / 'Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean',
    'beta_decode': d / 'Lean/DiophantineConsistency/Compact44/RetainedBetaBytes.lean',
    'kernel_decode': d / 'Lean/DiophantineConsistency/Compact44/CompactKernelByteRecipe.lean',
    'low_decode': d / 'Lean/DiophantineConsistency/Compact44/CompactLowByteAssembly.lean',
    'high_decode': d / 'Lean/DiophantineConsistency/Compact44/CompactShiftedHighByteAssembly.lean',
}
s = {k: f.read_text() for k, f in files.items()}
for term in ('(P86NaturalCancel.graph CompactBytePortsModelIff.byteP).output',
             'expression = Natural86EndpointDraft.expression',
             'rw [CompactBytePortsModelIff.byteP_eq]',
             'Natural86EndpointDraft.polynomialBridge',
             'Natural86EndpointDraft.native_equivalence',
             'Natural86EndpointDraft.standard_equivalence',
             'Natural86EndpointDraft.reference_equivalence'):
    assert term in s['adapter'], term
assert 'positiveShift expression' not in s['adapter']
assert '(P86NaturalCancel.graph CompactSymbolicModelIff.p).output' in s['endpoint']
assert 'theorem byteP_eq : byteP = p' in s['byte_tuple']
assert 'congrFun decode_ports j' in s['byte_tuple']
for term in ('theorem decode_ports', 'RetainedBetaBytes.decode_betaBytes',
             'CompactKernelByteRecipe.decode_bytes', 'CompactLowByteAssembly.decode_bytes',
             'CompactShiftedHighByteAssembly.decode_bytes',
             'CompactFixedBeta.betaNat + highNat'):
    assert term in s['decode_ports'], term
for k in ('beta_decode', 'kernel_decode', 'low_decode', 'high_decode'):
    assert 'theorem decode_' in s[k], k
print(json.dumps({'scope': 'literal source interfaces and file hashes only; no Lean or physical-byte binding',
                  'lean_run': False,
                  'files': {str(f.relative_to(d)): hashlib.sha256(f.read_bytes()).hexdigest()
                            for f in files.values()}}, indent=2, sort_keys=True))
