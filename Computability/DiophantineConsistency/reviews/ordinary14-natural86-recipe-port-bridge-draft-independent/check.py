#!/usr/bin/env python3
"""Independent bounded source/interface check; no Lean or provider use."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
author = root / 'research/ordinary14-natural86-recipe-port-bridge-draft'
pins = {
    'README.md': 'a8e221c5aeb94bf940399b78606d6bf610a0d550f4fd650b78e64994af4332d6',
    'Natural86RecipePorts.lean': '0f7011901bdbe9167e10370f3d16c844c5c123146952be5f6a8d385d9b0c4fec',
    'check_source.py': '19fae7ecb3058f09e91a448b810560fb47b9191d19a5bccbe37706ac17e55393',
    'observation.json': 'e4dce8c77d0873e9a33d040d31c7cd81eb22d7d1a53cbf7e5ae8a84c83995caf',
}
sha = lambda b: hashlib.sha256(b).hexdigest()
for name, digest in pins.items():
    assert sha((author / name).read_bytes()) == digest, name
tail = b'\nIndependent source review: [natural86 recipe-port bridge](../../reviews/ordinary14-natural86-recipe-port-bridge-draft-independent/README.md).\n'
readme = (author / 'README.md').read_bytes()
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == 'e4f50b1055b565fbbf1998ece1a1daf44c990f59b180a539b7be883cf9bde830'
obs = json.loads((author / 'observation.json').read_bytes())
for name, digest in obs['files'].items():
    assert sha((root / name).read_bytes()) == digest, name
for name, digest in {
    'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean': '379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46',
    'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean': '0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414',
}.items():
    assert sha((root / name).read_bytes()) == digest, name
out = subprocess.run([sys.executable, '-I', '-S', '-B', str(author / 'check_source.py')],
                     cwd=root, capture_output=True, check=True, timeout=60)
assert out.stdout == (author / 'observation.json').read_bytes() and not out.stderr

adapter = (author / 'Natural86RecipePorts.lean').read_text()
endpoint = (root / 'research/ordinary14-natural-cancel86-ipra-draft/Natural86Endpoint.lean').read_text()
ports = (root / 'Lean/DiophantineConsistency/Compact44/CompactBytePortsModelIff.lean').read_text()
assembly = (root / 'Lean/DiophantineConsistency/Compact44/CompactFourPortByteAssembly2.lean').read_text()
symbolic = (root / 'Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean').read_text()
natural = (root / 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
collapse = lambda s: re.sub(r'\s+', ' ', s).strip()

assert 'Nat.ofDigits 256 (bytePorts j) : ℕ' in ports
assert 'theorem byteP_eq : byteP = p' in ports
assert 'open CompactFourPortByteAssembly2 CompactSymbolicModelIff' in ports
assert re.search(r'def p\s*:\s*Fin 4 → ℤ', symbolic)
assert '![β,K,L,β+H]' in natural
for item in ('RetainedBetaBytes.betaBytes', 'CompactKernelByteRecipe.bytes',
             'CompactLowByteRecipeData.bytes', 'CompactShiftedHighByteWindow.bytes'):
    assert item in assembly
assert 'CompactFixedBeta.betaNat + highNat' in assembly
assert collapse('(P86NaturalCancel.graph CompactBytePortsModelIff.byteP).output') in collapse(adapter)
assert '(P86NaturalCancel.graph CompactSymbolicModelIff.p).output' in collapse(endpoint)
assert 'rw [CompactBytePortsModelIff.byteP_eq]' in adapter
assert 'positiveShift' not in adapter
for name in ('polynomialBridge', 'native_equivalence', 'standard_equivalence', 'reference_equivalence'):
    pat = r'theorem\s+' + name + r'\s*:\s*(.*?)\s*:=\s*by'
    a = re.search(pat, adapter, re.S)
    e = re.search(r'theorem\s+' + name + r'\s*:\s*(.*?)\s*:=', endpoint, re.S)
    assert a and e and collapse(a.group(1)) == collapse(e.group(1)), name
    assert 'Natural86EndpointDraft.' + name in adapter
assert not re.search(r'\b(sorry|admit|axiom)\b', adapter)
print(json.dumps({'status': 'PASS', 'scope': 'bounded literal source and interface review only',
                  'lean_run': False, 'provider_coherence_checked': False,
                  'physical_byte_binding_checked': False, 'author_receipt_reproduced': True,
                  'matched_endpoint_declarations': 4, 'decoded_port_count': 4},
                 sort_keys=True, indent=2))
