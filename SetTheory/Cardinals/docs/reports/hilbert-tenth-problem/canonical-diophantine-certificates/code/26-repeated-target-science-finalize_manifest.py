#!/usr/bin/env python3
"""Record this new packet and check approved predecessor pins, read-only."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parent
SHARED=ROOT.parent
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

expected={
    'sandpile-target-firing-20261004/build_target_certificate.py':'6a9ced103676ce7ba0b052e00779177fb522101fc5479866273e3908d299c975',
    'sandpile-target-firing-20261004/ARCHITECTURE.md':'dabbe1685bb050eca578c29472a00426c940df6002c383fe5c3a558797bf93c9',
    'sandpile-target-firing-20261004/SOURCE_NOTES.md':'ab6e86e29f71815b839687f2eef46b264fc9b0c3f1a4226ef2507c9be6c88c88',
    'sandpile-target-firing-20261004/evidence/polynomial-dag.json':'352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504',
    'sandpile-target-independent-audit-20261004/AUDIT.md':'8bfb480bb7ccf297774f2f0ba4d5292e0ec621056680b5dd4f16b90c1b5ad27d',
}
for relative,pin in expected.items():assert digest(SHARED/relative)==pin,relative
assert digest(ROOT/'evidence/polynomial-dag.json')=='7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6'
assert digest(ROOT/'build_repeated_certificate.py')=='c37f455dc5a9a673fb2b980fb5dc41103f9a85e82a97c24cae296ed580fe9928'
files={str(p.relative_to(ROOT)):digest(p) for p in sorted(ROOT.rglob('*'))
       if p.is_file() and p!=ROOT/'evidence/manifest.json' and '__pycache__' not in p.parts}
manifest=dict(status='author proof/source complete; independent component reviews pass',
              repeated_packet_files=files,approved_predecessor_pins_verified=expected,
              constructive_pell_dependency=dict(commit='ac77769fabe23cb237559e7f56578dbead91499f',
                   file='Mathlib/NumberTheory/PellMatiyasevic.lean',
                   sha256='993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a'),
              upstream_scripts_saved_schedules_or_lean_executed=False,
              full_external_adversarial_audit='separately coordinated by parent; not claimed here')
(ROOT/'evidence/manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print(json.dumps(manifest,sort_keys=True,indent=2))
