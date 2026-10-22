"""Verify the delivered byte manifest. Does not compile or execute constructions."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
manifest=json.loads((root/'SHA256SUMS.json').read_text())
for name,want in manifest.items():
    path=(root/name).resolve()
    if not path.is_relative_to(root):raise ValueError('Invalid relative path')
    if hashlib.sha256(path.read_bytes()).hexdigest()!=want:
        raise ValueError('Hash mismatch: '+name)
print('PASS:',len(manifest),'delivered file hashes')
