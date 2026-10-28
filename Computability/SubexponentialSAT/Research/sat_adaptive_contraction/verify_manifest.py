#!/usr/bin/env python3
"""Check delivered bytes before rebuilding or rerunning generators."""
from pathlib import Path
import hashlib
import json

root=Path(__file__).resolve().parent
manifest=json.loads((root/'MANIFEST.sha256.json').read_text())
errors=[]
for name,expected in manifest['files'].items():
    p=root/name
    if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
        errors.append(name)
if errors:
    raise SystemExit('File mismatch: '+', '.join(errors))
print(f"PASS: {len(manifest['files'])} packaged file hashes match.")
