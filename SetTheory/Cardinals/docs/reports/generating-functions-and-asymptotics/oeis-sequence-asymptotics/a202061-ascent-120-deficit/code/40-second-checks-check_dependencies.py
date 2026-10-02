#!/usr/bin/env python3
"""Pin the entire frozen sharp/foundation dependency to its original manifest."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parents[1]
dep=root/'dependency/sharp-deficit'
manifest=dep/'SHA256SUMS'
expected='be1c77323ab96fc1deee4eee7c23c37b52ed480c17a8ef2d9b267ebffc4cf5c8'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()==expected,'Changed frozen sharp manifest'
records={}
for line in manifest.read_text().splitlines():
    digest,name=line.split('  ',1)
    assert name not in records
    records[name]=digest
    assert hashlib.sha256((dep/name).read_bytes()).hexdigest()==digest,name
actual={p.relative_to(dep).as_posix() for p in dep.rglob('*') if p.is_file() and p.name!='SHA256SUMS' and not any(a.startswith('.') or a=='__pycache__' for a in p.relative_to(dep).parts) and p.suffix!='.pyc'}
expected_files={p for p in records if Path(p).name!='SHA256SUMS'}
assert actual==expected_files,(actual-expected_files,expected_files-actual)
print(f'PASS: pinned frozen manifest and {len(records)} dependency hashes, with exact payload set')
