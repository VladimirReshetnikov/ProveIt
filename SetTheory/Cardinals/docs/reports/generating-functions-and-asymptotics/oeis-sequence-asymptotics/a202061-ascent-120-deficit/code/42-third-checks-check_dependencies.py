#!/usr/bin/env python3
"""Pin every byte of the complete approved second-order dependency."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parents[1]
dep=root/'dependency/second-order'
manifest=dep/'SHA256SUMS'
expected='a05af510251956f138a54be2aec3517dd34fd649e820d3227556d84bfcb5f7d6'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()==expected,'Changed second-order manifest'
records={}
for line in manifest.read_text().splitlines():
    digest,name=line.split('  ',1)
    assert name not in records
    records[name]=digest
    assert hashlib.sha256((dep/name).read_bytes()).hexdigest()==digest,name
actual={p.relative_to(dep).as_posix() for p in dep.rglob('*') if p.is_file() and p.name!='SHA256SUMS' and not any(a.startswith('.') or a=='__pycache__' for a in p.relative_to(dep).parts) and p.suffix!='.pyc'}
expected_files={p for p in records if Path(p).name!='SHA256SUMS'}
assert actual==expected_files,(actual-expected_files,expected_files-actual)
print(f'PASS: pinned second-order manifest and {len(records)} dependency hashes, exact payload set')
