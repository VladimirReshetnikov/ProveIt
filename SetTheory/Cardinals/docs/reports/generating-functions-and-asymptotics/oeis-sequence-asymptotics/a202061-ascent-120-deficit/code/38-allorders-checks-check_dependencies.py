#!/usr/bin/env python3
"""Pin every byte of the complete approved third-order dependency."""
from pathlib import Path
import hashlib
root=Path(__file__).resolve().parents[1]
dep=root/'dependency/third-order'
manifest=dep/'SHA256SUMS'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()=='46235c0b3313375922cd4f0663e1e3bbb470a25384b9841caa5e827e691167a0','Changed third-order manifest'
records={}
for line in manifest.read_text().splitlines():
    digest,name=line.split('  ',1)
    assert name not in records
    records[name]=digest
    assert hashlib.sha256((dep/name).read_bytes()).hexdigest()==digest,name
actual={p.relative_to(dep).as_posix() for p in dep.rglob('*') if p.is_file() and p.name!='SHA256SUMS' and not any(a.startswith('.') or a=='__pycache__' for a in p.relative_to(dep).parts) and p.suffix!='.pyc'}
expected={p for p in records if Path(p).name!='SHA256SUMS'}
assert actual==expected,(actual-expected,expected-actual)
print(f'PASS: pinned third-order manifest and {len(records)} dependency hashes, exact payload set')
