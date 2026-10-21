#!/usr/bin/env python3
"""Verify the exact delivered file set and SHA-256 bytes; not a proof checker."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
manifest=root/'MANIFEST.sha256.json'
data=json.loads(manifest.read_text())
failures=[]
expected=set()
for entry in data['files']:
    rel=entry['path']
    q=Path(rel)
    if q.is_absolute() or '..' in q.parts:
        failures.append(f'unsafe manifest path: {rel}')
        continue
    expected.add(rel)
    p=root/q
    if not p.is_file():
        failures.append(f'missing: {rel}')
        continue
    raw=p.read_bytes()
    if len(raw)!=entry['size'] or hashlib.sha256(raw).hexdigest()!=entry['sha256']:
        failures.append(f'mismatch: {rel}')
actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
extra=actual-expected-{'MANIFEST.sha256.json'}
if extra: failures.append('unlisted files: '+', '.join(sorted(extra)))
if failures:
    print('INTEGRITY CHECK FAILED')
    print('\n'.join(failures))
    sys.exit(1)
print(f'PASS: {len(expected)} files match the delivered SHA-256 manifest.')
