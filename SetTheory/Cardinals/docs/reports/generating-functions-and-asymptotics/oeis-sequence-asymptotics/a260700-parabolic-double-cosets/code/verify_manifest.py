#!/usr/bin/env python3
"""Check SHA-256 and byte counts of every declared package file, without executing it."""
import hashlib
import json
from pathlib import Path,PurePosixPath
import sys
ROOT=Path(__file__).resolve().parent.parent
manifest=json.loads((ROOT/'MANIFEST.json').read_text())
for name,entry in manifest['files'].items():
    path=PurePosixPath(name)
    if path.is_absolute() or any(p in ('','..','.') for p in path.parts) or '\\' in name:
        raise SystemExit('Unsafe manifest path: '+name)
    file=ROOT/path
    if file.is_symlink() or not file.is_file() or ROOT not in file.resolve().parents:
        raise SystemExit('Missing, linked or unsafe file: '+name)
    data=file.read_bytes()
    if len(data)!=entry['bytes'] or hashlib.sha256(data).hexdigest()!=entry['sha256']:
        raise SystemExit('Checksum mismatch: '+name)
print('PASS: verified',len(manifest['files']),'declared files')
