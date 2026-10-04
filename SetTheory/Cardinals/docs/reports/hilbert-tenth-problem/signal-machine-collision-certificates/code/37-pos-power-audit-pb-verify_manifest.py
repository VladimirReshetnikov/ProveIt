#!/usr/bin/env python3
"""Read-only complete dossier manifest verification; no scientific execution."""
import hashlib
import json
import stat
from pathlib import Path

root = Path(__file__).resolve().parent
manifest_path = root / 'CANONICAL_MANIFEST.json'
raw = manifest_path.read_bytes()
manifest = json.loads(raw)
canonical = (json.dumps(manifest,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode('utf-8')
if raw != canonical:
    raise SystemExit('FAIL: noncanonical manifest encoding')
if manifest['excluded_files'] != ['CANONICAL_MANIFEST.json']:
    raise SystemExit('FAIL: unexpected manifest exclusions')
paths = list(root.rglob('*'))
if any(p.is_symlink() for p in paths):
    raise SystemExit('FAIL: symlinks are not permitted')
actual_files = {p.relative_to(root).as_posix() for p in paths if p.is_file()}
expected_files = {row['path'] for row in manifest['files']} | {'CANONICAL_MANIFEST.json'}
if actual_files != expected_files:
    raise SystemExit('FAIL: file inventory mismatch')
actual_dirs = {'.'} | {p.relative_to(root).as_posix() for p in paths if p.is_dir()}
if actual_dirs != set(manifest['directories']):
    raise SystemExit('FAIL: directory inventory mismatch')
for row in manifest['files']:
    p = root / row['path']
    if p.resolve() != p or root not in p.parents:
        raise SystemExit('FAIL: unsafe manifest path')
    data = p.read_bytes()
    if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
        raise SystemExit('FAIL: bytes/hash mismatch: '+row['path'])
for name in actual_files:
    if stat.S_IMODE((root/name).stat().st_mode) != 0o444:
        raise SystemExit('FAIL: file not mode 0444: '+name)
for name in actual_dirs:
    if stat.S_IMODE((root/name).stat().st_mode) != 0o555:
        raise SystemExit('FAIL: directory not mode 0555: '+name)
print('PASS: '+str(len(actual_files))+' files, '+str(len(actual_dirs))+' directories, exact hashes and read-only modes')
print('Manifest SHA-256: '+hashlib.sha256(raw).hexdigest())
