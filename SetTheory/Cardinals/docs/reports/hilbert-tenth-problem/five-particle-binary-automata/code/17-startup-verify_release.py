#!/usr/bin/env python3
"""Verify exact shipped inventory and SHA-256 byte pins without writing files."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXCLUDED = {'release-manifest.json', 'release-manifest.json.sha256'}

def require(condition, message):
    if not condition:
        raise SystemExit(message)

raw = (ROOT / 'release-manifest.json').read_bytes()
expected_manifest = (ROOT / 'release-manifest.json.sha256').read_text().split()[0]
require(hashlib.sha256(raw).hexdigest() == expected_manifest, 'Manifest checksum mismatch')
manifest = json.loads(raw)
files = manifest['files']
require(not any(p.is_symlink() for p in ROOT.rglob('*')), 'Symlinks are not part of this release')
actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()} - EXCLUDED
require(actual == set(files), 'File inventory mismatch: missing=%r extra=%r' % (sorted(set(files)-actual), sorted(actual-set(files))))
for name, expected in sorted(files.items()):
    p = Path(name)
    require(not p.is_absolute() and '..' not in p.parts, 'Unsafe manifest path')
    data = (ROOT / p).read_bytes()
    require(len(data) == expected['bytes'], 'Size mismatch: ' + name)
    require(hashlib.sha256(data).hexdigest() == expected['sha256'], 'SHA-256 mismatch: ' + name)
print(json.dumps({'status':'PASS','files_verified':len(files),'manifest_sha256':expected_manifest}, indent=2))
