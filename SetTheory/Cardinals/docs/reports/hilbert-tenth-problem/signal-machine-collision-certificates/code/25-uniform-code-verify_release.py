#!/usr/bin/env python3
"""Verify the complete release manifest and nested frozen scientific pins."""
import hashlib
from pathlib import Path, PurePosixPath
import json
from replay import verify_frozen, require

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = 'MANIFEST.sha256'


def inventory():
    files = []
    for p in ROOT.rglob('*'):
        require(not p.is_symlink(), 'Symlink rejected: ' + str(p))
        if p.is_file() and p.name != '__pycache__' and '__pycache__' not in p.parts:
            files.append(p.relative_to(ROOT).as_posix())
    return sorted(files)


def verify():
    path = ROOT / MANIFEST
    require(path.is_file() and not path.is_symlink(), 'Missing manifest')
    rows = {}
    for line in path.read_text().splitlines():
        sha, rel = line.split('  ', 1)
        q = PurePosixPath(rel)
        require(not q.is_absolute() and '..' not in q.parts and str(q) == rel,
                'Unsafe manifest path')
        require(rel not in rows and rel != MANIFEST, 'Duplicate or self manifest row')
        require(len(sha) == 64 and all(c in '0123456789abcdef' for c in sha), 'Invalid digest')
        rows[rel] = sha
    require(inventory() == sorted([MANIFEST, *rows]), 'Release file set differs')
    for rel, sha in rows.items():
        require(hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == sha, 'Hash mismatch: ' + rel)
    frozen = verify_frozen()
    return {'status': 'PASS', 'verified_files': len(rows),
            'manifest_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'frozen_manifests': frozen}


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2, sort_keys=True))
