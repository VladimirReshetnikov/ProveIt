#!/usr/bin/env python3
"""Verify the integrity and exact file set of an extracted Report173 package."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

def verify(root):
    root = Path(root)
    if not root.is_dir() or root.is_symlink():
        raise ValueError('package must be a regular directory')
    entries = list(root.rglob('*'))
    if any(p.is_symlink() or not (p.is_file() or p.is_dir()) for p in entries):
        raise ValueError('package contains a symlink or nonregular entry')
    manifest = json.loads((root / 'SHA256SUMS.json').read_text())
    if not isinstance(manifest, dict):
        raise ValueError('manifest must be an object')
    actual = {p.relative_to(root).as_posix() for p in entries if p.is_file()}
    if actual != set(manifest) | {'SHA256SUMS.json'}:
        raise ValueError('package file set differs from manifest')
    for name, expected in manifest.items():
        rel = Path(name)
        if rel.is_absolute() or '..' in rel.parts or rel.as_posix() != name or '\\' in name:
            raise ValueError('unsafe manifest path')
        got = hashlib.sha256((root / rel).read_bytes()).hexdigest()
        if got != expected:
            raise ValueError('SHA-256 mismatch: ' + name)
    return len(manifest)

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('directory', nargs='?', default=Path(__file__).resolve().parent)
    args = p.parse_args()
    try:
        count = verify(args.directory)
    except (OSError, ValueError) as exc:
        p.exit(1, 'FAIL: ' + str(exc) + '\n')
    print(json.dumps({'status': 'PASS', 'verified_files': count}, sort_keys=True))
