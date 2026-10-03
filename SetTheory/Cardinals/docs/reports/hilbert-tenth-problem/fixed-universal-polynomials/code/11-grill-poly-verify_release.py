#!/usr/bin/env python3
"""Verify the exact report23 distribution; optionally replay without mutation."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
EXCLUDED = {'RELEASE_INVENTORY.json', 'RELEASE_INVENTORY.sha256'}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for part in iter(lambda: f.read(1024 * 1024), b''):
            h.update(part)
    return h.hexdigest()

def verify():
    raw = (ROOT / 'RELEASE_INVENTORY.json').read_bytes()
    anchor = (ROOT / 'RELEASE_INVENTORY.sha256').read_text().strip()
    require(hashlib.sha256(raw).hexdigest() == anchor, 'Release inventory digest mismatch')
    spec = json.loads(raw)
    require(spec['schema'] == 'report23-release-inventory-v1', 'Unsupported inventory schema')
    actual_files, actual_dirs = {}, []
    for path in sorted(ROOT.rglob('*')):
        name = path.relative_to(ROOT).as_posix()
        require(not path.is_symlink(), 'Symlink in release: ' + name)
        if path.is_dir():
            actual_dirs.append(name)
        elif path.is_file():
            if name not in EXCLUDED:
                actual_files[name] = path
        else:
            raise RuntimeError('Non-regular release entry: ' + name)
    require(set(actual_files) == set(spec['files']), 'Release file-set mismatch')
    require(actual_dirs == spec['directories'], 'Release directory-set mismatch')
    for name, path in actual_files.items():
        item = spec['files'][name]
        require(path.stat().st_size == item['bytes'], 'Size mismatch: ' + name)
        require(digest(path) == item['sha256'], 'SHA-256 mismatch: ' + name)
    return {'status': 'PASS_RELEASE_INVENTORY', 'files': len(actual_files) + 2,
            'inventory_sha256': anchor}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--replay', action='store_true')
    args = p.parse_args()
    print(json.dumps(verify(), sort_keys=True), flush=True)
    flags = ['-B'] + (['-O'] if sys.flags.optimize else [])
    cmd = [sys.executable] + flags + [str(ROOT / 'reproducibility' / 'replay.py')]
    if not args.replay:
        cmd.append('--verify-only')
    subprocess.run(cmd, check=True, cwd=ROOT.parent)
    degree_cmd = [sys.executable] + flags + [str(ROOT / 'exact-degree' / 'replay.py')]
    if not args.replay:
        degree_cmd.append('--verify-only')
    subprocess.run(degree_cmd, check=True, cwd=ROOT.parent)
    print(json.dumps(verify(), sort_keys=True), flush=True)
    print('PASS: complete release unchanged after checks', flush=True)

if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, ValueError, OSError, subprocess.CalledProcessError) as exc:
        print('FAIL: ' + str(exc), file=sys.stderr)
        sys.exit(1)
