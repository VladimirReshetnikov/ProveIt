#!/usr/bin/env python3
"""Read-only point-in-time .olean overlay comparison, not a build gate."""
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
A = Path('/tmp/nine-sharing-norm38-current-nine-source-check-20261106/lib')
B = Path('/tmp/nine-sharing-norm38-current-source-to-seed-20261106/lib')
PINS = {
    PROJECT / 'research/nine-sharing-norm38-current-nine-source-draft/attempt01/state.json':
        '0849e547567401e7d0a55f8edd07cae8253fd22d8b1d83f05dbb94ab8b40540a',
    PROJECT / 'research/nine-sharing-norm38-current-source-to-seed/attempt01/state.json':
        '706bff9dd72de8b197bca5e69a7a0b91f6138dd7741bf419115865ac94612eb6',
    A / 'DiophantineConsistency/Norm38CurrentNineSource.olean':
        '5e984b94a1e43d0f52d59408a35f550da9908a13beae0e184190ad940be9a6d8',
    B / 'DiophantineConsistency/Norm38CurrentSourceToSeed.olean':
        '8963b7bb31156f726981321e3541eb9b122046381e4457393f63d530c78bb6ca',
}


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def inventory(root):
    if not root.is_dir() or root.is_symlink():
        raise RuntimeError(('bad root', str(root)))
    out = {}
    def onerror(exc):
        raise exc
    for base, dirs, files in os.walk(root, followlinks=False, onerror=onerror):
        for d in dirs:
            if (Path(base) / d).is_symlink():
                raise RuntimeError(('symlink directory', str(Path(base) / d)))
        for name in files:
            if not name.endswith('.olean'):
                continue
            path = Path(base) / name
            if not path.is_file():
                raise RuntimeError(('not a file', str(path)))
            out[str(path.relative_to(root))] = {
                'sha256': sha(path), 'realpath': str(path.resolve(strict=True))}
    return out


for path, expected in PINS.items():
    actual = sha(path)
    if actual != expected:
        raise RuntimeError(('pin mismatch', str(path), actual, expected))

a, b = inventory(A), inventory(B)
shared = sorted(a.keys() & b.keys())
mismatches = [key for key in shared if a[key] != b[key]]
if mismatches:
    raise RuntimeError(('shared content or realpath mismatch', mismatches))
print(json.dumps({
    'scope': 'point-in-time .olean contents and resolved paths only; no Lean build',
    'a_root': str(A), 'b_root': str(B),
    'a_count': len(a), 'b_count': len(b), 'shared_count': len(shared),
    'shared_mismatches': mismatches,
    'a_only': {key: a[key] for key in sorted(a.keys() - b.keys())},
    'b_only': {key: b[key] for key in sorted(b.keys() - a.keys())},
    'pins': {str(k): v for k, v in PINS.items()},
}, indent=2, sort_keys=True))
