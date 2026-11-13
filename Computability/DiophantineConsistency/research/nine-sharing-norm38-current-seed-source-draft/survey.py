#!/usr/bin/env python3
"""Read-only point-in-time .olean overlay comparison, not a build gate."""
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
A = Path('/tmp/nine-sharing-norm38-seed-source-composition-check-20261106/lib')
B = Path('/tmp/nine-sharing-norm38-current-four-cast-instantiation-check-20261105/lib')
PINS = {
    PROJECT / 'research/nine-sharing-norm38-seed-source-composition-draft/attempt01/state.json':
        '9bef14e22cf04c4a9b0810dcd71866c40401a1f49d369e068151dfe2b111ce59',
    PROJECT / 'research/nine-sharing-norm38-current-four-cast-instantiation-check/attempt01/state.json':
        'bad562eeca80d04d60ede99deb281686134612c3c091230a7326dd850b5deabf',
    A / 'DiophantineConsistency/Norm38SeedSource.olean':
        'e4a4092b123ed7dd0b3c6c2d7e88af9447ca3f1a941ded0dba3f656a1edfd766',
    B / 'DiophantineConsistency/Norm38CurrentFourCastInstantiation.olean':
        '4f6ea58e06ea51ee24b830daba85da258de463e51587b37e89cfb1dbefffac95',
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
