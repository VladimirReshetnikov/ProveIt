#!/usr/bin/env python3
"""Read-only point-in-time .olean overlay comparison, not a build gate."""
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
A = Path('/tmp/nine-sharing-norm38-current-existential-iff-check-20261106/lib')
B = Path('/tmp/nine-sharing-norm38-current-source-cast-instantiation-20261106/lib')
PINS = {
    PROJECT / 'research/nine-sharing-norm38-current-existential-iff-draft/attempt01/state.json':
        'dcbe82fca2f8c866e301d62281696fed13c33ca9240449b784e8439510674ba9',
    PROJECT / 'research/nine-sharing-norm38-current-source-cast-instantiation/attempt01/state.json':
        'ce4c75e2c8f603965d6bfc6f8038a0299a54163b22d78b01afc48c38a70fda27',
    A / 'DiophantineConsistency/Norm38CurrentExistentialIff.olean':
        'ff60f85e32694d66ed4fbbaa83e4b84778bb6655fc90a4bc35e621181dca4786',
    B / 'DiophantineConsistency/Norm38CurrentSourceFourCasts.olean':
        'd0419dac500817ece12c1d6d4d4a90ab78afb45fe62447a2d2311a9b1d980a43',
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
