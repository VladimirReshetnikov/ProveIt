#!/usr/bin/env python3
"""Read-only point-in-time .olean overlay comparison, not a build gate."""
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent.parent
A = Path('/tmp/nine-sharing-norm38-current-seed-source-check-20261106/lib')
B = Path('/tmp/nine-sharing-seed38-current-jones-retry01-20261105/lib')
PINS = {
    PROJECT / 'research/nine-sharing-norm38-current-seed-source-draft/attempt01/state.json':
        '20c2e1ba07a2131cee639d2e872498a006ce150d22f72ba0cab7fcec3342a64c',
    PROJECT / 'research/nine-sharing-seed38-current-jones-retry01/attempt01/state.json':
        'ca43e7d3588626c70043b8909d6cbf2762784a3132d079ae22d9329485b32d1f',
    A / 'DiophantineConsistency/Norm38CurrentSeedSource.olean':
        '176750b96fc712e1827066d61958dd164852427587d599d5846aeec4d1207d10',
    B / 'DiophantineConsistency/SharingSeed38CurrentJones.olean':
        '9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e',
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
