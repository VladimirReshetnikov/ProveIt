#!/usr/bin/env python3
"""Merge fresh Lean objects, rejecting every unequal duplicate."""
import hashlib
import shutil
import sys
from pathlib import Path

if len(sys.argv) < 3:
    raise SystemExit('usage: merge_objects.py OUTPUT INPUT...')
out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
counts = [0, 0]
def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.digest()
for arg in sys.argv[2:]:
    root = Path(arg)
    for src in root.rglob('*'):
        if not src.is_file():
            continue
        rel = src.relative_to(root)
        if rel.parts[0] == 'DiophantineConsistency':
            continue  # Supplied through the separately pinned project overlay.
        if not any(str(rel).endswith(s) for s in ('.olean', '.olean.private', '.olean.server', '.ir')):
            continue
        dst = out / rel
        if dst.exists():
            if digest(src) != digest(dst):
                raise SystemExit(f'conflicting Lean object: {rel} from {root}')
            counts[1] += 1
        else:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
            counts[0] += 1
print(f'Object overlay: {counts[0]} unique files, {counts[1]} matching duplicates')
