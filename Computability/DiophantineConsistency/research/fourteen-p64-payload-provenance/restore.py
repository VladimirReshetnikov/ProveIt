#!/usr/bin/env python3
"""Restore missing P64 package paths from their exact pinned Git blobs.

Existing paths are checked, never overwritten. Output is an auditable JSON
record; this does not prove a Lean-to-payload equality.
"""
import hashlib
import json
import os
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('assertions required; do not use Python -O')
ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
PACKAGE = ROOT / 'Computability/DiophantineConsistency/con-zfc-diophantine-forms/64-structural-reductions/positive14'
pins_path = PACKAGE / 'SOURCE_PINS.json'
pin_bytes = pins_path.read_bytes()
pins = json.loads(pin_bytes)['files']
assert len(pins) == 40
prepared = []
for entry in pins:
    relative = Path(entry['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    path = PACKAGE / relative
    for parent in path.parents:
        if parent == PACKAGE:
            break
        if os.path.lexists(parent):
            assert parent.is_dir() and not parent.is_symlink(), f'unsafe parent: {parent}'
    info = subprocess.check_output(['git', 'ls-tree', entry['commit'], '--', entry['source_path']], text=True).strip()
    left, found_path = info.split('\t', 1)
    mode, kind, oid = left.split()
    assert found_path == entry['source_path'] and kind == 'blob' and oid == entry['git_blob_sha1']
    assert mode in ('100644', '100755')
    data = subprocess.check_output(['git', 'cat-file', 'blob', oid])
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    existed = os.path.lexists(path)
    if existed:
        assert path.is_file() and not path.is_symlink() and path.read_bytes() == data, f'existing path differs: {path}'
    prepared.append((entry, path, mode, data, existed))

restored, present = [], []
for entry, path, mode, data, existed in prepared:
    if existed:
        present.append(entry['path'])
        continue
    path.parent.mkdir(parents=True, exist_ok=True)
    # Exclusive creation avoids silently replacing a path added after preflight.
    with path.open('xb') as f:
        f.write(data)
    if mode == '100755':
        path.chmod(0o755)
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry['sha256']
    restored.append({'path': entry['path'], 'sha256': entry['sha256'],
                     'git_blob_sha1': entry['git_blob_sha1'], 'mode': mode, 'bytes': len(data)})
print(json.dumps({'status': 'PASS', 'source_pins_sha256': hashlib.sha256(pin_bytes).hexdigest(),
                  'restored_count': len(restored), 'existing_count': len(present),
                  'restored': restored, 'existing': present,
                  'scope': 'Exact pinned Git blobs and package-path bytes; no Lean port equality.'}, indent=2, sort_keys=True))
