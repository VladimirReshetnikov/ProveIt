#!/usr/bin/env python3
"""Independent read-only inventories; never import input-tree programs."""
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

BASE = Path('/workspace/shared/report69-independent-release-tool-review-20261004')
CANDIDATE = Path('/workspace/shared/report69-tool-review-candidate-v5')
ROOTS = [CANDIDATE] + [Path('/workspace/shared') / name for name in (
    'two-witness-tensor-compiler-20261004', 'three-witness-bounded-halting-20261004',
    'three-witness-independent-audit-20261004', 'positive-power12-continuation-20261004',
    'independent-power12-audit-20261004', 'report66-bounded-certificates-counting-release-20261004',
    'report67-power-reductions-release-20261004', 'report68-gap-statistics-release-20261004',
    'independent-low-arity-audit-20261004', 'interpolation-exact-degree-20261004',
    'interpolation-exact-degree-independent-audit-20261004')]

def inventory(root):
    rows = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        row = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
        if stat.S_ISREG(s.st_mode):
            with p.open('rb') as stream:
                raw = stream.read()
            row.update(kind='file', bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(), nlink=s.st_nlink)
        elif stat.S_ISDIR(s.st_mode):
            row['kind'] = 'directory'
        elif stat.S_ISLNK(s.st_mode):
            row.update(kind='symlink', target=os.readlink(p))
        else:
            raise ValueError('Nonregular preserved source: ' + str(p))
        rows[str(p)] = row
    return rows

def main():
    tag = sys.argv[1]
    assert tag in ('before', 'after')
    value = {str(p): inventory(p) for p in ROOTS}
    target = BASE / ('PRESERVATION_' + tag.upper() + '.json')
    with target.open('x') as stream:
        json.dump(value, stream, sort_keys=True, indent=2)
        stream.write('\n')
    if tag == 'after':
        before = json.loads((BASE / 'PRESERVATION_BEFORE.json').read_text())
        changed = {root: [p for p in set(before[root]) | set(value[root]) if before[root].get(p) != value[root].get(p)] for root in value}
        assert not any(changed.values()), changed
    print(json.dumps({'status': 'PASS', 'phase': tag, 'roots': len(value), 'entries': sum(len(v) for v in value.values()), 'sha256': hashlib.sha256(target.read_bytes()).hexdigest()}))

if __name__ == '__main__':
    main()
