#!/usr/bin/env python3
"""Illustrate little-endian Blocks digits and a non-covering orbit; no Lean."""
import json
N, s = 6, 2
orbit = [(t*s) % N for t in range(N)]
rows = [10, 200, 942, 10, 200, 942]
W = sum(row * 1024**t for t, row in enumerate(rows))
assert W < 2**(10*N)
assert [(W // 1024**t) % 1024 for t in range(N)] == rows
assert len(set(orbit)) == 3 < N
print(json.dumps({'N': N, 's': s, 'orbit': orbit, 'row_ids': rows, 'W': W,
                  'covered_blocks': len(set(orbit)), 'lean_launched': False},
                 indent=2, sort_keys=True))
