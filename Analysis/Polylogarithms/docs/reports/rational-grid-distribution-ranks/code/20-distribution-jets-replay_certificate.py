#!/usr/bin/env python3
"""Replay the S4 linear-algebra certificate with standard-library arithmetic."""
import json
from fractions import Fraction as Q
from pathlib import Path
from distribution import rank

p = Path(__file__).resolve().parents[1]/'certificates'/'s4_rowspace_obstruction.json'
d = json.loads(p.read_text())
rows = [[Q(x) for x in row] for row in d['rows']]
target = [Q(x) for x in d['target']]
w = d['witness']
assert all(sum(x*y for x,y in zip(row,w)) == 0 for row in rows)
assert sum(x*y for x,y in zip(target,w)) == 768
assert rank(rows) == 20
assert rank(rows+[target]) == 21
print('PASS: 96 exact annihilations, rank 20, augmented rank 21, target pairing 768.')
