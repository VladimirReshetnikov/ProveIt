#!/usr/bin/env python3
"""Compare blank-tape startup against the pinned PA196 source seed, bounded."""
from pathlib import Path
import hashlib
import build221 as b
HERE = Path(__file__).resolve().parent
PINS = {'pa196.native.tm': '454254a42a9f9096b72f73ef491107713002ca32f2a51f165eee7ca299283215', 'two-fresh5/candidate.native.tm': '75534c360a43a524382534f4e67bfb556486a68e6d51a1540fd4c75108c372e9'}
for name, digest in PINS.items():
    if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != digest: raise ValueError('input hash mismatch: ' + name)
tables = [b.read_table((HERE / name).read_bytes()) for name in PINS]
bits = set(); state = 74; pos = 0
for _ in range(58154):
    w, d, state = tables[0][state, int(pos in bits)]
    if w: bits.add(pos)
    else: bits.discard(pos)
    pos += d
target = (state, pos, bits)
a = [set(), set()]; q = [74, 74]; head = [0, 0]; first = None
roots = 0
for i in range(1, 58155):
    for j, table in enumerate(tables):
        if q[j] == 254: raise ValueError(('early halt', j, i))
        w, d, nxt = table[q[j], int(head[j] in a[j])]
        if w: a[j].add(head[j])
        else: a[j].discard(head[j])
        head[j] += d; q[j] = nxt
    if q[1] == 84:
        roots += 1
        if (q[1], head[1], a[1]) == target: raise ValueError(('target reached', i))
    if first is None and (q[0] != q[1] or head[0] != head[1] or a[0] != a[1]): first = i
if (first, q, head, list(map(len, a))) != (39, [84, 54], [-2, 42], [66, 151]): raise ValueError('startup mismatch')
for i in range(58155, 10000001):
    if q[1] == 254: raise ValueError(('candidate halted', i))
    w, d, nxt = tables[1][q[1], int(head[1] in a[1])]
    if w: a[1].add(head[1])
    else: a[1].discard(head[1])
    head[1] += d; q[1] = nxt
    if q[1] == 84:
        roots += 1
        if (q[1], head[1], a[1]) == target: raise ValueError(('target reached', i))
print('first divergence:', first, '; original seed step:', 58154)
print('candidate did not reach the exact original seed in first 10000000 steps; root visits:', roots)
print('This bounded comparison does not rule out other correct startup paths.')
