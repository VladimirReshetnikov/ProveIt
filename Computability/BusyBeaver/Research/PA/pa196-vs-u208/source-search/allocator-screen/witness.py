#!/usr/bin/env python3
"""Concrete bounded counterexample to treating prefix dispatch as runtime proof."""
from pathlib import Path
import hashlib
import build221 as b

HERE = Path(__file__).resolve().parent
PINS = {
    'pa196.native.tm': '454254a42a9f9096b72f73ef491107713002ca32f2a51f165eee7ca299283215',
    'one-fresh1/candidate.native.tm': 'e5b3a27df424a10a26173365ce58b75bb30e829be656af35cae07943ecc3d3f7',
}
for name, digest in PINS.items():
    if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != digest:
        raise ValueError('input hash mismatch: ' + name)
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
def tape(path, gap, values):
    positions = {-1}; positions.update(i for i, c in enumerate(path) if c == '1')
    positions.add(gap); cur = gap + 1; physical = [0] * 9
    for i, j in enumerate(PHY): physical[j] = values[i]
    for value in physical + [0]:
        cur += 1; positions.update(range(cur, cur + value + 1)); cur += value + 1
    return positions

def trial(name):
    table = b.read_table((HERE / name).read_bytes())
    bits = tape('01000', 56, [0] * 9); expected = tape('0101', 56, [0] * 9)
    q = 84; head = 0
    for step in range(1, 100001):
        w, d, q = table[q, int(head in bits)]
        if w: bits.add(head)
        else: bits.discard(head)
        head += d
        if q == 84 and head == 0 and bits == expected: return ('return', step)
        if q == 254: return ('halt', step)
    return ('no expected return in bound', 100000)
tables = [b.read_table((HERE / name).read_bytes()) for name in PINS]
a = [tape('01000', 56, [0] * 9) for _ in range(2)]; q = [84,84]; head = [0,0]
for step in range(1,10):
    if step == 9:
        if (q, head, int(head[0] in a[0])) != ([11,11], [4,4], 0): raise ValueError(('witness precondition',q,head,int(head[0] in a[0])))
        if (tables[0][11,0], tables[1][11,0]) != ((0,-1,26),(0,1,29)): raise ValueError('divergent rows')
    for i in range(2):
        w, d, nxt = tables[i][q[i], int(head[i] in a[i])]
        if w: a[i].add(head[i])
        else: a[i].discard(head[i])
        q[i] = nxt; head[i] += d
    equal = (q[0], head[0], a[0]) == (q[1], head[1], a[1])
    if equal != (step < 9): raise ValueError(('unexpected divergence', step))
print('first divergence: ninth transition, after eight completed transitions, native row (11,0)')
original = trial('pa196.native.tm')
candidate = trial('one-fresh1/candidate.native.tm')
if original != ('return', 526) or candidate != ('no expected return in bound', 100000):
    raise ValueError((original, candidate))
print('original:', original, '; candidate:', candidate)
print('A finite mismatch, not a proof about eventual blank-tape halting.')
