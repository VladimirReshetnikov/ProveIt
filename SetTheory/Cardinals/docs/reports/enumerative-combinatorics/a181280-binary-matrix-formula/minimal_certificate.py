#!/usr/bin/env python3
"""Exact twelve-value certificate. Python 3.10+, standard library only.
The article proves the all-n implication; this code uses tuple states.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product

pairs = [(i, j) for i in range(4) for j in range(i, 4)]
states = list(product((False, True), repeat=3))
columns = list(product((0, 1), repeat=4))
full = (True, True, True)

def accepted(g):
    matrix = [[0] * 4 for _ in range(4)]
    for (i, j), bit in zip(pairs, g):
        matrix[i][j] = matrix[j][i] = bit
    return matrix[0] > matrix[1] > matrix[2] > matrix[3]

def formula(n):
    return (F(16**n, 512)
            + F((288*n - 3473)*8**n, 147456)
            - F(113*(-8)**n, 49152)
            + F((6*n*n - 219*n + 820)*4**n, 6144)
            - F((13*n - 164)*(-4)**n, 6144)
            - F((3*n + 32)*2**n, 288))

edges = {}
for state in states:
    edges[state] = []
    for v in columns:
        if any(not state[i] and v[i] > v[i+1] for i in range(3)):
            continue
        target = tuple(state[i] or v[i] < v[i+1] for i in range(3))
        delta = tuple(v[i] * v[j] for i, j in pairs)
        edges[state].append((target, delta))

accepting = {g for g in product((0, 1), repeat=10) if accepted(g)}
if len(accepting) != 48:
    raise AssertionError('Acceptance predicate is incorrect')

tab = {((False, False, False), (0,) * 10): 1}
counts = []
for n in range(16):
    counts.append(sum(value for (state, gram), value in tab.items()
                      if state == full and gram in accepting))
    if n == 15:
        break
    nxt = defaultdict(int)
    for (state, gram), value in tab.items():
        for target, delta in edges[state]:
            new_gram = tuple(x ^ y for x, y in zip(gram, delta))
            nxt[target, new_gram] += value
    tab = nxt

if counts[:4] != [0, 0, 0, 0]:
    raise AssertionError('Initial prefix differs')
for n in range(4, 16):
    if counts[n] != formula(n):
        raise AssertionError(f'The certificate fails at n={n}')
    print(n, counts[n], 'OK')
print('All twelve exact certificate values match.')
