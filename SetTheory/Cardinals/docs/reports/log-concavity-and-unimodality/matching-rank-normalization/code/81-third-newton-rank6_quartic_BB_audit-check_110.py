#!/usr/bin/env python3
"""Independent exact BB (J,K,H)=(1,1,0) Schur reconstruction."""
from itertools import combinations, permutations
from pathlib import Path
import json
import sympy as s

p, m, q, h = s.symbols('p m q h')


def matched(columns, slots):
    return any(all(mask & (1 << coordinate) for mask, coordinate in zip(columns, perm))
               for perm in permutations(slots))


def pairs(S, T):
    return sum(matched((S, T), I) for I in combinations(range(3), 2))


def triple(S, T, U):
    return int(matched((S, T, U), (0, 1, 2)))


def equal(left, right, label):
    difference = s.cancel(left - right)
    if difference != 0:
        raise ArithmeticError((label, difference))


E = p + m
x = q + h
r = s.Matrix([p * S.bit_count() + m * pairs(1, S) for S in range(1, 7)])
v = s.Matrix([q * S.bit_count() + h * (S & 6).bit_count() for S in range(1, 7)])
B = s.Matrix(6, 6, lambda i, j: p * pairs(i + 1, j + 1)
             + m * triple(1, i + 1, j + 1))
M = 3 * r * r.T / (4 * E) - B
w = 3 * x * r / (4 * E) - v
z = s.Matrix([(h * p - p * q - 2 * m * q) / p ** 2,
              -q / p, 0, -q / p, 0, 0])
for i in range(6):
    equal((M * z)[i], w[i], ('inverse-column', i))
S = s.cancel(3 * x ** 2 / (4 * E) - (w.T * z)[0])
equal(S, 2 * q * (h * p - m * q) / p ** 2, 'Schur normalization')
equal(M.det(), p ** 4 * (p + m) ** 2 / 4, 'R determinant')
zv, ze = s.symbols('z_v z_e')
f = q + h * zv + p * ze + m * zv * ze
equal(s.diff(f, zv) * s.diff(f, ze) - f * s.diff(f, zv, ze),
      h * p - m * q, 'Rayleigh difference')
out = {'status': 'pass', 'profile': [1, 1, 0], 'class_order': list(range(1, 7)),
       'E': str(E), 'x': str(x), 'r': [str(t) for t in r], 'v': [str(t) for t in v],
       'inverse_cross_column': [str(s.factor(t)) for t in z],
       'R_determinant': str(p ** 4 * (p + m) ** 2 / 4),
       'Schur': str(s.factor(S)), 'Rayleigh_difference': str(h * p - m * q)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
