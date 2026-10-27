#!/usr/bin/env python3
"""Exact optimal convex weights and exact Euclidean-envelope menu certificate.

This proves an optimum within the fixed nine-plan support envelope, not a
lower bound on SAT or on the actual contractor's runtime.
"""

def require(condition, message):
    if not condition:
        raise RuntimeError(message)
import json
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations, product
from math import lcm, gcd, isqrt
import check_consistent_certificate as c
ROOT = Path(__file__).resolve().parent
WITNESS = (67, 67, 69, 69, 67, 69, 67, 69, 69)
menus = [c.supports(p) for p in c.PLANS]
chosen = [menus[i][a] for i, a in enumerate(WITNESS)]
gram = [[c.dot(u, v) for v in chosen] for u in chosen]

def linear_solve(A, b):
    rows = [[Q(x) for x in row] + [Q(y)] for row, y in zip(A, b)]
    n = len(rows)
    for col in range(n):
        pivot = next((i for i in range(col, n) if rows[i][col]))
        rows[col], rows[pivot] = (rows[pivot], rows[col])
        z = rows[col][col]
        rows[col] = [x / z for x in rows[col]]
        for i in range(n):
            if i != col:
                z = rows[i][col]
                rows[i] = [x - z * y for x, y in zip(rows[i], rows[col])]
    return [r[-1] for r in rows]
z = linear_solve(gram, [1] * 9)
require(all((sum((Q(gram[i][j]) * z[j] for j in range(9))) == 1 for i in range(9))), 'Exact check failed at original source line 35')
Z = sum(z)
require(Z > 0, 'Exact check failed at original source line 37')
p = [x / Z for x in z]
require(sum(p) == 1 and all((x > 0 for x in p)), 'Exact check failed at original source line 39')
den = lcm(*(x.denominator for x in p))
weights = [int(x * den) for x in p]
require(sum(weights) == den and gcd(*weights) == 1, 'Exact check failed at original source line 42')
vectors = [[tuple((w * x for x in v)) for v in menu] for w, menu in zip(weights, menus)]
norms = [[c.dot(v, v) for v in menu] for menu in vectors]

def tuple_norm(t):
    return sum((sum((vectors[i][a][e] for i, a in enumerate(t))) ** 2 for e in range(45)))
M = tuple_norm(WITNESS)
H = Q(1, Z * c.SCALE * c.SCALE)
require(Q(M, den * den * c.SCALE * c.SCALE) == H, 'Exact check failed at original source line 49')
direction = [sum((p[i] * Q(chosen[i][e], c.SCALE) for i in range(9))) for e in range(45)]
require(all((t >= 0 for t in direction)), 'Exact check failed at original source line 51')
require(sum((x * x for x in direction)) == H, 'Exact check failed at original source line 52')
require(all((sum((Q(chosen[i][e], c.SCALE) * direction[e] for e in range(45))) == H for i in range(9))), 'Exact check failed at original source line 53')
pair, maximum = ({}, {})
for i, j in combinations(range(9), 2):
    table = [[norms[i][a] + norms[j][b] + 16 * c.dot(v, u) for b, u in enumerate(vectors[j])] for a, v in enumerate(vectors[i])]
    pair[i, j] = table
    maximum[i, j] = max(map(max, table))
keep = []
excluded = []
for i in range(9):
    accepted = []
    for a in range(72):
        upper = sum((max(pair[j, k][a]) if i == j else max((row[a] for row in pair[j, k])) if i == k else maximum[j, k] for j, k in combinations(range(9), 2)))
        if upper >= 8 * M:
            accepted.append(a)
        else:
            excluded.append(upper)
    keep.append(accepted)
count = 1
for x in keep:
    count *= len(x)
require(count < 1000000, count)
actual = max(((tuple_norm(t), t) for t in product(*keep)))
require(actual[0] == M, (actual[0], M))
require(max(excluded) < 8 * M, 'Exact check failed at original source line 77')

def atan_interval(d, n):
    s = sum((Q((-1) ** j, (2 * j + 1) * d ** (2 * j + 1)) for j in range(n)), Q(0))
    t = s + Q((-1) ** n, (2 * n + 1) * d ** (2 * n + 1))
    return (min(s, t), max(s, t))
a, b = atan_interval(5, 35)
cc, dd = atan_interval(239, 12)
pi = (16 * a - 4 * dd, 16 * b - 4 * cc)
n = 70
lnlo = sum((Q(2, (2 * j + 1) * 3 ** (2 * j + 1)) for j in range(n)), Q(0))
ln = (lnlo, lnlo + Q(2, (2 * n + 1) * 3 ** (2 * n + 1)) * Q(9, 8))
beta2 = H / 50
rad = 2 * beta2 / Q(301, 20000)
unit = 10 ** 35
r = isqrt(rad.numerator * unit * unit // rad.denominator)
C = (pi[0] / ln[1] * Q(r, unit), pi[1] / ln[0] * Q(r + 1, unit))
require(Q(29746057, 1000000) < C[0] < C[1] < Q(29746058, 1000000), 'Exact check failed at original source line 93')
out = {'status': 'PASS', 'scope': 'exact Euclidean support-envelope optimum for the inherited nine plans', 'not_claimed': 'SAT lower bound, measured runtime improvement, or smaller logarithmic order', 'selected_tuple': list(WITNESS), 'gram': gram, 'z': [str(x) for x in z], 'normalized_weights': [str(x) for x in p], 'weight_denominator': den, 'integer_weights': weights, 'normalized_norm_squared': str(H), 'beta_squared': str(beta2), 'direction': [str(x) for x in direction], 'global_support_maximum_norm': M, 'survivors': keep, 'surviving_tuples': count, 'max_excluded_pair_bound': max(excluded), 'exclusion_threshold': 8 * M, 'coefficient_interval': [str(x) for x in C], 'coefficient_display': float(C[0]), 'exact_weight_display': [float(x) for x in p]}
(ROOT / 'fixed_menu_optimal_certificate.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: out[k] for k in ['status', 'scope', 'survivors', 'surviving_tuples', 'coefficient_display', 'exact_weight_display']}, indent=2))
