"""Exact finite checks accompanying the mathematical article.

These computations check concrete rational examples and the algebra in finite
matrix certificates. They do not formalize infinite products, ordinal recursion,
elementarity, Polishness, or the Choice-dependent non-Borel functional.
Run with Python 3.10+; standard library only.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random

counts = {}


def check(category, condition):
    if not condition:
        raise AssertionError(category)
    counts[category] = counts.get(category, 0) + 1


def sign(v):
    return next((1 if x > 0 else -1 for x in v if x), 0)


def matvec(a, x):
    return [sum((c * t for c, t in zip(row, x)), F(0)) for row in a]


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def triangular_inverse(a):
    n = len(a)
    b = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            b[i][j] = (F(i == j) - sum(a[i][k] * b[k][j]
                                      for k in range(i))) / a[i][i]
    return b


# The five-coordinate conjugacy displayed in the article.
u = identity(5)
u[1][0] = F(2)
u[3][0] = F(1)
u[3][2] = F(-1)
u_inv = triangular_inverse(u)
check('five_coordinate_matrix_inverse', matmul(u, u_inv) == identity(5))
check('five_coordinate_matrix_inverse', matmul(u_inv, u) == identity(5))
for tup in product([-1, 0, 1], repeat=5):
    x = list(map(F, tup))
    y = matvec(u, x)
    check('five_coordinate_round_trip', matvec(u_inv, y) == x)
    check('five_coordinate_order', sign(y) == sign(x))
    if x[1] == x[3] == 0:
        check('subspace_equations', y[1] == 2*y[0] and y[3] == y[0]-y[2])

# Rectangular positive-pivot embedding, with nontrivial lower entries.
rng = random.Random(231113699)
n, m = 8, 19
pivots = [0, 2, 3, 6, 9, 10, 14, 17]
a = [[F(0) for _ in range(n)] for _ in range(m)]
for i, p in enumerate(pivots):
    a[p][i] = F(i+1, i+2)
    for j in range(p+1, m):
        a[j][i] = F(rng.randrange(-3, 4), rng.randrange(1, 5))
pivot_matrix = [a[p] for p in pivots]
inverse_pivot = triangular_inverse(pivot_matrix)
left = [[F(0) for _ in range(m)] for _ in range(n)]
for i in range(n):
    for k, p in enumerate(pivots):
        left[i][p] = inverse_pivot[i][k]
projection = matmul(a, left)
check('rectangular_left_inverse', matmul(left, a) == identity(n))
check('projection_idempotence', matmul(projection, projection) == projection)
for _ in range(400):
    x = [F(rng.randrange(-7, 8), rng.randrange(1, 6)) for _ in range(n)]
    y = matvec(a, x)
    check('rectangular_round_trip', matvec(left, y) == x)
    check('rectangular_order', sign(y) == sign(x))
    v = [F(rng.randrange(-7, 8), rng.randrange(1, 6)) for _ in range(m)]
    pv = matvec(projection, v)
    check('projection_image', matvec(projection, pv) == pv)
    check('projection_pivots', all(pv[p] == v[p] for p in pivots))


def positive(h, integer):
    return sign(h) > 0 or (sign(h) == 0 and integer >= 0)


# Standard division works even with a negative integer coordinate provided the
# leading coefficient is positive. This is the subtle positive-cone boundary.
for h in product([F(-1), F(0), F(1)], repeat=3):
    for z in range(-12, 13):
        if not positive(h, z):
            continue
        for modulus in range(1, 10):
            qz, residue = divmod(z, modulus)
            qh = tuple(c/modulus for c in h)
            check('standard_division_identity',
                  all(modulus*c == d for c, d in zip(qh, h))
                  and modulus*qz + residue == z)
            check('standard_division_positive_quotient', positive(qh, qz))
            check('standard_division_residue', 0 <= residue < modulus)

result = {
    'all_checks_passed': True,
    'total_checks': sum(counts.values()),
    'checks_by_category': counts,
    'rational_arithmetic': 'fractions.Fraction; no floating point',
    'random_seed': 231113699,
    'scope': 'Finite algebraic examples only; not a formal proof of the article.',
    'five_coordinate_matrix': [[str(c) for c in row] for row in u],
    'rectangular_pivot_positions': pivots,
    'rectangular_left_inverse_verified': True,
    'excluded_claims': [
        'infinite and transfinite theorem verification',
        'existence or computation of the wild functional',
        'formal verification of Presburger elementarity',
        'topological or Borel conclusions by computation',
    ],
}
out = Path(__file__).with_name('verification_results.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'all_checks_passed': True, 'total_checks': result['total_checks'],
                  'output': out.name}, indent=2))
