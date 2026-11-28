#!/usr/bin/env python3
"""Check the affine spanning bound on a rational cyclic representation."""
from fractions import Fraction as Q
from itertools import product


def squared_norm(vec):
    return sum(x * x for x in vec)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def shift(col, step):
    """Simultaneous cyclic shift on two blocks of dimension d."""
    return tuple(col[k * d + (i - step) % d] for k in range(2) for i in range(d))


def column_rank(columns):
    basis = {}
    for col in columns:
        row = list(col)
        for i in sorted(basis):
            if row[i]:
                coeff = row[i]
                row = [x - coeff * y for x, y in zip(row, basis[i])]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is not None:
            scale = row[pivot]
            basis[pivot] = [x / scale for x in row]
    return len(basis)


# The target is the first block, the source has four columns, and the
# restricted source omits the final column. The columns have disjoint
# support before translation. The projection shrinks the first norm.
d, h = 8, 4
cols = []
for i in range(h):
    col = [Q(0)] * (2 * d)
    scale = Q(35, 36) if i == 0 else Q(1)
    col[2 * i] = scale * Q(399, 401)
    col[2 * i + 1] = scale * Q(40, 401)
    col[d + 2 * i] = Q(1, 11)
    cols.append(tuple(col))

a = sum(1 - squared_norm(col[:d]) for col in cols) / h
r = Q(1, h)
orbit = [[shift(col, s) for col in cols] for s in range(d)]
overlap = sum(dot(x, y) ** 2 for shifted in orbit for x in cols for y in shifted) / d
v = max(Q(0), d * overlap / h**2 - 1)
eta = 2 * (a + r) + v
assert 0 < eta < 1

avg = [[sum(col[i] * col[j] for shifted in orbit for col in shifted) / d
        for j in range(2 * d)] for i in range(2 * d)]
assert sum(squared_norm(row) for row in avg) == overlap

ranks = []
for mask in range(1 << d):
    retained = [col[:d] for s, shifted in enumerate(orbit) if mask & (1 << s)
                for col in shifted[:-1]]
    ranks.append(column_rank(retained))

for mask, rank in enumerate(ranks):
    k = d - rank
    average_gain = Q(sum(ranks[mask | (1 << s)] - rank for s in range(d)), d)
    assert average_gain >= Q(h, 2 * d) * (k - d * eta)

for count in range(5):
    total = sum(d - ranks[sum(1 << s for s in set(selected))]
                for selected in product(range(d), repeat=count))
    expected_defect = Q(total, d**count)
    upper = d * (eta + (1 - eta) * (1 - Q(h, 2 * d)) ** count)
    assert expected_defect <= upper
    print(f"{count} draws: exact expected missing dimension = {expected_defect}")

print("Trace identity, 256 span inequalities and five finite sampling checks passed.")
print(f"a = {a}, r = {r}, v = {v}, eta = {eta}")

# Check the centered trace calculation and the stronger rank-gain bound
# used in Theorem 4. Clear the square root only when the left side is positive.
cov = [[Q(d, h) * avg[i][j] for j in range(d)] for i in range(d)]
centered_norm = sum((cov[i][j] - int(i == j))**2 for i in range(d) for j in range(d))
assert centered_norm <= (2*a + v) * d
for mask, rank in enumerate(ranks):
    u = Q(d - rank, d)
    gain = Q(sum(ranks[mask | (1 << s)] - rank for s in range(d)), d)
    residual = u - a - r - v / 2 - gain / h
    assert residual <= 0 or residual**2 <= (2*a + v) * u
b = Q(8)
budget = (19 / (2*b**2) + b**-6 + 19 / (4*b)) / (1 - 1/b)
assert budget == Q(194561, 229376) < 1
print('Centered trace bound, all centered rank-gain bounds, and the b=8 endpoint passed.')
