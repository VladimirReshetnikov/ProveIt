"""Exact lower certificate for the unit regular dodecahedron (Python 3)."""

from collections import Counter
from itertools import product

# z = exp(2 pi i / 5); basis 1,z,z^2,z^3.
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
Z = (0, 1, 0, 0)


def add(p, q):
    return tuple(a + b for a, b in zip(p, q))


def sub(p, q):
    return tuple(a - b for a, b in zip(p, q))


def mul(p, q):
    coeffs = [0] * 7
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            coeffs[i + j] += a * b
    for k in range(6, 3, -1):
        for j in range(k - 4, k):
            coeffs[j] -= coeffs[k]
    return tuple(coeffs[:4])


def conjugate(p):
    # z^4 = -1-z-z^2-z^3, z^(-2)=z^3, z^(-3)=z^2.
    a, b, c, d = p
    return (a - b, -b, d - b, c - b)


def norm2(p):
    # A real ring element (u,0,v,v) is u - v*phi.
    u, w, v, t = mul(p, conjugate(p))
    assert w == 0 and v == t
    return (u, -v)


def nonnegative_phi(a, b):
    """Decide a+b*phi >= 0 using only integer signs and squares."""
    x = 2 * a + b
    if b == 0:
        return x >= 0
    if b > 0:
        return x >= 0 or 5 * b * b >= x * x
    return x >= 0 and x * x >= 5 * b * b


# All cycles have the outward boundary orientation. Face 0 starts at V=0.
FACES = (
    (0, 16, 1, 14, 12), (0, 12, 2, 10, 8), (0, 8, 4, 18, 16),
    (9, 11, 3, 14, 1), (16, 18, 5, 9, 1), (2, 12, 14, 3, 17),
    (17, 19, 6, 10, 2), (3, 11, 7, 19, 17), (4, 13, 15, 5, 18),
    (8, 10, 6, 13, 4), (5, 15, 7, 11, 9), (6, 19, 7, 15, 13)
)
SOURCE, TARGET = 0, 7
VERTEX_PAIRS = tuple((i, j) for i, j in product(range(12), repeat=2)
                     if i < j and len(set(FACES[i]) & set(FACES[j])) == 2)
ADJ = [[j for j in range(12) if (min(i, j), max(i, j)) in VERTEX_PAIRS]
       for i in range(12)]

# Physical labels 0..7 are the lexicographic sign triples (-1,-1,-1), ...,
# (1,1,1). For 8..19, take cyclic right shifts of (0,i/phi,j*phi)
# in order of shift 0,1,2 and signs (i,j)=(-,-),(-,+),(+,-),(+,+).
# Multiply every coordinate by phi/2 for unit edges. The planar model below
# already has unit edges.
basis_pentagon = []
vertex, direction = ZERO, ONE
for _ in range(5):
    basis_pentagon.append(vertex)
    vertex = add(vertex, direction)
    direction = mul(direction, Z)
assert vertex == ZERO


def adjacent_face(i, j, chart):
    a, b = sorted(set(FACES[i]) & set(FACES[j]))
    initial = dict(zip(FACES[j], basis_pentagon))
    unit_edge = sub(initial[b], initial[a])
    assert norm2(unit_edge) == (1, 0)
    rotation = mul(sub(chart[b], chart[a]), conjugate(unit_edge))
    assert norm2(rotation) == (1, 0)
    return {k: add(chart[a], mul(rotation, sub(v, initial[a])))
            for k, v in initial.items()}


def enumerate_strips():
    first = dict(zip(FACES[0], basis_pentagon))
    stack = [((0,), first)]
    while stack:
        seq, chart = stack.pop()
        if TARGET in chart:
            yield seq, norm2(sub(chart[TARGET], first[SOURCE]))
            continue
        for j in ADJ[seq[-1]]:
            if j not in seq and SOURCE not in FACES[j]:
                stack.append((seq + (j,), adjacent_face(seq[-1], j, chart)))


if __name__ == '__main__':
    counts = Counter()
    for strip, (a, b) in enumerate_strips():
        assert nonnegative_phi(a - 5, b - 7), (strip, a, b)
        counts[a, b] += 1
    assert sum(counts.values()) == 50
    print("a b multiplicity  (squared unfolded displacement = a+b*phi)")
    for (a, b), n in sorted(counts.items()):
        print(a, b, n)
    print("All 50 strips have squared displacement at least 5+7*phi.")
