"""Exact finite checks of the all-dimensional quartic/quintic cube formulas.

Standard-library only. Mathematical proofs are in the accompanying article; this script
checks combinatorial coefficients and several exact cyclic-group examples.
"""
from fractions import Fraction
from itertools import combinations, product


def rank(matrix, modulus=None):
    a = [list(map(Fraction, row)) if modulus is None else list(row)
         for row in matrix]
    r = 0
    for j in range(len(a[0])):
        piv = next((i for i in range(r, len(a))
                    if a[i][j] != 0), None)
        if piv is None:
            continue
        a[r], a[piv] = a[piv], a[r]
        inv = 1 / a[r][j] if modulus is None else pow(a[r][j], -1, modulus)
        a[r] = [v * inv if modulus is None else v * inv % modulus
                for v in a[r]]
        for i in range(r + 1, len(a)):
            factor = a[i][j]
            a[i] = [v - factor * w if modulus is None
                    else (v - factor * w) % modulus
                    for v, w in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def vertex_matrix(vertices):
    return [[1] * len(vertices)] + [list(row) for row in zip(*vertices)]


def coefficients(d):
    return ((6**d - 2 * 4**d + 2**d) // 8,
            (8**d - 3 * 6**d + 3 * 4**d - 2**d) // 24,
            (8**d - 3 * 6**d + 3 * 4**d - 2**d) // 6,
            (10**d - 4 * 8**d + 6 * 6**d - 4 * 4**d + 2**d) // 24)


def check_classification(d):
    vertices = list(product((0, 1), repeat=d))
    par = tet = circuit = det3 = 0
    for vs in combinations(vertices, 4):
        mat = vertex_matrix(vs)
        rq = rank(mat)
        par += rq == 3
        tet += rq == 4 and rank(mat, 2) == 3
    for vs in combinations(vertices, 5):
        mat = vertex_matrix(vs)
        rq = rank(mat)
        if rq == 4:
            circuit += all(rank(vertex_matrix(sub)) == 4
                           for sub in combinations(vs, 4))
        det3 += rq == 5 and rank(mat, 3) == 4
    actual = (par, tet, circuit, det3)
    assert actual == coefficients(d), (d, actual, coefficients(d))
    return actual


def moment(f, vertices):
    n = len(f)
    d = len(vertices[0])
    total = 0
    for variables in product(range(n), repeat=d + 1):
        x, *hs = variables
        val = 1
        for vertex in vertices:
            arg = (x + sum(a * h for a, h in zip(vertex, hs))) % n
            val *= f[arg]
        total += val
    return Fraction(total, n ** (d + 1))


def low_coefficients(f, d):
    n = len(f)
    vertices = list(product((0, 1), repeat=d))
    totals = [0] * 6
    for variables in product(range(n), repeat=d + 1):
        x, *hs = variables
        pol = [1, 0, 0, 0, 0, 0]
        for vertex in vertices:
            val = f[(x + sum(a * h for a, h in zip(vertex, hs))) % n]
            for k in range(5, 0, -1):
                pol[k] += val * pol[k-1]
        totals = [a + b for a, b in zip(totals, pol)]
    return [Fraction(v, n ** (d + 1)) for v in totals]


def check_moments(n, d):
    raw = [(i * i + 3 * i + 1) % 7 for i in range(n)]
    f = [n * a - sum(raw) for a in raw]
    assert sum(f) == 0
    q = moment(f, [(0, 0), (1, 0), (0, 1), (1, 1)])
    D = moment(f, [(0, 0, 0), (1, 0, 0), (0, 1, 0),
                   (0, 0, 1), (1, 1, 1)])
    T3 = moment(f, [(0, 0, 0, 0), (0, 1, 1, 1),
                    (1, 0, 1, 1), (1, 1, 0, 1), (1, 1, 1, 0)])
    P, _, F, H = coefficients(d)
    pol = low_coefficients(f, d)
    assert pol[0] == 1 and pol[1:4] == [0, 0, 0], (n, d, pol)
    assert pol[4] == P * q, (n, d, pol[4], P*q)
    assert pol[5] == F * D + H * T3, (n, d, pol[5], F*D+H*T3)
    if n % 3:
        assert T3 == 0
    return str(pol[4]), str(pol[5]), str(T3)


if __name__ == '__main__':
    for d in (2, 3, 4):
        print('classification', d, check_classification(d), flush=True)
    for n, d in ((3, 3), (3, 4), (5, 3), (5, 4), (7, 4), (9, 4)):
        print('moments', n, d, check_moments(n, d), flush=True)
