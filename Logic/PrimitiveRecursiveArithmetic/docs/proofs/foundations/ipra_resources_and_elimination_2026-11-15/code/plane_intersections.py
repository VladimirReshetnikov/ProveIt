"""Exact reference implementation of certified rational plane intersections.

This executable illustrates the construction in paper/report.pdf.
It is not an iPRA proof checker and its regression checks are not proofs.
All polynomial operations use fractions.Fraction. Determinants use the
finite permutation formula to make the arithmetic contract transparent.
"""
from fractions import Fraction as Q
from itertools import permutations
from math import comb, gcd, prod
import json


def trim(a):
    """Normalize a univariate coefficient tuple, low coefficient first."""
    a = tuple(map(Q, a))
    last = max((i + 1 for i, x in enumerate(a) if x), default=0)
    return a[:last]


def add(a, b):
    return trim((a[i] if i < len(a) else 0) +
                (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def mul(a, b):
    if not a or not b:
        return ()
    r = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return trim(r)


def scale(a, c):
    return trim(Q(c) * x for x in a)


def eval1(a, x):
    r = Q(0)
    for c in reversed(a):
        r = r * x + c
    return r


def clean2(f):
    return {(i, j): Q(c) for (i, j), c in f.items() if c}


def degree2(f):
    return max((i + j for (i, j), c in f.items() if c), default=-1)


def eval2(f, x, y):
    return sum((c * x**i * y**j for (i, j), c in f.items()), Q(0))


def shear(f, c):
    """F(U-c V,V), as a sparse exact coefficient table."""
    r = {}
    for (i, j), a in f.items():
        for k in range(i + 1):
            key = (i - k, j + k)
            r[key] = r.get(key, Q(0)) + a * comb(i, k) * (-c)**k
    return clean2(r)


def v_coefficients(f, d):
    """Coefficients in V, each a polynomial in U."""
    return [trim(f.get((i, j), Q(0)) for i in range(d + 1))
            for j in range(d + 1)]


def determinant(a):
    n = len(a)
    result = ()
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j]
                         for i in range(n) for j in range(i + 1, n))
        term = (Q(-1 if inversions % 2 else 1),)
        for i, j in enumerate(perm):
            term = mul(term, a[i][j])
        result = add(result, term)
    return result


def resultant(f, g, d, e):
    fc = v_coefficients(f, d)
    gc = v_coefficients(g, e)
    n = d + e
    matrix = []
    for shift in range(e):
        matrix.append([fc[k - shift] if 0 <= k - shift <= d else ()
                       for k in range(n)])
    for shift in range(d):
        matrix.append([gc[k - shift] if 0 <= k - shift <= e else ()
                       for k in range(n)])
    return determinant(matrix)


def integer_coefficients(p):
    denominator = prod(c.denominator for c in p)
    return tuple(int(c * denominator) for c in p)


def rational_roots(p):
    """Complete bounded scan; raises on the identically zero polynomial."""
    p = trim(p)
    if not p:
        raise ValueError("zero polynomial has no finite rational-root list")
    a = integer_coefficients(p)
    k = next(i for i, x in enumerate(a) if x)
    roots = {Q(0)} if k else set()
    if k == len(a) - 1:
        return sorted(roots)
    for numerator in range(-abs(a[k]), abs(a[k]) + 1):
        if numerator == 0 or a[k] % numerator:
            continue
        for denominator in range(1, abs(a[-1]) + 1):
            if a[-1] % denominator or gcd(abs(numerator), denominator) != 1:
                continue
            r = Q(numerator, denominator)
            if eval1(p, r) == 0:
                roots.add(r)
    return sorted(roots)


def specialize_u(f, u, d):
    return trim(sum((a * u**i for (i, k), a in f.items() if k == j), Q(0))
                for j in range(d + 1))


def intersect(f, g):
    f, g = clean2(f), clean2(g)
    d, e = degree2(f), degree2(g)
    if d == 0 or e == 0:
        return {"status": "success", "points": [], "reason": "nonzero constant"}
    if d < 0 or e < 0:
        return {"status": "unsupported", "reason": "zero polynomial"}
    chosen = None
    for c in range(d + e + 1):
        ff, gg = shear(f, c), shear(g, c)
        if ff.get((0, d), 0) and gg.get((0, e), 0):
            chosen = c, ff, gg
            break
    if chosen is None:
        raise AssertionError("bounded-shear theorem violated")
    c, ff, gg = chosen
    r = resultant(ff, gg, d, e)
    certificate = {"shear": c, "degrees": [d, e], "resultant": r}
    if not r:
        return {"status": "unsupported", "reason": "zero resultant", **certificate}
    points = set()
    for u in rational_roots(r):
        fibre = specialize_u(ff, u, d)
        assert len(fibre) == d + 1 and fibre[-1] != 0
        for v in rational_roots(fibre):
            if eval2(gg, u, v) == 0:
                p = u - c * v, v
                assert eval2(f, *p) == eval2(g, *p) == 0
                points.add(p)
    points = sorted(points)
    height = max((max(abs(z.numerator), z.denominator)
                  for p in points for z in p), default=0)
    assert len(r) - 1 <= d * e
    assert len(points) <= d * e
    return {"status": "success", "points": points, "height": height, **certificate}


def encode(x):
    if isinstance(x, Q):
        return str(x)
    if isinstance(x, dict):
        return {k: encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def self_check():
    examples = [
        ("four points, repeated elimination fibres",
         {(2, 0): 1, (0, 2): 1, (0, 0): -5},
         {(1, 1): 1, (0, 0): -2},
         [(-2, -1), (-1, -2), (1, 2), (2, 1)]),
        ("two initially nongeneric leading directions",
         {(1, 1): 1, (0, 0): -2},
         {(1, 0): 1, (0, 1): 1, (0, 0): -3},
         [(1, 2), (2, 1)]),
        ("zero elimination root and two-point fibre",
         {(2, 0): 1, (0, 2): 1, (0, 0): -1},
         {(1, 0): 1}, [(0, -1), (0, 1)]),
        ("rational denominators",
         {(1, 0): 2, (0, 0): -1},
         {(0, 1): 3, (0, 0): -1}, [(Q(1, 2), Q(1, 3))]),
        ("isolated origin with zero constant term",
         {(0, 2): 1, (1, 0): -1},
         {(1, 0): 1}, [(0, 0)]),
    ]
    results = []
    for name, f, g, expected in examples:
        actual = intersect(f, g)
        assert actual["status"] == "success"
        assert actual["points"] == sorted((Q(x), Q(y)) for x, y in expected)
        # Independent bounded-box scan: every point seen must be in the list.
        box = sorted({Q(a, b) for a in range(-6, 7) for b in range(1, 7)})
        seen = {(x, y) for x in box for y in box
                if eval2(clean2(f), x, y) == eval2(clean2(g), x, y) == 0}
        assert seen == set(actual["points"])
        results.append({"case": name, **actual})
    common = intersect({(0, 1): 1, (1, 0): -1},
                       {(0, 1): 2, (1, 0): -2})
    assert common["status"] == "unsupported" and common["reason"] == "zero resultant"
    results.append({"case": "positive-dimensional refusal", **common})
    assert intersect({(0, 0): 1}, {})["points"] == []
    assert intersect({}, {(1, 0): 1})["status"] == "unsupported"
    assert rational_roots((0, -6, 11, -6, 1)) == [Q(0), Q(1), Q(2), Q(3)]
    assert rational_roots((Q(1, 2),)) == []
    return {"status": "passed", "scope": "finite regression checks only", "examples": results}


if __name__ == "__main__":
    print(json.dumps(encode(self_check()), indent=2))
