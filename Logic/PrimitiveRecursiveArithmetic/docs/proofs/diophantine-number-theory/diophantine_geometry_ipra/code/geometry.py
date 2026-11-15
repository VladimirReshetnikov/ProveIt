#!/usr/bin/env python3
"""Exact executable companions to Diophantine geometry in iPRA.

No floating point, symbolic algebra dependency, or unbounded witness search.
The paper proves correctness; these programs are executable illustrations.
Inputs failing a stated mathematical precondition raise ValueError.
Such branches can be totalized by returning the empty list / zero in iPRA.
"""
from fractions import Fraction
from itertools import permutations, product
from math import factorial, gcd, isqrt


def gcd_all(values):
    g = 0
    for x in values:
        g = gcd(g, abs(x))
    return g


def canonical(v):
    """Primitive integer projective representative; first nonzero entry > 0."""
    v = tuple(v)
    g = gcd_all(v)
    if g == 0:
        raise ValueError("the zero vector is not a projective point")
    w = tuple(x // g for x in v)
    if next(x for x in w if x) < 0:
        w = tuple(-x for x in w)
    return w


def height(v):
    return max(map(abs, canonical(v)))


def projective_points(n, bound):
    """Exactly P^n(Q) of multiplicative height <= bound, without duplicates."""
    if n < 0 or bound < 0:
        raise ValueError("nonnegative dimension and bound required")
    points = []
    for v in product(range(-bound, bound + 1), repeat=n + 1):
        if gcd_all(v) == 1 and next(x for x in v if x) > 0:
            points.append(v)
    return points


def eval_polynomial(terms, v):
    """terms is a list of (integer coefficient, exponent tuple)."""
    total = 0
    for c, exponents in terms:
        if len(exponents) != len(v) or any(e < 0 for e in exponents):
            raise ValueError("one nonnegative exponent per coordinate required")
        term = c
        for x, e in zip(v, exponents):
            term *= x ** e
        total += term
    return total


def bounded_locus(n, bound, polynomials):
    return [v for v in projective_points(n, bound)
            if all(eval_polynomial(f, v) == 0 for f in polynomials)]


def residue_solutions(n, modulus, polynomials):
    """Unimodular residue vectors, not quotient classes, satisfying all equations."""
    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    return [v for v in product(range(modulus), repeat=n + 1)
            if gcd_all((modulus,) + v) == 1
            and all(eval_polynomial(f, v) % modulus == 0 for f in polynomials)]


def determinant(matrix):
    """Leibniz definition with exactly n! summands; adequate for small examples."""
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("square matrix required")
    total = 0
    for p in permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        term = -1 if inversions % 2 else 1
        for i in range(n):
            term *= matrix[i][p[i]]
        total += term
    return total


def adjugate(matrix):
    n = len(matrix)
    return [[(-1) ** (i + j) * determinant([
        [matrix[r][c] for c in range(n) if c != i]
        for r in range(n) if r != j])
        for j in range(n)] for i in range(n)]


def form_eval(coefficients, x, y):
    d = len(coefficients) - 1
    return sum(c * x ** (d - i) * y ** i for i, c in enumerate(coefficients))


def convolution(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def sylvester(f, g):
    """Columns of (A,B) -> AF+BG on binary forms of degree d-1."""
    if len(f) != len(g) or len(f) < 2:
        raise ValueError("two forms of the same positive degree required")
    d = len(f) - 1
    matrix = [[0] * (2 * d) for _ in range(2 * d)]
    for k in range(d):
        for i in range(d + 1):
            matrix[k + i][k] = f[i]
            matrix[k + i][d + k] = g[i]
    return matrix


def map_certificate(f, g):
    """Return two adjugate identities and explicit height constants."""
    matrix = sylvester(f, g)
    r = determinant(matrix)
    if r == 0:
        raise ValueError("nonzero homogeneous resultant is required")
    d = len(f) - 1
    adj = adjugate(matrix)
    columns = []
    for j in (0, 2 * d - 1):
        col = [adj[i][j] for i in range(2 * d)]
        a, b = col[:d], col[d:]
        af, bg = convolution(a, f), convolution(b, g)
        target = [0] * (2 * d)
        target[j] = r
        assert [u + v for u, v in zip(af, bg)] == target
        columns.append((a, b))
    m = max(1, *(abs(c) for c in tuple(f) + tuple(g)))
    lower = max(sum(map(abs, a)) + sum(map(abs, b)) for a, b in columns)
    return {"degree": d, "resultant": r, "certificates": columns,
            "lower_constant": lower, "upper_constant": (d + 1) * m,
            "coarse_lower_constant": 2 * d * factorial(2 * d - 1) * m ** (2 * d - 1)}


def rational_map(f, g, p):
    x, y = canonical(p)
    return canonical((form_eval(f, x, y), form_eval(g, x, y)))


def preperiodic_points(f, g):
    """Complete finite list with repetition witnesses, for degree >= 2.

    The potentially enormous bound is intentional. No practical efficiency
    assertion is made. Each orbit stops at escape or a repeat within |S|+1
    states, where S is the explicitly computed height box.
    """
    cert = map_certificate(f, g)
    if cert["degree"] < 2:
        raise ValueError("degree at least 2 required")
    bound = cert["lower_constant"]
    candidates = projective_points(1, bound)
    result = []
    for p in candidates:
        current, seen, orbit = p, {}, []
        for j in range(len(candidates) + 1):
            if height(current) > bound:
                break
            if current in seen:
                result.append({"point": p, "i": seen[current], "j": j,
                               "orbit": orbit})
                break
            seen[current] = j
            orbit.append(current)
            current = rational_map(f, g, current)
        else:
            raise AssertionError("finite pigeonhole invariant failed")
    return cert, result


def circle_parameter(s, t):
    if s == 0 and t == 0:
        raise ValueError("nonzero parameter required")
    return canonical((s * s - t * t, 2 * s * t, s * s + t * t))


def circle_inverse(p):
    x, y, z = canonical(p)
    if x * x + y * y != z * z:
        raise ValueError("point not on the circle")
    return canonical((z + x, y)) if z + x else (0, 1)


def elliptic_points_xheight(a, b, bound):
    """All affine rational points on y^2=x^3+a*x+b with H(x)<=bound.

    Add the separate point at infinity to obtain the projective point list.
    Nonsingularity is not needed for this enumeration lemma.
    """
    if bound < 0:
        raise ValueError("nonnegative height bound required")
    result = set()
    for d in range(1, isqrt(bound) + 1):
        for numerator in range(-bound, bound + 1):
            if gcd(numerator, d) != 1:
                continue
            rhs = numerator ** 3 + a * numerator * d ** 4 + b * d ** 6
            if rhs >= 0:
                root = isqrt(rhs)
                if root * root == rhs:
                    for sign in (-1, 1):
                        result.add((Fraction(numerator, d * d),
                                    Fraction(sign * root, d ** 3)))
    return sorted(result)


def rational_roots(coefficients):
    """All rational roots of a nonzero polynomial; coefficients in ascending order."""
    a = list(coefficients)
    while a and a[-1] == 0:
        a.pop()
    if not a:
        raise ValueError("zero polynomial has no finite root list")
    if len(a) == 1:
        return []
    first = next(i for i, c in enumerate(a) if c)
    roots = {Fraction(0)} if first else set()
    low, high = abs(a[first]), abs(a[-1])
    for p in range(-low, low + 1):
        if p == 0 or low % p:
            continue
        for q in range(1, high + 1):
            if high % q or gcd(p, q) != 1:
                continue
            value = Fraction(p, q)
            if sum(c * value ** i for i, c in enumerate(a)) == 0:
                roots.add(value)
    return sorted(roots)


if __name__ == "__main__":
    import json
    data = {}
    for name, f, g in [("t_squared", [1, 0, 0], [0, 0, 1]),
                       ("t_squared_minus_one", [1, 0, -1], [0, 0, 1])]:
        cert, points = preperiodic_points(f, g)
        data[name] = {"certificate": cert, "preperiodic_points": points}
    obstruction = [(1, (2, 0, 0)), (1, (0, 2, 0)), (-3, (0, 0, 2))]
    data["x2_y2_3z2"] = {"mod3_residue_count": len(residue_solutions(2, 3, [obstruction])),
                           "mod9_residue_count": len(residue_solutions(2, 9, [obstruction]))}
    data["E1_affine_xheight_100"] = [[str(x), str(y)] for x, y in elliptic_points_xheight(-1, 0, 100)]
    data["E6_affine_xheight_36"] = [[str(x), str(y)] for x, y in elliptic_points_xheight(-36, 0, 36)]
    data["rational_roots_example"] = [str(x) for x in rational_roots([0, 6, -5, 1])]
    print(json.dumps(data, indent=2))
