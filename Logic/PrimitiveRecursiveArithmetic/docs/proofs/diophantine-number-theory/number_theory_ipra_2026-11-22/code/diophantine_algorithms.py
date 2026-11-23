#!/usr/bin/env python3
"""Exact-arithmetic companion to the Diophantine chapter.

These finite computations check examples and implementation invariants. They
are not machine-checked iPRA proofs. Python integers are unbounded; every
mathematical search below has the finite fuel specified in the report.
"""
from fractions import Fraction
from math import gcd, isqrt


def continuants(coefficients):
    """Return [(p_i,q_i)] for a finite simple continued-fraction list."""
    if not coefficients or coefficients[0] < 0:
        raise ValueError("need a nonempty list with nonnegative first entry")
    if any(a < 1 for a in coefficients[1:]):
        raise ValueError("later coefficients must be positive")
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    out = []
    for a in coefficients:
        p, q = a * pm1 + pm2, a * qm1 + qm2
        out.append((p, q))
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
    return out


def rational_cf(a, b):
    if a < 0 or b <= 0:
        raise ValueError("need a >= 0 and b > 0")
    out = []
    for _ in range(b + 1):
        c, r = divmod(a, b)
        out.append(c)
        if r == 0:
            return out
        a, b = b, r
    raise AssertionError("Euclidean fuel invariant failed")


def dirichlet_grid(alpha, Q):
    """The literal Q+1-points/Q-boxes construction, valid for signed rationals."""
    if Q < 1:
        raise ValueError("Q must be positive")
    a, b = alpha.numerator, alpha.denominator
    seen = {}
    for j in range(Q + 1):
        integer_part, remainder = divmod(j * a, b)
        box = (Q * remainder) // b
        if box in seen:
            i, old_part = seen[box]
            return integer_part - old_part, j - i
        seen[box] = j, integer_part
    raise AssertionError("finite pigeonhole invariant failed")


def simultaneous_grid(alphas, N):
    if N < 1 or not alphas:
        raise ValueError("need positive N and a nonempty rational list")
    bound = N ** len(alphas)
    seen = {}
    for j in range(bound + 1):
        parts, boxes = [], []
        for alpha in alphas:
            k, r = divmod(j * alpha.numerator, alpha.denominator)
            parts.append(k)
            boxes.append((N * r) // alpha.denominator)
        key = tuple(boxes)
        if key in seen:
            i, old_parts = seen[key]
            return [a - b for a, b in zip(parts, old_parts)], j - i
        seen[key] = j, parts
    raise AssertionError("finite grid pigeonhole invariant failed")


def dirichlet_cf(a, b, Q):
    """Efficient rational Dirichlet witness, from the continuant error identity.

    Use the last convergent whose denominator is <= Q. The next denominator
    exceeds Q, so |q*(a/b)-p| < 1/Q. If the exact rational is reached first,
    its error is zero. This replaces the large grid scan for experiments.
    """
    if a < 0 or b <= 0 or Q < 1:
        raise ValueError("need nonnegative numerator and positive b,Q")
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    numerator, denominator = a, b
    for _ in range(b + 1):
        c, r = divmod(numerator, denominator)
        p, q = c * pm1 + pm2, c * qm1 + qm2
        if q > Q:
            assert qm1 > 0
            return pm1, qm1
        if r == 0:
            return p, q
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
        numerator, denominator = denominator, r
    raise AssertionError("continued-fraction fuel invariant failed")


def bounded_norm_pair(D, Y, use_grid=False):
    if D < 2 or isqrt(D) ** 2 == D or Y < 0:
        raise ValueError("need nonsquare D >= 2 and Y >= 0")
    Q = 4 * (D + 1) * (Y + 1)
    A = isqrt(D * Q ** 4)
    if use_grid:
        p, q = dirichlet_grid(Fraction(A, Q ** 2), Q)
    else:
        p, q = dirichlet_cf(A, Q ** 2, Q)
    m = p * p - D * q * q
    assert 0 < p <= D * Q + 1
    assert Y < q <= Q
    assert 0 < abs(m) < 4 * D + 2
    return p, q, m, Q


def pell_bound(D):
    """The explicit mathematical bound; extremely large even for moderate D."""
    C, B = 4 * D + 2, 4 * (D + 1)
    K = 2 * C ** 3
    U = (B + 1) ** (K + 1)
    return 4 * (D + 1) ** 2 * (U + 1) ** 2


def pell_norm_collision(D):
    """Find a Pell solution via the chapter's norm/residue collision.

    The for-loop fuel is K+1, not an unbounded 'until a solution' search.
    The much faster continued-fraction implementation supplies each rational
    Dirichlet witness; the report's grid implementation is interchangeable.
    """
    if D < 2 or isqrt(D) ** 2 == D:
        raise ValueError("need nonsquare D >= 2")
    C = 4 * D + 2
    K = 2 * C ** 3
    seen = {}
    T = 0
    for j in range(K + 1):
        p, q, m, Q = bounded_norm_pair(D, T)
        key = (m, p % abs(m), q % abs(m))
        if key in seen:
            i, old_p, old_q = seen[key]
            nx = old_p * p - D * old_q * q
            ny = old_p * q - p * old_q
            assert nx % m == 0 and ny % m == 0
            x, y = nx // m, ny // m
            assert x >= 2 and y >= 1
            assert x * x - D * y * y == 1
            return {
                "D": D, "x": x, "y": y, "common_norm": m,
                "earlier_index": i, "later_index": j,
                "earlier_pair": [old_p, old_q], "later_pair": [p, q],
            }
        seen[key] = j, p, q
        T = Q
    raise AssertionError("norm-class pigeonhole invariant failed")


def pell_multiply(D, a, b):
    x, y = a
    u, v = b
    return x * u + D * y * v, x * v + y * u


def pell_power(D, base, exponent):
    out = (1, 0)
    for _ in range(exponent):
        out = pell_multiply(D, out, base)
    return out


def pell_exponent(D, fundamental, pair):
    """Recover the exponent with fuel equal to the input second coordinate.

    Preconditions: fundamental really is the least positive solution and pair
    is a nonnegative solution with positive first coordinate.
    """
    u, v = fundamental
    x, y = pair
    if u <= 1 or v < 1 or u * u - D * v * v != 1:
        raise ValueError("invalid positive base solution")
    if x < 1 or y < 0 or x * x - D * y * y != 1:
        raise ValueError("invalid target solution")
    initial_y = y
    for n in range(initial_y + 1):
        if y == 0:
            assert x == 1
            return n
        nx, ny = u * x - D * v * y, u * y - v * x
        if not (nx > 0 and 0 <= ny < y):
            raise ValueError("base was not fundamental for this target")
        assert nx * nx - D * ny * ny == 1
        x, y = nx, ny
    raise AssertionError("Pell descent fuel invariant failed")


def pythagorean_parameters(a, b, c):
    if min(a, b, c) < 1 or a * a + b * b != c * c:
        raise ValueError("need a positive right triangle")
    scale = gcd(a, b)
    assert c % scale == 0
    a, b, c = a // scale, b // scale, c // scale
    exchanged = a % 2 == 0
    if exchanged:
        a, b = b, a
    m, n = isqrt((c + a) // 2), isqrt((c - a) // 2)
    assert a == m * m - n * n and b == 2 * m * n
    assert c == m * m + n * n
    assert m > n > 0 and gcd(m, n) == 1 and (m - n) % 2 == 1
    return scale, exchanged, m, n
