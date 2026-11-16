"""Exact rational finite spectral certificates.

This is an executable reference for the human proof, not an iPRA proof
checker or a completed Lean formalization.  The core has an explicit
primitive-recursive fuel bound.  Exact fractions can become large.

Public API: jacobi(A, epsilon) -> dictionary with Q, d, transformed,
residual_sq, epsilon, fuel and steps.  Matrix helpers use nested lists of
fractions; an empty list denotes the unique 0 by 0 matrix.
"""

from fractions import Fraction as F


def matrix(rows):
    """Convert a square array of integers/Fractions to exact rationals."""
    result = [[F(x) for x in row] for row in rows]
    n = len(result)
    if any(len(row) != n for row in result):
        raise ValueError("Expected a square matrix")
    return result


def identity(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    n = len(a)
    return [[a[j][i] for j in range(n)] for i in range(n)]


def matmul(a, b):
    n = len(a)
    if len(b) != n:
        raise ValueError("Matrix dimensions differ")
    return [[sum((a[i][k] * b[k][j] for k in range(n)), F(0))
             for j in range(n)] for i in range(n)]


def matadd(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def matsub(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    c = F(c)
    return [[c * x for x in row] for row in a]


def diagonal(d):
    n = len(d)
    return [[F(d[i]) if i == j else F(0)
             for j in range(n)] for i in range(n)]


def frob_sq(a):
    return sum((x * x for row in a for x in row), F(0))


def offdiag_sq(a):
    return sum((a[i][j] ** 2 for i in range(len(a))
                for j in range(len(a)) if i != j), F(0))


def conjugate(a, q):
    """Return q^T a q."""
    return matmul(matmul(transpose(q), a), q)


def ceil_fraction(x):
    x = F(x)
    return -(-x.numerator // x.denominator)


def pivot_rotation(h, b):
    """Return rational (c,s,branch) making |b'|^2 <= |b|^2/2.

    The transformed pivot is b'=(c*c-s*s)*b-c*s*h.  The caller
    provides b!=0.  The two algebraic branches are proved in the report.
    """
    h, b = F(h), F(b)
    if b == 0:
        return F(1), F(0), "zero"
    if h * h >= b * b:
        t = b / (4 * h)
        u = t * t
        return (1 - u) / (1 + u), 2 * t / (1 + u), "large_difference"
    c, s = F(3, 5), F(4, 5)
    plus = (c * c - s * s) * b - c * s * h
    minus = (c * c - s * s) * b + c * s * h
    if minus * minus < plus * plus:
        s = -s
    return c, s, "small_difference"


def givens(n, i, j, c, s):
    if not 0 <= i < j < n:
        raise ValueError("Invalid pivot coordinates")
    g = identity(n)
    g[i][i], g[i][j] = c, -s
    g[j][i], g[j][j] = s, c
    return g


def jacobi(a, epsilon):
    """Compute a sorted rational approximate diagonalization.

    The mathematical definition runs exactly `fuel` stages and freezes
    the state when it meets the residual bound.  Returning that frozen
    state immediately is an equivalent execution optimization.
    """
    a = matrix(a)
    epsilon = F(epsilon)
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    if a != transpose(a):
        raise ValueError("Input must be symmetric")
    n = len(a)
    q, current = identity(n), a
    initial = frob_sq(a)
    fuel = n * (n - 1) * (ceil_fraction(initial / epsilon ** 2) + 1)
    steps = 0
    branch_counts = {"large_difference": 0, "small_difference": 0}
    if n >= 2:
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for _ in range(fuel):
            if offdiag_sq(current) <= epsilon ** 2:
                break
            i, j = max(pairs, key=lambda ij: current[ij[0]][ij[1]] ** 2)
            b = current[i][j]
            h = current[i][i] - current[j][j]
            c, s, branch = pivot_rotation(h, b)
            g = givens(n, i, j, c, s)
            current = conjugate(current, g)
            q = matmul(q, g)
            steps += 1
            branch_counts[branch] += 1
    order = sorted(range(n), key=lambda i: (current[i][i], i))
    current = [[current[i][j] for j in order] for i in order]
    q = [[row[j] for j in order] for row in q]
    result = {
        "Q": q,
        "d": [current[i][i] for i in range(n)],
        "transformed": current,
        "residual_sq": offdiag_sq(current),
        "epsilon": epsilon,
        "fuel": fuel,
        "steps": steps,
        "initial_frob_sq": initial,
        "branch_counts": branch_counts,
    }
    if result["residual_sq"] > epsilon ** 2:
        raise AssertionError("Explicit fuel exhausted before the proven bound")
    return result


def pivot_rotation_grid(h, b, grid):
    """Round the large-difference half-angle parameter toward zero.

    The decrease proof needs the grid chosen by jacobi_grid and an active
    maximum pivot.  This function alone does not promise uniform decrease
    for an arbitrary grid and pivot.
    """
    h, b = F(h), F(b)
    if b == 0 or h * h < b * b:
        return pivot_rotation(h, b)
    ideal = b / (4 * h)
    scaled = grid * abs(ideal)
    j = scaled.numerator // scaled.denominator
    t = F(j if ideal >= 0 else -j, grid)
    u = t * t
    return (1 - u) / (1 + u), 2 * t / (1 + u), "large_difference"


def jacobi_grid(a, epsilon):
    """Finite-grid variant with bounded rotation denominators.

    This has the same certificate as jacobi and the additional fields
    grid, magnitude_bound, rotation_denominator_bound.  It doubles the
    simple additive fuel bound, retaining a decrease of at least b^2/2.
    """
    a = matrix(a)
    epsilon = F(epsilon)
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    if a != transpose(a):
        raise ValueError("Input must be symmetric")
    n = len(a)
    q, current = identity(n), a
    initial = frob_sq(a)
    magnitude_bound = 1 + ceil_fraction(initial)
    grid = max(1, ceil_fraction(128 * magnitude_bound * n / epsilon))
    fuel = 2 * n * (n - 1) * (ceil_fraction(initial / epsilon ** 2) + 1)
    steps = 0
    branch_counts = {"large_difference": 0, "small_difference": 0}
    if n >= 2:
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for _ in range(fuel):
            if offdiag_sq(current) <= epsilon ** 2:
                break
            i, j = max(pairs, key=lambda ij: current[ij[0]][ij[1]] ** 2)
            b = current[i][j]
            h = current[i][i] - current[j][j]
            c, s, branch = pivot_rotation_grid(h, b, grid)
            g = givens(n, i, j, c, s)
            current = conjugate(current, g)
            q = matmul(q, g)
            steps += 1
            branch_counts[branch] += 1
    order = sorted(range(n), key=lambda i: (current[i][i], i))
    current = [[current[i][j] for j in order] for i in order]
    q = [[row[j] for j in order] for row in q]
    result = {
        "Q": q,
        "d": [current[i][i] for i in range(n)],
        "transformed": current,
        "residual_sq": offdiag_sq(current),
        "epsilon": epsilon,
        "fuel": fuel,
        "steps": steps,
        "initial_frob_sq": initial,
        "branch_counts": branch_counts,
        "grid": grid,
        "magnitude_bound": magnitude_bound,
        "rotation_denominator_bound": max(5, 2 * grid ** 2),
    }
    if result["residual_sq"] > epsilon ** 2:
        raise AssertionError("Explicit fuel exhausted before the proven bound")
    return result


def verify_certificate(a, certificate):
    """Finite exact verification of the returned mathematical certificate."""
    a = matrix(a)
    n = len(a)
    q, d = certificate["Q"], certificate["d"]
    b = certificate["transformed"]
    return (
        a == transpose(a)
        and len(q) == n
        and all(len(row) == n for row in q)
        and len(d) == n
        and matmul(transpose(q), q) == identity(n)
        and matmul(q, transpose(q)) == identity(n)
        and conjugate(a, q) == b
        and d == [b[i][i] for i in range(n)]
        and d == sorted(d)
        and offdiag_sq(b) == certificate["residual_sq"]
        and offdiag_sq(b) <= certificate["epsilon"] ** 2
        and frob_sq(a) == frob_sq(b)
        and certificate["steps"] <= certificate["fuel"]
    )


def serialize(value):
    """JSON-safe exact output; fractions use numerator/denominator pairs."""
    if isinstance(value, F):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, dict):
        return {key: serialize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [serialize(item) for item in value]
    return value


if __name__ == "__main__":
    import json

    example = matrix([[2, 1], [1, 3]])
    certificate = jacobi(example, F(1, 4))
    print(json.dumps(serialize({"input": example, "certificate": certificate,
                                "verified": verify_certificate(example, certificate)}),
                     indent=2))
