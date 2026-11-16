#!/usr/bin/env python3
"""Exact finite norm constructors and reproducible checks.

Polynomials are tuples of rational coefficients in ascending degree order;
the zero polynomial is (). Matrices act on column coefficient vectors.
No floating-point arithmetic or symbolic-algebra package is used.

This is a reference implementation, not an iPRA proof checker. All-input
correctness is proved in the report; the checks here exercise independent
consequences of the definitions and deliberately degenerate fibers.
"""

from __future__ import annotations

from fractions import Fraction as Q
from itertools import permutations
from math import gcd
from pathlib import Path
import json
import random


def poly(values=()):
    out = [Q(x) for x in values]
    while out and not out[-1]:
        out.pop()
    return tuple(out)


ZERO = ()
ONE = (Q(1),)


def add(a, b):
    return poly((a[i] if i < len(a) else 0) +
                (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def neg(a):
    return tuple(-x for x in a)


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    if not a or not b:
        return ZERO
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return poly(out)


def power(a, n):
    if n < 0:
        raise ValueError("The exponent must be nonnegative")
    out = ONE
    for _ in range(n):
        out = mul(out, a)
    return out


def evaluate(a, x):
    out = Q(0)
    for coefficient in reversed(a):
        out = coefficient + x * out
    return out


def degree(a):
    return len(poly(a)) - 1


def sign(p):
    return -1 if sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p))) % 2 else 1


def determinant(M):
    """Leibniz expansion; factorially bounded, with exact coefficients."""
    m = len(M)
    if any(len(row) != m for row in M):
        raise ValueError("The matrix must be square")
    out = ZERO
    for p in permutations(range(m)):
        term = poly([sign(p)])
        for j in range(m):
            term = mul(term, M[p[j]][j])
        out = add(out, term)
    return out


def matrix_add(M, N):
    return [[add(a, b) for a, b in zip(r, s)] for r, s in zip(M, N)]


def matrix_mul(M, N):
    m = len(M)
    return [[sum_polys(mul(M[i][k], N[k][j]) for k in range(m))
             for j in range(m)] for i in range(m)]


def sum_polys(ps):
    out = ZERO
    for p in ps:
        out = add(out, p)
    return out


def general_monic_matrix(F, A):
    """Norm matrix for Y^m+sum F[i](X)Y^i and G=sum A[i](X)Y^i.

    Both lists have length m. This computes sum A_i*T^i from the
    companion matrix T, independently of the specialized entry formula.
    """
    m = len(F)
    if not m or len(A) != m:
        raise ValueError("Need equally sized nonempty coefficient lists")
    T = [[ZERO for _ in range(m)] for _ in range(m)]
    for j in range(m - 1):
        T[j + 1][j] = ONE
    for i in range(m):
        T[i][m - 1] = neg(F[i])
    I = [[ONE if i == j else ZERO for j in range(m)] for i in range(m)]
    M = [[ZERO for _ in range(m)] for _ in range(m)]
    current = I
    for coefficient in A:
        M = matrix_add(M, [[mul(coefficient, p) for p in row]
                           for row in current])
        current = matrix_mul(current, T)
    return M


def superelliptic_matrix(m, f, A):
    if m < 1 or len(A) != m:
        raise ValueError("Need m >= 1 and exactly m coefficient polynomials")
    return [[mul(A[(r - j) % m], power(f, (((r - j) % m) + j) // m))
             for j in range(m)] for r in range(m)]


def superelliptic_norm(m, f, A):
    return determinant(superelliptic_matrix(m, f, A))


def weighted_degree(m, f, A):
    if m < 2 or degree(f) < 1 or gcd(m, degree(f)) != 1:
        raise ValueError("Need m >= 2, deg f >= 1, and coprime degrees")
    if len(A) != m or not any(A):
        raise ValueError("Need exactly m coefficients, not all zero")
    return max((m * degree(a) + degree(f) * i, i)
               for i, a in enumerate(A) if a)


def scalar_determinant(M):
    """Independent rational Gaussian-elimination determinant."""
    A = [[Q(x) for x in row] for row in M]
    m = len(A)
    out = Q(1)
    for j in range(m):
        pivot = next((i for i in range(j, m) if A[i][j]), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            A[pivot], A[j] = A[j], A[pivot]
            out = -out
        c = A[j][j]
        out *= c
        for i in range(j + 1, m):
            q = A[i][j] / c
            for k in range(j, m):
                A[i][k] -= q * A[j][k]
    return out


def divide_linear(p, a):
    """Return q,r with p=(X-a)q+r by exact synthetic division."""
    if len(p) < 2:
        return ZERO, (p[0] if p else Q(0))
    q = [Q(0)] * (len(p) - 1)
    q[-1] = p[-1]
    for k in range(len(q) - 2, -1, -1):
        q[k] = p[k + 1] + a * q[k + 1]
    r = p[0] + a * q[0]
    return poly(q), r


def multiplicity(p, a):
    if not p:
        raise ValueError("The zero polynomial has no finite multiplicity")
    count = 0
    while len(p) > 1:
        q, r = divide_linear(p, a)
        if r:
            break
        p = q
        count += 1
    return count


def evaluate_G(A, x, y):
    return sum((evaluate(a, x) * y ** i for i, a in enumerate(A)), Q(0))


def checks():
    rng = random.Random(20261115)
    counts = {"norm_degree_and_leading_coefficient": 0,
              "independent_companion_matrices": 0,
              "independent_determinant_evaluations": 0,
              "hyperelliptic_norm_identities": 0,
              "evaluation_row_identities": 0,
              "fiber_multiplicity_checks": 0,
              "sharp_examples": 0,
              "necessary_hypothesis_checks": 0}
    for m in range(2, 6):
        for d in range(1, 8):
            if gcd(m, d) != 1:
                continue
            for case in range(3):
                f = poly([rng.randint(-2, 2) for _ in range(d)] + [rng.choice([-2, -1, 1, 2])])
                A = [poly(rng.randint(-2, 2) for _ in range(rng.randrange(4)))
                     for _ in range(m)]
                if not any(A):
                    A[case % m] = ONE
                w, k = weighted_degree(m, f, A)
                M = superelliptic_matrix(m, f, A)
                N = determinant(M)
                shift = [(j + k) % m for j in range(m)]
                assert degree(N) == w
                assert N[-1] == sign(shift) * A[k][-1] ** m * f[-1] ** k
                counts["norm_degree_and_leading_coefficient"] += 1
                F = [neg(f)] + [ZERO] * (m - 1)
                assert M == general_monic_matrix(F, A)
                counts["independent_companion_matrices"] += 1
                for x in [Q(-2), Q(0), Q(2, 3)]:
                    scalar = [[evaluate(p, x) for p in row] for row in M]
                    assert evaluate(N, x) == scalar_determinant(scalar)
                    counts["independent_determinant_evaluations"] += 1
                if m == 2:
                    assert N == sub(power(A[0], 2), mul(f, power(A[1], 2)))
                    counts["hyperelliptic_norm_identities"] += 1

    # Force one exact curve point while varying the coefficient functions.
    for m in range(2, 6):
        for b in [Q(-1), Q(0), Q(2)]:
            a = Q(1, 2)
            f = add(poly([b ** m]), mul(poly([-a, 1]), poly([1, 0, 1])))
            A = [poly([i - 1, 2 - i]) for i in range(m)]
            M = superelliptic_matrix(m, f, A)
            for j in range(m):
                left = sum((b ** r * evaluate(M[r][j], a) for r in range(m)), Q(0))
                assert left == evaluate_G(A, a, b) * b ** j
                counts["evaluation_row_identities"] += 1

    # Two distinct ordinates over the same abscissa consume two factors;
    # a ramified fiber y=0 consumes at least one, without any division by y.
    f = poly([1, -1, 0, 1])
    A = [poly([0, 1]), ZERO, ZERO, ZERO]
    N = superelliptic_norm(4, f, A)
    assert evaluate(f, 0) == 1 and evaluate_G(A, 0, 1) == 0
    assert evaluate_G(A, 0, -1) == 0 and multiplicity(N, Q(0)) >= 2
    counts["fiber_multiplicity_checks"] += 1
    f = poly([0, 1, 0, 0, 1])
    A = [ZERO, ONE, ZERO]
    N = superelliptic_norm(3, f, A)
    assert evaluate(f, 0) == 0 and evaluate_G(A, 0, 0) == 0
    assert multiplicity(N, Q(0)) == 1
    counts["fiber_multiplicity_checks"] += 1

    # Sharp m=3, d=4 example: exactly four supplied common points.
    f = poly([1, -8, 14, -7, 1])
    A = [poly([-1]), ONE, ZERO]
    N = superelliptic_norm(3, f, A)
    assert N == sub(f, ONE) and degree(N) == 4
    for a in [Q(0), Q(1), Q(2), Q(4)]:
        assert evaluate(f, a) == 1 and evaluate_G(A, a, 1) == 0
        assert multiplicity(N, a) == 1
    counts["sharp_examples"] += 1

    # Deliberately violate coprimality: the norm is identically zero.
    f = poly([0, 0, 1])
    A = [poly([0, -1]), ONE]
    assert not superelliptic_norm(2, f, A)
    try:
        weighted_degree(2, f, A)
    except ValueError:
        counts["necessary_hypothesis_checks"] += 1
    else:
        raise AssertionError("Coprimality precondition was not checked")

    # Generic monic equation with three rational points in one fiber.
    # F=Y(Y-1)(Y-2)-X, G=X, so det multiplication by G is X^3.
    F = [poly([0, -1]), poly([2]), poly([-3])]
    A = [poly([0, 1]), ZERO, ZERO]
    N = determinant(general_monic_matrix(F, A))
    assert N == poly([0, 0, 0, 1]) and multiplicity(N, Q(0)) == 3
    for b in [Q(0), Q(1), Q(2)]:
        assert b ** 3 + sum(evaluate(F[i], 0) * b ** i for i in range(3)) == 0
    counts["fiber_multiplicity_checks"] += 1
    return {"status": "passed", "arithmetic": "exact fractions.Fraction",
            "scope": "Finite implementation checks; not an iPRA proof checker",
            "counts": counts,
            "sharp_example": {"m": 3, "f": [1, -8, 14, -7, 1],
                              "norm": [0, -8, 14, -7, 1], "bound": 4,
                              "common_points": [[0, 1], [1, 1], [2, 1], [4, 1]]}}


if __name__ == "__main__":
    report = checks()
    destination = Path(__file__).resolve().parents[1] / "validation" / "norm_checks.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
