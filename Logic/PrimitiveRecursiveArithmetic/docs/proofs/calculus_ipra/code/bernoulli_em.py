#!/usr/bin/env python3
"""Exact rational companions to the constructive calculus manuscript.

Only the Python standard library is used.  Polynomials have low-to-high
coefficients in ``fractions.Fraction``.  No floating-point arithmetic occurs.

The validation suite checks finitely many instances of the polynomial FTC,
normalized Bernoulli recurrences, Euler--Maclaurin with its exact remainder,
and the finite-grid defect estimate from the paper.  These checks are useful
regression checks; they are NOT a formal proof of the general theorem or of
its arithmetization in iPRA.

Run from any working directory:
    python3 bernoulli_em.py --validate --output validation.json
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
from typing import Iterable, Sequence

Poly = tuple[Q, ...]
ZERO: Poly = (Q(0),)
ONE: Poly = (Q(1),)


def poly(coefficients: Iterable[Q | int]) -> Poly:
    """Canonical coefficient tuple; the zero polynomial has one coefficient."""
    result = [Q(c) for c in coefficients]
    if not result:
        return ZERO
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result)


def add(f: Poly, g: Poly) -> Poly:
    return poly((f[i] if i < len(f) else 0) +
                (g[i] if i < len(g) else 0)
                for i in range(max(len(f), len(g))))


def scale(c: Q | int, f: Poly) -> Poly:
    return poly(Q(c) * a for a in f)


def sub(f: Poly, g: Poly) -> Poly:
    return add(f, scale(-1, g))


def mul(f: Poly, g: Poly) -> Poly:
    answer = [Q(0)] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            answer[i + j] += a * b
    return poly(answer)


def power(f: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError("The polynomial exponent must be nonnegative")
    answer = ONE
    for _ in range(n):
        answer = mul(answer, f)
    return answer


def evaluate(f: Poly, x: Q | int) -> Q:
    answer = Q(0)
    for a in reversed(f):
        answer = answer * x + a
    return answer


def derivative(f: Poly, order: int = 1) -> Poly:
    if order < 0:
        raise ValueError("The derivative order must be nonnegative")
    for _ in range(order):
        f = poly(i * f[i] for i in range(1, len(f)))
    return f


def primitive(f: Poly) -> Poly:
    """Coefficientwise primitive with constant coefficient zero."""
    return poly([Q(0)] + [a / (i + 1) for i, a in enumerate(f)])


def integral(f: Poly, a: Q | int = 0, b: Q | int = 1) -> Q:
    F = primitive(f)
    return evaluate(F, b) - evaluate(F, a)


def compose_affine(f: Poly, a: Q | int, h: Q | int = 1) -> Poly:
    """Return the polynomial t |-> f(a+h*t)."""
    answer = ZERO
    linear = poly([a, h])
    for c in reversed(f):
        answer = add(mul(answer, linear), poly([c]))
    return answer


def normalized_bernoulli(max_order: int) -> list[Poly]:
    """Return P_n=B_n(x)/n! by primitive plus zero-mean normalization."""
    if max_order < 0:
        raise ValueError("The maximum order must be nonnegative")
    result = [ONE]
    for _ in range(max_order):
        A = primitive(result[-1])
        result.append(sub(A, poly([integral(A)])))
    return result


def bernstein_coefficients(max_order: int) -> list[tuple[Q, ...]]:
    """Bernstein coefficients for P_n, computed without power-basis conversion.

    c_j = (sum_{i<j}(i+1)b_i - sum_{i>=j}(n-i)b_i)/(n(n+1)).
    The absolute coefficient bound contracts by a factor at most 1/2.
    """
    if max_order < 0:
        raise ValueError("The maximum order must be nonnegative")
    result = [(Q(1),)]
    for n in range(1, max_order + 1):
        previous = result[-1]
        result.append(tuple(
            (sum(((i + 1) * previous[i] for i in range(j)), Q(0)) -
             sum(((n - i) * previous[i] for i in range(j, n)), Q(0))) /
            (n * (n + 1))
            for j in range(n + 1)
        ))
    return result


def from_bernstein(coefficients: Sequence[Q]) -> Poly:
    n = len(coefficients) - 1
    answer = ZERO
    for j, c in enumerate(coefficients):
        term = mul(power(poly([0, 1]), j), power(poly([1, -1]), n - j))
        answer = add(answer, scale(c * comb(n, j), term))
    return answer


def em_remainder(f: Poly, a: int, b: int, m: int,
                 bernoulli: Sequence[Poly] | None = None) -> Q:
    """Exact unit-mesh remainder -sum_k int_0^1 P_(2m)(t) f^(2m)(k+t) dt."""
    if b < a or m < 1:
        raise ValueError("Require integer a <= b and m >= 1")
    r = 2 * m
    P = normalized_bernoulli(r) if bernoulli is None else bernoulli
    f_r = derivative(f, r)
    return -sum((integral(mul(P[r], compose_affine(f_r, k)))
                 for k in range(a, b)), Q(0))


def em_sides(f: Poly, a: int, b: int, m: int,
             bernoulli: Sequence[Poly] | None = None) -> tuple[Q, Q]:
    """Inclusive endpoint sum and full exact Euler--Maclaurin right side."""
    if b < a or m < 1:
        raise ValueError("Require integer a <= b and m >= 1")
    P = normalized_bernoulli(2 * m) if bernoulli is None else bernoulli
    lhs = sum((evaluate(f, k) for k in range(a, b + 1)), Q(0))
    rhs = integral(f, a, b) + (evaluate(f, a) + evaluate(f, b)) / 2
    for s in range(1, m + 1):
        d = derivative(f, 2 * s - 1)
        rhs += P[2 * s][0] * (evaluate(d, b) - evaluate(d, a))
    rhs += em_remainder(f, a, b, m, P)
    return lhs, rhs


def em_scaled_sides(f: Poly, a: Q, h: Q, intervals: int,
                    m: int) -> tuple[Q, Q]:
    """Rational mesh version, with inclusive sum multiplied by h.

    Its remainder is -h^(2m+1) sum_k int_0^1
    P_(2m)(t) f^(2m)(a+h*(k+t)) dt.  The degenerate zero-interval
    case is included explicitly by the inclusive-sum convention.
    """
    if h <= 0 or intervals < 0 or m < 1:
        raise ValueError("Require h > 0, intervals >= 0, and m >= 1")
    r = 2 * m
    P = normalized_bernoulli(r)
    b = a + intervals * h
    lhs = h * sum((evaluate(f, a + k * h)
                   for k in range(intervals + 1)), Q(0))
    rhs = integral(f, a, b) + h * (evaluate(f, a) + evaluate(f, b)) / 2
    for s in range(1, m + 1):
        d = derivative(f, 2 * s - 1)
        rhs += h ** (2 * s) * P[2 * s][0] * (evaluate(d, b) - evaluate(d, a))
    f_r = derivative(f, r)
    rhs -= h ** (r + 1) * sum(
        (integral(mul(P[r], compose_affine(f_r, a + k * h, h)))
         for k in range(intervals)), Q(0))
    return lhs, rhs


def ceil_q(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def ceil_log2_q(x: Q) -> int:
    """Smallest nonnegative s with 2^s >= x, for positive rational x."""
    if x <= 0:
        raise ValueError("Require x > 0")
    # For x >= 1, ceil(x) is a sufficient bounded-search limit.
    bound = max(1, ceil_q(x))
    for s in range(bound + 1):
        if Q(2) ** s >= x:
            return s
    raise AssertionError("The proved search bound was insufficient")


def round_down_dyadic(x: Q, bits: int) -> Q:
    """An exact rational oracle: error is nonnegative and less than 2^-bits."""
    denominator = 2 ** bits
    return Q((x.numerator * denominator) // x.denominator, denominator)


def coefficient_bound(f: Poly, radius: Q) -> Q:
    return sum((abs(c) * radius ** i for i, c in enumerate(f)), Q(0))


def second_order_bound(f: Poly, radius: Q) -> Q:
    """Algebraic Taylor remainder bound on |x|, |x+h| <= radius >= 1."""
    return sum((abs(c) * Q(i * (i - 1), 2) * radius ** (i - 2)
                for i, c in enumerate(f) if i >= 2), Q(0))


def finite_grid_check(f: Poly, a: int, b: int, r: int, q: int) -> dict:
    """Check the fully rational finite-grid certificate for one polynomial.

    Precision is p=q+ell+4, so accumulated endpoint evaluation errors
    remain controlled even after H=2^ell derivative differences.
    """
    if not (a < b and r >= 1 and q >= 0):
        raise ValueError("Require a < b, r >= 1, q >= 0")
    P = normalized_bernoulli(r)
    jet = [derivative(f, j) for j in range(r + 1)]
    radius = Q(max(1, abs(a), abs(b)))
    M = max(1, ceil_q(max(coefficient_bound(g, radius) for g in jet)))
    T = max(Q(1), max(second_order_bound(g, radius) for g in jet[:-1]))
    ell = q + ceil_log2_q(T)
    H = 2 ** ell
    h = Q(1, H)
    eps = Q(1, 2 ** q)
    p = q + ell + 4
    oracle_error = Q(1, 2 ** p)
    length = b - a
    D = 2 ** r * (M + 1) * (r + 1) ** 2

    samples: list[list[Q]] = []
    for g in jet:
        values = []
        for global_i in range(length * H + 1):
            exact = evaluate(g, Q(a) + global_i * h)
            value = round_down_dyadic(exact, p)
            assert 0 <= exact - value < oracle_error
            assert abs(value) <= M + oracle_error
            values.append(value)
        samples.append(values)

    quadrature = [Q(0)] * (r + 1)
    for j in range(r + 1):
        quadrature[j] = h * sum(
            (evaluate(P[j], i * h) * samples[j][cell * H + i]
             for cell in range(length) for i in range(H)), Q(0))

    boundary = [Q(0)] * (r + 1)
    defects = [Q(0)] * (r + 1)
    local_checks = 0
    for j in range(1, r + 1):
        boundary[j] = sum(
            (evaluate(P[j], 1) * samples[j - 1][(cell + 1) * H] -
             evaluate(P[j], 0) * samples[j - 1][cell * H]
             for cell in range(length)), Q(0))
        defects[j] = boundary[j] - quadrature[j - 1] - quadrature[j]
        local_sum = Q(0)
        for cell in range(length):
            for i in range(H):
                index = cell * H + i
                t = i * h
                u, u_next = evaluate(P[j], t), evaluate(P[j], t + h)
                v, v_next = samples[j - 1][index:index + 2]
                derivative_value = samples[j][index]
                derivative_error = (v_next - v) - h * derivative_value
                assert abs(derivative_error) <= h * eps + (2 + h) * oracle_error
                assert abs(derivative_error) <= Q(19, 16) * h * eps
                local = u_next * v_next - u * v - h * (
                    u * derivative_value + evaluate(P[j - 1], t) * v)
                # The ring identity used to prove the local estimate.
                expanded = (
                    u * derivative_error +
                    v * ((u_next - u) - h * evaluate(P[j - 1], t)) +
                    (u_next - u) * (v_next - v)
                )
                assert local == expanded
                assert abs(local) <= h * D * eps
                local_sum += local
                local_checks += 1
        assert local_sum == defects[j]
        assert abs(defects[j]) <= length * D * eps
        if j >= 2:
            assert boundary[j] == P[j][0] * (samples[j - 1][-1] - samples[j - 1][0])

    signed_error = sum(((-1) ** (j + 1) * defects[j]
                        for j in range(1, r + 1)), Q(0))
    rhs = (quadrature[0] +
           sum(((-1) ** j * boundary[j] for j in range(2, r + 1)), Q(0)) +
           (-1) ** (r + 1) * quadrature[r] + signed_error)
    assert boundary[1] == rhs
    assert abs(signed_error) <= length * r * D * eps
    return {
        "interval": [a, b], "order": r, "q": q, "ell": ell,
        "oracle_precision": p, "grid_steps": length * H,
        "local_checks": local_checks, "bound_M": M, "constant_D": D,
        "alternating_defect": str(signed_error),
        "proved_instance_bound": str(length * r * D * eps),
    }


def validation() -> dict:
    """Run deterministic finite tests; report every scope explicitly."""
    max_order = 20
    P = normalized_bernoulli(max_order)
    bernstein = bernstein_coefficients(max_order)
    bernoulli_checks = 0
    for n in range(max_order + 1):
        assert from_bernstein(bernstein[n]) == P[n]
        assert max(abs(c) for c in bernstein[n]) <= Q(1, 2 ** n)
        assert sum(abs(c) for c in P[n]) <= Q(3, 2) ** n
        assert compose_affine(P[n], 1, -1) == scale((-1) ** n, P[n])
        bernoulli_checks += 4
        if n >= 1:
            assert derivative(P[n]) == P[n - 1]
            assert integral(P[n]) == 0
            bernoulli_checks += 2
            for j in range(n + 1):
                weight_sum = Q(j * (j + 1) + (n - j) * (n - j + 1), 2 * n * (n + 1))
                assert weight_sum <= Q(1, 2)
                bernoulli_checks += 1
        if n >= 2:
            assert evaluate(P[n], 0) == evaluate(P[n], 1)
            bernoulli_checks += 1
        if n >= 3 and n % 2:
            assert P[n][0] == 0
            bernoulli_checks += 1

    polynomial_cases = [poly(Q((-1) ** (i + degree) * (i + 1), i + 2)
                             for i in range(degree + 1))
                        for degree in range(13)]
    polynomial_cases.extend([ZERO, ONE, poly([0, 1]), poly([0, 0, 1])])
    ftc_intervals = [(Q(-3), Q(2)), (Q(1, 3), Q(7, 5)),
                     (Q(0), Q(0)), (Q(4), Q(-2))]
    ftc_checks = 0
    for f in polynomial_cases:
        assert derivative(primitive(f)) == f
        ftc_checks += 1
        for a, b in ftc_intervals:
            assert integral(derivative(f), a, b) == evaluate(f, b) - evaluate(f, a)
            ftc_checks += 1

    unit_intervals = [(-3, 2), (0, 1), (2, 5), (-2, -2), (-3, -1), (0, 0)]
    em_checks = 0
    nonzero_remainders = 0
    for f in polynomial_cases:
        for a, b in unit_intervals:
            for m in range(1, 7):
                lhs, rhs = em_sides(f, a, b, m, P)
                assert lhs == rhs
                nonzero_remainders += em_remainder(f, a, b, m, P) != 0
                em_checks += 1

    meshes = [(Q(-3, 2), Q(2, 3), 5), (Q(1, 3), Q(1, 5), 0),
              (Q(-2), Q(3, 2), 3), (Q(0), Q(1, 4), 4)]
    scaled_checks = 0
    for f in polynomial_cases:
        for a, h, intervals in meshes:
            for m in range(1, 5):
                lhs, rhs = em_scaled_sides(f, a, h, intervals, m)
                assert lhs == rhs
                scaled_checks += 1

    finite_inputs = [
        (poly([Q(1, 7), Q(1, 5), Q(-1, 6), Q(1, 20)]), -1, 1),
        (poly([Q(1, 3), Q(1, 2), Q(-1, 7), Q(1, 11), Q(1, 13)]), 0, 2),
    ]
    finite_results = [finite_grid_check(f, a, b, r, q)
                      for f, a, b in finite_inputs
                      for r in range(1, 5) for q in (1, 2)]

    example_f = poly([0, 0, 0, 0, 1])
    example_lhs, example_rhs = em_sides(example_f, 0, 3, 1, P)
    assert example_lhs == 98
    return {
        "status": "passed",
        "arithmetic": "exact fractions.Fraction; no floating-point arithmetic",
        "scope": "Finite regression checks, not a formal proof of the universal theorem or iPRA derivability.",
        "normalized_bernoulli": {
            "maximum_order": max_order,
            "checks": bernoulli_checks,
            "bernoulli_numbers": [str(P[n][0] * factorial(n)) for n in range(max_order + 1)],
            "maximum_bernstein_coefficients": [str(max(abs(c) for c in row)) for row in bernstein],
        },
        "polynomial_ftc": {"checks": ftc_checks, "maximum_degree": 12},
        "unit_mesh_euler_maclaurin": {
            "checks": em_checks, "orders_m": [1, 6], "intervals": unit_intervals,
            "nonzero_remainder_instances": nonzero_remainders,
        },
        "rational_mesh_euler_maclaurin": {"checks": scaled_checks, "orders_m": [1, 4]},
        "finite_grid": {
            "cases": len(finite_results),
            "local_product_checks": sum(x["local_checks"] for x in finite_results),
            "details": finite_results,
        },
        "example_x4_sum_0_to_3_order_m1": {
            "sum": str(example_lhs), "right_side": str(example_rhs),
            "integral": str(integral(example_f, 0, 3)),
            "endpoint_half_sum": str((evaluate(example_f, 0) + evaluate(example_f, 3)) / 2),
            "first_correction": str(P[2][0] * (evaluate(derivative(example_f), 3) - evaluate(derivative(example_f), 0))),
            "remainder": str(em_remainder(example_f, 0, 3, 1, P)),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true", help="Run exact finite regression checks")
    parser.add_argument("--output", type=Path, help="Write the validation report as JSON")
    args = parser.parse_args()
    if not args.validate:
        parser.error("Pass --validate to run the exact rational checks")
    report = validation()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    compact = {k: v for k, v in report.items() if k != "finite_grid"}
    compact["finite_grid"] = {k: v for k, v in report["finite_grid"].items() if k != "details"}
    print(json.dumps(compact, indent=2))


if __name__ == "__main__":
    main()
