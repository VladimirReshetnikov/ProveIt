#!/usr/bin/env python3
"""Exact certificates for the counterexamples in article.tex.

Python 3.9+, standard library only. Fractions, not floats, are used in every
algebraic check. The finite tests supplement the all-real proofs in the article;
they are not a replacement for those proofs.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from pathlib import Path
from typing import Callable, List, Sequence, Tuple

Polynomial = List[F]  # coefficients in ascending order


def normalize(x: F) -> Tuple[F, F]:
    """Return (scale,u), with x=scale*u, scale a power of 8, 1<=u<8."""
    if x <= 0:
        raise ValueError("normalize expects a positive rational")
    scale, u = F(1), F(x)
    while u < 1:
        scale /= 8
        u *= 8
    while u >= 8:
        scale *= 8
        u /= 8
    return scale, u


def cubic(x: F) -> F:
    """The odd, self-similar, two-branch counterexample."""
    x = F(x)
    if x == 0:
        return F(0)
    if x < 0:
        return -cubic(-x)
    scale, u = normalize(x)
    return scale * ((u + 5) / 2 if u <= 3 else 4 * u - 8)


def conjugating_map(x: F, inverse: bool = False) -> F:
    """Independent polygonal conjugacy H, or its exact inverse."""
    if x == 0:
        return F(0)
    if x < 0:
        return -conjugating_map(-x, inverse)
    scale, u = normalize(F(x))
    if inverse:
        v = (u + 1) / 2 if u <= 3 else (2 * u - 4 if u <= 4 else u)
    else:
        v = 2 * u - 1 if u <= 2 else (u / 2 + 2 if u <= 4 else u)
    return scale * v


def iterate(f: Callable[[F], F], x: F, n: int) -> F:
    if n < 0:
        raise ValueError("iterate expects a nonnegative count")
    for _ in range(n):
        x = f(x)
    return x


def poly_mul(p: Sequence[F], q: Sequence[F]) -> Polynomial:
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def poly_power(p: Sequence[F], n: int) -> Polynomial:
    r = [F(1)]
    for _ in range(n):
        r = poly_mul(r, p)
    return r


def det(matrix: Sequence[Sequence[F]]) -> F:
    a = [[F(x) for x in row] for row in matrix]
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError("det expects a square matrix")
    result = F(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        value = a[j][j]
        result *= value
        for i in range(j + 1, n):
            multiple = a[i][j] / value
            for k in range(j + 1, n):
                a[i][k] -= multiple * a[j][k]
    return result


def residual(p: Sequence[F], u: Callable[[int], F], n: int) -> F:
    return sum((a * u(n + j) for j, a in enumerate(p)), F(0))


def certificate(p: Polynomial, u: Callable[[int], F]) -> dict:
    d = len(p) - 1
    for n in range(-80, 81):
        assert residual(p, u, n) == 0, (n, p)
    matrix = [[u(i + j) for j in range(d)] for i in range(d)]
    determinant = det(matrix)
    assert determinant != 0, "This orbit does not certify the claimed degree"
    return {
        "polynomial_ascending": [str(x) for x in p],
        "first_terms": [str(u(n)) for n in range(max(12, 2 * d))],
        "hankel_matrix": [[str(x) for x in row] for row in matrix],
        "hankel_determinant": str(determinant),
        "recurrence_checks": 161,
        "checks_start": -80,
        "checks_end": 80,
    }


def run() -> dict:
    if not __debug__:
        raise RuntimeError("Run this verifier without -O: its assertions must remain enabled")
    # Test both formulas, inverse identities and global scaling on exact rationals.
    points = {F(p, q) * F(8) ** k
              for q in range(1, 13)
              for p in range(-48, 49)
              for k in range(-3, 4)}
    points.update(F(b) * F(8) ** k
                  for b in (1, 2, 3, 4, 8) for k in range(-12, 13))
    for x in sorted(points):
        fx = cubic(x)
        assert iterate(cubic, x, 3) == 8 * x
        assert cubic(8 * x) == 8 * fx
        assert cubic(-x) == -fx
        assert fx == conjugating_map(2 * conjugating_map(x, inverse=True))
        inv = iterate(cubic, x / 8, 2)
        assert cubic(inv) == x
        assert iterate(cubic, fx / 8, 2) == x
    ordered = sorted(points)
    for x, y in zip(ordered, ordered[1:]):
        slope = (cubic(y) - cubic(x)) / (y - x)
        assert F(1, 2) <= slope <= 4

    cubic_poly = [F(-8), F(0), F(0), F(1)]
    cubic_orbit = lambda n: F(8) ** (n // 3) * (F(1), F(3), F(4))[n % 3]
    c3 = certificate(cubic_poly, cubic_orbit)
    assert c3["hankel_determinant"] == "-56"

    # h(n) = n + sin(pi*n/2)/4, exactly evaluated through the 4-cycle.
    analytic_orbit = lambda n: F(n) + F((0, 1, 0, -1)[n % 4], 4)
    quartic_poly = poly_mul(poly_power([F(-1), F(1)], 2),
                            [F(1), F(0), F(1)])
    c4 = certificate(quartic_poly, analytic_orbit)
    real_only_residual = residual([F(1), F(-2), F(1)], analytic_orbit, 0)
    assert real_only_residual == F(-1, 2)
    for n in range(-80, 81):
        assert analytic_orbit(n + 4) == analytic_orbit(n) + 4

    # A repeated positive root: h(t)=2^t(t^2+16).
    repeated_poly = poly_power([F(-2), F(1)], 3)
    repeated_orbit = lambda n: F(2) ** n * (n * n + 16)
    cr = certificate(repeated_poly, repeated_orbit)

    # Nontrivial repeated circular spectrum:
    # h(t)=2^t[(t^2+64)^2 + t^2*cos(pi*t/2)/1024 + t^3*cos(pi*t)/1024].
    # The article's explicit derivative estimates certify monotonicity.
    mixed_poly = poly_mul(poly_power([F(-2), F(1)], 5),
                          poly_mul(poly_power([F(2), F(1)], 4),
                                   poly_power([F(4), F(0), F(1)], 3)))
    def mixed_orbit(n: int) -> F:
        w = F((n * n + 64) ** 2)
        w += F(n * n * (1, 0, -1, 0)[n % 4], 1024)
        w += F(n ** 3 * (1, -1)[n % 2], 1024)
        return F(2) ** n * w
    cm = certificate(mixed_poly, mixed_orbit)

    return {
        "arithmetic": "fractions.Fraction, exact rational arithmetic throughout",
        "scope": "Finite checks and algebraic certificates; see article for all-real proofs",
        "distinct_rational_test_points": len(points),
        "adjacent_exact_secant_checks": len(points) - 1,
        "cubic": c3,
        "analytic_quartic": c4,
        "quartic_real_only_residual_at_zero": str(real_only_residual),
        "repeated_positive_root": cr,
        "mixed_repeated_circular_spectrum": cm,
        "result": "PASS",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" /
                                "exact_certificates.json")
    args = parser.parse_args()
    report = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("PASS: exact verification completed")
    print("Distinct rational points:", report["distinct_rational_test_points"])
    print("Cubic Hankel determinant:", report["cubic"]["hankel_determinant"])
    print("Analytic quartic Hankel determinant:",
          report["analytic_quartic"]["hankel_determinant"])
    print("Certificate:", args.output)


if __name__ == "__main__":
    main()
