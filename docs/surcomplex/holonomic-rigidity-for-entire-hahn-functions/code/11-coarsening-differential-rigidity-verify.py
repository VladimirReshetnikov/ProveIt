#!/usr/bin/env python3
"""Exact finite checks accompanying article.tex.

These checks are NOT proofs of infinite-support, all-order, or cardinal claims.
Requires Python >= 3.9 and SymPy. No network or external service is used.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product, combinations
import json
from pathlib import Path
import platform
from typing import Dict, List

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: python -m pip install sympy") from exc


Vector = Dict[int, Fraction]


def add(a: Vector, b: Vector) -> Vector:
    result = dict(a)
    for key, value in b.items():
        result[key] = result.get(key, Fraction(0)) + value
        if result[key] == 0:
            del result[key]
    return result


def scale(n: int, a: Vector) -> Vector:
    return {i: n * x for i, x in a.items() if n * x}


def compare(a: Vector, b: Vector) -> int:
    diff = add(a, scale(-1, b))
    if not diff:
        return 0
    value = diff[max(diff)]
    return 1 if value > 0 else -1


def code(bits: tuple) -> int:
    value = 1
    for bit in bits:
        if bit not in (0, 1):
            raise ValueError("Binary words must contain only 0 or 1.")
        value = 2 * value + bit
    return value


def run_checks() -> dict:
    groups: List[dict] = []

    def record(name: str, cases: int, purpose: str) -> None:
        groups.append({"name": name, "cases": cases, "status": "passed", "purpose": purpose})

    def require(condition: bool, message: str) -> None:
        if not condition:
            raise AssertionError(message)

    z, a, b, c, T = sp.symbols("z a b c T")
    Y = sp.symbols("Y0:4")

    def evaluation(P, p, r):
        return sp.expand(P.subs({Y[j]: sp.diff(p, z, j) for j in range(r + 1)}, simultaneous=True))

    def order(p):
        p = sp.Poly(sp.expand(p), z)
        if p.is_zero:
            return None
        return min(monom[0] for monom, value in p.terms() if value != 0)

    # Check the exact coefficient-isolation identity, not just numerical values.
    polynomials = [
        (Y[1] - Y[0] ** 2 - z, 1),
        (z ** 2 * Y[0] * Y[2] + z * Y[0] * Y[1] - z ** 2 * Y[1] ** 2, 2),
        (Y[2] ** 2 + z * Y[0] * Y[1] + 1 + z ** 2, 2),
        ((1 + z) * Y[3] ** 2 + z ** 2 * Y[0] ** 3 + Y[1], 3),
    ]
    bases = [1 + z, 1 - 2 * z + 3 * z ** 2, z ** 3 + sp.Rational(1, 2) * z ** 4]
    cases = 0
    for P, r in polynomials:
        for p in bases:
            Aj = [evaluation(sp.diff(P, Y[j]), p, r) for j in range(r + 1)]
            active = [(order(Aj[j]) - j) for j in range(r + 1) if Aj[j] != 0]
            require(bool(active), "Sample must have a nonzero linearization")
            s = min(active)
            Cj = [sp.expand(Aj[j]).coeff(z, s + j) if s + j >= 0 else 0 for j in range(r + 1)]
            Q = sp.expand(sum(Cj[j] * sp.prod(T - k for k in range(j)) for j in range(r + 1)))
            require(Q != 0, "Indicial polynomial incorrectly vanished")
            n = max(r + 2, s + 2 * r + 2, sp.degree(p, z) + 2)
            tail = a * z ** n + b * z ** (n + 1) + c * z ** (n + 2)
            difference = evaluation(P, p + tail, r) - evaluation(P, p, r)
            lhs = sp.expand(difference).coeff(z, n + s)
            require(sp.expand(lhs - a * Q.subs(T, n)) == 0, "Tail isolation failed")
            cases += 1
    record("singular_tail_coefficient_isolation", cases,
           "Exact multivariate Taylor coefficient identity for orders 1--3; does not prove the general lemma.")

    # Repository corner example, including the m=0 boundary.
    P = z ** 2 * Y[0] * Y[2] + z * Y[0] * Y[1] - z ** 2 * Y[1] ** 2
    cases = 0
    for m in range(10):
        p = a * z ** m
        require(evaluation(P, p, 2) == 0, "Monomial solution identity failed")
        Aj = [evaluation(sp.diff(P, Y[j]), p, 2) for j in range(3)]
        s = min(order(Aj[j]) - j for j in range(3) if Aj[j] != 0)
        Q = sum(sp.expand(Aj[j]).coeff(z, s + j) * sp.prod(T - k for k in range(j)) for j in range(3))
        require(s == m and sp.expand(Q - a * (T - m) ** 2) == 0, "Corner indicial identity failed")
        cases += 1
    record("vanishing_corner_indicial_polynomial", cases, "Q(T)=a(T-m)^2 and s=m for 0 <= m <= 9.")

    # Exact Painleve I recurrence using rational initial coefficients.
    cases = 0
    for a0, a1 in [(Fraction(0), Fraction(0)), (Fraction(1, 3), Fraction(-2, 5)), (Fraction(1), Fraction(1))]:
        coeffs = [a0, a1]
        for n in range(24):
            rhs = 6 * sum((coeffs[j] * coeffs[n - j] for j in range(n + 1)), Fraction(0))
            rhs += int(n == 1)
            coeffs.append(rhs / ((n + 1) * (n + 2)))
        for n in range(24):
            lhs = (n + 1) * (n + 2) * coeffs[n + 2]
            rhs = 6 * sum((coeffs[j] * coeffs[n - j] for j in range(n + 1)), Fraction(0)) + int(n == 1)
            require(lhs == rhs, "Painleve recurrence failed")
            cases += 1
    record("painleve_local_formal_solutions", cases, "24 coefficient equations for each of three rational initial conditions.")

    # Common coarsened factor model: reduction of g,h need not preserve the individual series.
    eps = sp.symbols("epsilon")
    cases = 0
    for G, H, A in [(1 + b * z, 1 - a * z + z ** 2, z + z ** 3),
                    (z + z ** 2, z * (1 + a * z), 1 + z ** 2),
                    (1 + z ** 4, 1 - b * z, z ** 5 - z)]:
        g, h = sp.expand(G * (1 + eps * A)), sp.expand(H * (1 + eps * A))
        require(sp.cancel(g / h - G / H) == 0, "Rational quotient identity failed")
        require(sp.expand(g.subs(eps, 0) - G) == 0 and sp.expand(h.subs(eps, 0) - H) == 0,
                "Polynomial reduction model failed")
        cases += 1
    record("common_factor_reduction_models", cases, "Finite polynomial models of simultaneous numerator/denominator reduction.")

    # Binary prefix coding; distinct paths share exactly their common prefix codes.
    cases = 0
    for length in range(1, 9):
        words = list(product((0, 1), repeat=length))
        values = [code(word) for word in words]
        require(set(values) == set(range(2 ** length, 2 ** (length + 1))), "Coding range failed")
        cases += 1
    paths = list(product((0, 1), repeat=7))
    for x, y in combinations(paths, 2):
        common = next((i for i in range(7) if x[i] != y[i]), 7)
        sx = {code(x[:j]) for j in range(1, 8)}
        sy = {code(y[:j]) for j in range(1, 8)}
        require(sx & sy == {code(x[:j]) for j in range(1, common + 1)}, "Prefix overlap failed")
        cases += 1
    record("binary_prefix_coding", cases, "Eight code ranges and all pairs of length-seven branches; not an infinite-family proof.")

    # High coordinates dominate every chosen multiple of fixed low coordinates.
    cases = 0
    for g1, g2, b1, b2 in product((-3, 0, 4), repeat=4):
        gamma = {i: Fraction(x) for i, x in [(1, g1), (2, g2)] if x}
        beta = {i: Fraction(x) for i, x in [(1, b1), (2, b2)] if x}
        for n in [1, 2, 10, 100, 1000]:
            value = add({3: Fraction(1)}, scale(n, gamma))
            require(compare(value, beta) > 0, "Reverse lex weighted comparison failed")
            cases += 1
    # Exterior scale makes leading values decrease.
    previous = None
    for n in range(1, 31):
        value = {n: Fraction(1), 100: Fraction(-n)}
        if previous is not None:
            require(compare(value, previous) < 0, "Exterior escape comparison failed")
            cases += 1
        previous = value
    record("finite_reverse_lexicographic_tests", cases, "Weighted growth and loss of summability after adding an exterior scale.")

    # Initial generator valuations can hide a direction appearing after subtraction.
    alpha, beta = (Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))
    first = {alpha: Fraction(1)}
    second = {alpha: Fraction(1), beta: Fraction(1)}
    diff = dict(second)
    for key, value in first.items():
        diff[key] -= value
        if not diff[key]:
            del diff[key]
    require(diff == {beta: Fraction(1)}, "Generator cancellation example failed")
    record("generator_value_cancellation", 1, "t^alpha and t^alpha+t^beta reveal t^beta after subtraction.")

    u = 1 / (z - c)
    require(sp.cancel(sp.diff(u, z) + u ** 2) == 0, "Riccati identity failed")
    cases = 1
    for prime in (2, 3, 5, 7):
        require(all((prime * n) % prime == 0 for n in range(1, 31)), "Characteristic-p derivative test failed")
        cases += 1
    record("boundary_equations", cases, "Riccati rational solution and finite characteristic-p derivative checks.")

    return {
        "status": "all finite checks passed",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "groups": groups,
        "number_of_groups": len(groups),
        "total_finite_cases": sum(x["cases"] for x in groups),
        "limitations": [
            "No Lean verification was performed.",
            "Finite checks do not prove arbitrary-support well-ordering or summability.",
            "Finite checks do not prove the general coefficient-field or descent theorem.",
            "Finite checks do not prove continuum-sized differential independence.",
            "No surreal sums were numerically approximated.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    try:
        result = run_checks()
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (AssertionError, OSError, ValueError) as exc:
        raise SystemExit(f"Verification failed: {exc}") from exc
    print(f"{result['number_of_groups']} check groups passed ({result['total_finite_cases']} finite cases).")
    print(f"Recorded in {args.output.resolve()}")


if __name__ == "__main__":
    main()
