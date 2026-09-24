#!/usr/bin/env python3
"""Exact finite checks for Positive Moment Functionals with Invisible Negative Mass.

Only FINITE Hahn polynomials with rational exponents/coefficients are represented.
No floating-point specialization of t, truncation of a product, or claim of an
infinite/formal proof is made. Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations
import json
from math import factorial
from pathlib import Path
import random
from typing import Callable

Series = dict[Q, Q]
Polynomial = list[Q]                    # ascending ordinary powers of X
HahnPolynomial = list[Series]          # finite Hahn-polynomial coefficients


def clean(a: Series) -> Series:
    return {e: c for e, c in a.items() if c}


def constant(c: int | Q) -> Series:
    c = Q(c)
    return {Q(0): c} if c else {}


def monomial(e: int | Q, c: int | Q = 1) -> Series:
    c = Q(c)
    return {Q(e): c} if c else {}


def add(a: Series, b: Series) -> Series:
    out = a.copy()
    for e, c in b.items():
        out[e] = out.get(e, Q(0)) + c
    return clean(out)


def scale(a: Series, c: int | Q) -> Series:
    return clean({e: v * Q(c) for e, v in a.items()})


def mul(a: Series, b: Series) -> Series:
    out: Series = {}
    for e, c in a.items():
        for f, d in b.items():
            out[e + f] = out.get(e + f, Q(0)) + c * d
    return clean(out)


def total(terms) -> Series:
    ans: Series = {}
    for term in terms:
        ans = add(ans, term)
    return ans


def leading(a: Series) -> tuple[Q, Q]:
    if not a:
        raise ValueError("The zero series has no finite leading exponent.")
    e = min(a)
    return e, a[e]


def positive(a: Series) -> bool:
    return bool(a) and leading(a)[1] > 0


def poly_mul(a: Polynomial, b: Polynomial) -> Polynomial:
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        for j, d in enumerate(b):
            out[i + j] += c * d
    return out


def poly_eval(p: Polynomial, x: Q) -> Q:
    ans = Q(0)
    for c in reversed(p):
        ans = ans * x + c
    return ans


def hpoly_eval(p: HahnPolynomial, x: Q) -> Series:
    ans: Series = {}
    for c in reversed(p):
        ans = add(scale(ans, x), c)
    return ans


A = Q(3, 4)


def x(n: int) -> Q:
    if n < 1:
        raise ValueError("n must be positive")
    return Q(1, n + 1)


def q(n: int) -> Q:
    if n < 1:
        raise ValueError("n must be positive")
    return Q(n, n + 1)


def signed_model(n: int) -> dict[Q, Series]:
    """mu_n: n early atoms, one compensating anchor, and mass -t at zero."""
    if n < 1:
        raise ValueError("n must be positive")
    anchor = add(constant(1), monomial(1))
    for j in range(1, n + 1):
        anchor = add(anchor, monomial(q(j), -1))
    return {A: anchor, **{x(j): monomial(q(j)) for j in range(1, n + 1)},
            Q(0): monomial(1, -1)}


def integrate_real(mu: dict[Q, Series], f: Callable[[Q], Q]) -> Series:
    return total(scale(w, f(node)) for node, w in mu.items())


def integrate_square(mu: dict[Q, Series], p: HahnPolynomial,
                     g: Callable[[Q], Q] = lambda u: Q(1)) -> Series:
    return total(scale(mul(w, mul(hpoly_eval(p, node), hpoly_eval(p, node))), g(node))
                 for node, w in mu.items())


def moment(mu: dict[Q, Series], k: int,
           g: Callable[[Q], Q] = lambda u: Q(1)) -> Series:
    return integrate_real(mu, lambda u: g(u) * u ** k)


def permutation_sign(p: tuple[int, ...]) -> int:
    inversions = sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p)))
    return -1 if inversions % 2 else 1


def determinant(matrix: list[list[Series]]) -> Series:
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("Matrix must be square.")
    ans: Series = {}
    for p in permutations(range(n)):
        term = constant(permutation_sign(p))
        for i in range(n):
            term = mul(term, matrix[i][p[i]])
        ans = add(ans, term)
    return ans


def vandermonde_squared(nodes) -> Q:
    ans = Q(1)
    for a, b in combinations(nodes, 2):
        ans *= (b - a) ** 2
    return ans


def cauchy_binet(mu: dict[Q, Series], d: int,
                 g: Callable[[Q], Q]) -> Series:
    ans: Series = {}
    for nodes in combinations(mu, d + 1):
        term = constant(vandermonde_squared(nodes))
        for node in nodes:
            term = mul(term, scale(mu[node], g(node)))
        ans = add(ans, term)
    return ans


def predicted_lc(d: int) -> Q:
    numerator = 1
    for j in range(1, d + 1):
        numerator *= (3 * j - 1) * factorial(j - 1)
    return Q(numerator, 4 ** d * factorial(d + 1) ** d) ** 2


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def check(self, condition: bool, category: str, detail: str) -> None:
        if not condition:
            raise AssertionError(f"{category}: {detail}")
        self.counts[category] += 1


def run_checks() -> dict:
    checks = Checks()
    localizers = {
        "1": lambda u: Q(1),
        "X": lambda u: u,
        "1-X": lambda u: 1 - u,
        "X(1-X)": lambda u: u * (1 - u),
    }
    # Independent determinant and subset-expansion computations; no leading-term shortcut.
    determinant_records = []
    for n in range(1, 6):
        mu = signed_model(n)
        checks.check(moment(mu, 0) == constant(1), "normalization", f"n={n}")
        checks.check(mu[Q(0)] == monomial(1, -1), "negative_event", f"n={n}")
        for d in range(min(n, 3) + 1):
            for name, g in localizers.items():
                moments = [moment(mu, k, g) for k in range(2 * d + 1)]
                matrix = [[moments[i + j] for j in range(d + 1)]
                          for i in range(d + 1)]
                det = determinant(matrix)
                cb = cauchy_binet(mu, d, g)
                checks.check(det == cb, "Cauchy_Binet", f"n={n}, d={d}, g={name}")
                nodes = [A] + [x(j) for j in range(1, d + 1)]
                lc = predicted_lc(d)
                for node in nodes:
                    lc *= g(node)
                val = sum((q(j) for j in range(1, d + 1)), Q(0))
                checks.check(leading(det) == (val, lc), "determinant_leading_term",
                             f"n={n}, d={d}, g={name}")
                if n == 5:
                    determinant_records.append({"d": d, "localizer": name,
                                                "valuation": str(val),
                                                "leading_coefficient": str(lc)})

    # Exact detector showing that each finite approximation eventually fails positivity.
    detector_records = []
    for n in range(1, 9):
        p: Polynomial = [Q(1)]
        for node in [A] + [x(j) for j in range(1, n + 1)]:
            p = poly_mul(p, [-node, Q(1)])
        hp = [constant(c) for c in p]
        old_value = integrate_square(signed_model(n), hp)
        expected = monomial(1, -poly_eval(p, Q(0)) ** 2)
        checks.check(old_value == expected, "finite_negative_detector", f"n={n}")
        new_value = integrate_square(signed_model(n + 1), hp)
        checks.check(leading(new_value) == (q(n + 1), poly_eval(p, x(n + 1)) ** 2),
                     "next_atom_restores_positivity", f"n={n}")
        detector_records.append({"early_atoms": n, "detector_degree": n + 1,
                                 "negative_value_coefficient_at_1": str(expected[Q(1)]),
                                 "restored_valuation": str(q(n + 1))})

    # Random finite Hahn coefficients, including negative exponents and cancellation.
    rng = random.Random(20260922)
    for trial in range(96):
        degree = rng.randrange(0, 4)
        p: HahnPolynomial = []
        for _ in range(degree + 1):
            c: Series = {}
            for _ in range(3):
                exponent = rng.choice([Q(-2), Q(-1, 3), Q(0), Q(1, 5), Q(7, 3)])
                c = add(c, monomial(exponent, Q(rng.randrange(-4, 5),
                                               rng.randrange(1, 5))))
            p.append(c)
        if not any(p):
            p[0] = constant(1)
        for name, g in localizers.items():
            # There are five distinct early atoms and degree <= 3, so a leading
            # coefficient polynomial cannot vanish at all of them.
            checks.check(positive(integrate_square(signed_model(5), p, g)),
                         "Hahn_coefficient_positivity", f"trial={trial}, g={name}")

    # Coefficient-level simple-spectrum recurrences, including the node 0.
    for left, right in [(x(j), A) for j in range(1, 9)] + [(A, Q(0))]:
        seq = [left ** k - right ** k for k in range(12)]
        for k in range(10):
            checks.check(seq[k + 2] - (left + right) * seq[k + 1]
                         + left * right * seq[k] == 0,
                         "coefficient_recurrence", f"nodes={left},{right}; k={k}")

    # Continuous tent tests: finite model must contain the first nonzero early atom.
    tent_records = []
    mu = signed_model(9)
    for k in range(2, 10):
        val = integrate_real(mu, lambda u, k=k: max(Q(0), 1 - k * u))
        checks.check(leading(val) == (q(k), Q(1, k + 1)),
                     "continuous_tent_test", f"k={k}")
        tent_records.append({"k": k, "valuation": str(q(k)),
                             "leading_coefficient": str(Q(1, k + 1))})

    # Closed Vandermonde formula and harmonic-number valuation, beyond matrix tests.
    closed_form_records = []
    for d in range(13):
        nodes = [A] + [x(j) for j in range(1, d + 1)]
        checks.check(vandermonde_squared(nodes) == predicted_lc(d),
                     "closed_Vandermonde_formula", f"d={d}")
        val = sum((q(j) for j in range(1, d + 1)), Q(0))
        harmonic = sum((Q(1, j) for j in range(1, d + 2)), Q(0))
        checks.check(val == d + 1 - harmonic, "harmonic_valuation", f"d={d}")
        if d >= 1:
            previous_q = q(d - 1) if d > 1 else Q(0)
            checks.check(q(d) - previous_q == Q(1, d * (d + 1)),
                         "Jacobi_recurrence_valuation", f"d={d}")
        closed_form_records.append({"d": d, "valuation": str(val),
                                    "leading_coefficient": str(predicted_lc(d))})

    return {
        "status": "PASS",
        "arithmetic": "exact fractions; finite sparse Hahn polynomials; no floating point",
        "seed": 20260922,
        "total_assertions": sum(checks.counts.values()),
        "assertions_by_category": dict(sorted(checks.counts.items())),
        "scope": ("Finite algebraic checks only. Infinite support arguments, measure "
                  "classification, positivity for every degree, and quadrature existence "
                  "are proved in the article, not certified by this program."),
        "determinant_records_for_5_early_atoms": determinant_records,
        "finite_negative_detectors": detector_records,
        "continuous_tent_tests": tent_records,
        "closed_form_records": closed_form_records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    result = run_checks()
    (args.output_dir / "verification_results.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    lines = ["EXACT FINITE VERIFICATION: PASS",
             f"Assertions: {result['total_assertions']}",
             f"Arithmetic: {result['arithmetic']}", ""]
    lines += [f"{name}: {count}" for name, count in result["assertions_by_category"].items()]
    lines += ["", result["scope"], "", "Run: python3 verify.py"]
    summary = "\n".join(lines) + "\n"
    (args.output_dir / "verification_summary.txt").write_text(summary, encoding="utf-8")
    print(summary)


if __name__ == "__main__":
    main()
