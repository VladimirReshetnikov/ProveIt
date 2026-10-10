#!/usr/bin/env python3
"""Exact finite audits for the polynomial Lerch saturation theorem.

The all-index theorem is proved in lerch_notes.tex. These computations
independently check its finite algebra, isolate every root of the rational
auxiliary polynomials by SymPy's exact Sturm machinery, and certify both
mesh inequalities for each requested index. No floating-point sign is
used. Requires Python >= 3.10 and SymPy.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import factorial, prod
from pathlib import Path

import sympy as sp


def add_derivative(coeffs: list[Fraction], reciprocal: Fraction) -> list[Fraction]:
    out = coeffs.copy()
    for j in range(len(coeffs) - 1):
        out[j] += reciprocal * (j + 1) * coeffs[j + 1]
    return out


def linear_product(parameters: range) -> list[Fraction]:
    coeffs = [Fraction(1)]
    for a in parameters:
        out = [Fraction(0)] * (len(coeffs) + 1)
        for i, c in enumerate(coeffs):
            out[i] += c
            out[i + 1] += a * c
        coeffs = out
    return coeffs


def as_fraction(value) -> Fraction:
    n, d = value.as_numer_denom()
    return Fraction(int(n), int(d))


def display(value: Fraction | int) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def ceiling(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def verify_index(n: int) -> dict:
    direct = [Fraction(0)] * n + [Fraction(1)]
    for j in range(1, n):
        direct = add_derivative(direct, Fraction(1, j))
    p = linear_product(range(1, n))
    r = [coefficient / factorial(j + 1) for j, coefficient in enumerate(p)]
    transformed = [Fraction(0)] + [n * coefficient for coefficient in r]
    assert direct == transformed, ("factorial multiplier identity", n)
    assert r[0] == 1
    assert r[1] == Fraction(n * (n - 1), 4)

    x = sp.Symbol("x")
    polynomial = sp.Poly(sum(sp.Rational(c.numerator, c.denominator) * x**j
                             for j, c in enumerate(direct)), x, domain=sp.QQ)
    isolated = polynomial.intervals(eps=sp.Rational(1, 10**12))
    brackets = []
    for (lo, hi), multiplicity in isolated:
        assert multiplicity == 1
        brackets.append((as_fraction(lo), as_fraction(hi)))
    assert len(brackets) == n
    assert brackets[-1] == (Fraction(0), Fraction(0))
    assert all(hi < 0 for lo, hi in brackets[:-1])
    ordinary_mesh_lower = min(brackets[j + 1][0] - brackets[j][1]
                              for j in range(n - 1))
    delta = Fraction(2) if n == 2 else Fraction(4, n * (n - 1) * (n - 2))
    assert ordinary_mesh_lower >= delta

    positive = [(-hi, -lo) for lo, hi in reversed(brackets[:-1])]
    smallest_lower = positive[0][0]
    assert smallest_lower >= Fraction(4, n * (n - 1))
    if n > 2:
        logarithmic_mesh_lower = min(positive[j + 1][0] / positive[j][1]
                                      for j in range(n - 2))
        assert logarithmic_mesh_lower >= Fraction(n - 1, n - 2)
    else:
        logarithmic_mesh_lower = None

    harmonic = sum((Fraction(1, j) for j in range(1, n)), Fraction(0))
    threshold_unsquared = 16 + 24 * harmonic / delta
    threshold_real = threshold_unsquared**2
    threshold = ceiling(threshold_real)
    assert threshold - 1 < threshold_real <= threshold
    certified_threshold_real = (16 + 24 * harmonic / ordinary_mesh_lower)**2
    certified_threshold = ceiling(certified_threshold_real)
    assert certified_threshold - 1 < certified_threshold_real <= certified_threshold
    assert certified_threshold <= threshold
    if n >= 3:
        assert threshold <= 36 * n**4 * (n - 1)**2 * (n - 2)**2 <= 36 * n**8

    return {
        "n": n,
        "B_n_coefficients_ascending": list(map(display, direct)),
        "all_B_n_root_brackets": [[display(lo), display(hi)] for lo, hi in brackets],
        "theorem_ordinary_mesh_lower": display(delta),
        "certified_ordinary_mesh_lower": display(ordinary_mesh_lower),
        "theorem_smallest_nonzero_root_lower": display(Fraction(4, n * (n - 1))),
        "certified_smallest_nonzero_root_lower": display(smallest_lower),
        "theorem_logarithmic_mesh_lower": display(Fraction(n - 1, n - 2)) if n > 2 else None,
        "certified_logarithmic_mesh_lower": display(logarithmic_mesh_lower)
        if logarithmic_mesh_lower is not None else None,
        "H_n_minus_1": display(harmonic),
        "threshold_before_ceiling": display(threshold_real),
        "new_sufficient_threshold": threshold,
        "sufficient_threshold_from_certified_mesh": certified_threshold,
        "certified_mesh_threshold_before_ceiling": display(certified_threshold_real),
        "previous_explicit_threshold": 576 * n**2 * (3 * n)**(2 * n - 4),
    }


def verify_finite_multiplier() -> dict:
    count = 0
    for n in (1, 2, 3, 7, 20):
        for r in range(18):
            left = Fraction(1, n**r) * prod(Fraction(j + r, j)
                                            for j in range(2, n + 2))
            right = Fraction(1, factorial(r + 1)) * prod(Fraction(n + h, n)
                                                        for h in range(2, r + 2))
            assert left == right
            count += 1
    return {"exact_finite_multiplier_coefficient_checks": count}


def verify_gamma_moments() -> list[dict]:
    output = []
    for m in (1, 2, 3, 5, 10, 16, 32):
        k = 16 * m**2
        pos = prod(Fraction(k + j, k) for j in range(1, 2 * m + 1))
        neg = prod(Fraction(k, k - j) for j in range(2 * m))
        square_upper = pos + neg - 2
        assert square_upper < Fraction(2, 3)
        output.append({"m": m, "k": k,
                       "exact_Cauchy_square_upper": display(square_upper),
                       "less_than_two_thirds": True})
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=16)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("polynomial_mesh_certificates.json"))
    args = parser.parse_args()
    if args.max_n < 2:
        parser.error("--max-n must be at least 2")
    indices = []
    for n in range(2, args.max_n + 1):
        indices.append(verify_index(n))
        print(f"n={n}: exact polynomial identity, complete root isolation, "
              f"mesh bounds PASS; analytic k={indices[-1]['new_sufficient_threshold']}, "
              f"certified k={indices[-1]['sufficient_threshold_from_certified_mesh']}",
              flush=True)
    payload = {
        "status": "PASS",
        "arithmetic": "exact rational, including all root-bracket acceptance",
        "scope": "finite audits only; the all-index proof is in the article",
        "sympy_version": sp.__version__,
        "finite_multiplier": verify_finite_multiplier(),
        "gamma_moments": verify_gamma_moments(),
        "indices": indices,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
