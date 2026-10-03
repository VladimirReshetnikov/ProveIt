#!/usr/bin/env python3
"""Derive and assert the four principal-neighborhood coefficients exactly.

This script implements the cumulant/Hermite calculation in Sections 2 and 5.
The second-neighborhood coefficient -18*(-1)^(n+k) is derived analytically in
Section 5.2, not inferred by this principal-neighborhood calculation.
SymPy uses rational arithmetic; no fitted numerical coefficients are used.
"""
from __future__ import annotations

from itertools import product
from pathlib import Path
import sympy as sp


def main() -> None:
    j, k, n, u, d, h, h2 = sp.symbols("j k n u d h h2")
    order = 10
    moments = [sp.Integer(1)] + [
        sp.factor(sp.summation((2 * k - 1) ** r, (k, 1, j)) / (j + 1))
        for r in range(1, order + 1)
    ]
    cumulants = [sp.Integer(0)]
    for r in range(1, order + 1):
        cumulants.append(sp.factor(moments[r] - sum(
            sp.binomial(r - 1, ell - 1) * cumulants[ell] * moments[r - ell]
            for ell in range(1, r)
        )))

    lines = ["Exact symbolic derivation of the principal-neighborhood coefficients."]
    kappa = {}
    for r in (3, 4, 6, 8, 10):
        numerator, denominator = sp.cancel(cumulants[r]).as_numer_denom()
        polynomial_part = sp.div(numerator, denominator, j)[0]
        kappa[r] = sp.expand(sp.summation(polynomial_part, (j, 1, n)))
        lines.append(f"Polynomial portion of kappa_{r}: {kappa[r]}")
    variance = (n ** 3 / sp.Integer(9) + n ** 2 / sp.Integer(2)
                - 29 * n / sp.Integer(18) + 3 * h - h2 - 2)

    def truncate(expression: sp.Expr) -> sp.Expr:
        return sp.series(expression, u, 0, 5).removeO().expand()

    # Each even cumulant kappa_(2r) has weight r-1. Terms with total
    # weight <=4 suffice through n^-4. Retain d^0 and d^2 in the Hermite
    # polynomials; all discarded d powers contribute later for bounded d.
    even_orders = (4, 6, 8, 10)
    terms = sp.Integer(1)
    for exponents in product(range(5), range(3), range(2), range(2)):
        if not any(exponents):
            continue
        if sum(e * (r // 2 - 1) for e, r in zip(exponents, even_orders)) > 4:
            continue
        degree = sum(e * r for e, r in zip(exponents, even_orders))
        coefficient = sp.prod(
            kappa[r] ** e / (sp.factorial(r) ** e * sp.factorial(e))
            for e, r in zip(exponents, even_orders)
        )
        hermite = (sp.Integer((-1) ** (degree // 2))
                   * sp.factorial2(degree - 1) / variance ** (degree // 2))
        hermite += ((-1) ** (degree // 2 - 1) * sp.factorial(degree) * d ** 2
                    / (sp.factorial(degree // 2 - 1) * 2 ** (degree // 2 - 1)
                       * 2 * variance ** (degree // 2 + 1)))
        terms += truncate((coefficient * hermite).subs(n, 1 / u))
    terms += truncate((-kappa[3] * d / (2 * variance ** 2)).subs(n, 1 / u))

    factorial_factor = (1 + u) * sp.exp(u / 12 - u ** 3 / 360)
    variance_factor = (1 + sp.Rational(9, 2) * u - sp.Rational(29, 2) * u ** 2
                       + (27 * h - 9 * h2 - 18) * u ** 3) ** (-sp.Rational(1, 2))
    gaussian = sp.exp(-d ** 2 / (2 * variance)).subs(n, 1 / u)
    answer = truncate(truncate(factorial_factor) * truncate(variance_factor))
    answer = truncate(answer * truncate(gaussian))
    answer = truncate(answer * truncate(terms))

    expected = {
        1: -sp.Rational(431, 300),
        2: sp.Rational(23085971, 1764000),
        3: (-sp.Rational(9, 2) * d ** 2 - sp.Rational(27, 2) * h
            + sp.Rational(9, 2) * h2 - sp.Rational(107751433393, 1587600000)),
        4: (sp.Rational(1263, 40) * d ** 2 - sp.Rational(81, 2) * d
            + sp.Rational(3789, 40) * h - sp.Rational(1263, 40) * h2
            + sp.Rational(155775441709528423, 322727328000000)),
    }
    for r in range(1, 5):
        coefficient = sp.factor(answer.coeff(u, r))
        assert sp.expand(coefficient - expected[r]) == 0, f"Order-{r} mismatch"
        lines.append(f"PASS: coefficient of n^-{r} = {coefficient}")
    logarithm = truncate(sp.log(answer))
    assert sp.expand(logarithm.coeff(u, 2) - sp.Rational(5907087, 490000)) == 0
    third_log = (-sp.Rational(9, 2) * d ** 2 - sp.Rational(27, 2) * h
                 + sp.Rational(9, 2) * h2 - sp.Rational(197099473, 3937500))
    assert sp.expand(logarithm.coeff(u, 3) - third_log) == 0
    lines.append("PASS: second and third logarithmic coefficients.")
    lines.append("No asymptotic remainder or publication-priority claim is checked by this script.")
    result = "\n".join(lines) + "\n"
    output = Path(__file__).resolve().parent / "symbolic_output.txt"
    output.write_text(result, encoding="utf-8")
    print(result, end="")


if __name__ == "__main__":
    main()
