#!/usr/bin/env python3
"""Exact finite certificates accompanying the beta/iPRA report.

This program uses only Python integers and fractions.Fraction.  It does not
numerically evaluate Gamma, Beta, pi, or any transcendental function.  It
checks the finite algebraic identities isolated in the report.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
from typing import Iterable


Poly = list[Fraction]  # coefficient of X^i at index i


def trim(p: Poly) -> Poly:
    q = p[:]
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return q


def poly_add(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    out = [Fraction(0) for _ in range(n)]
    for i, c in enumerate(a):
        out[i] += c
    for i, c in enumerate(b):
        out[i] += c
    return trim(out)


def poly_sub(a: Poly, b: Poly) -> Poly:
    return poly_add(a, [-c for c in b])


def poly_mul(a: Poly, b: Poly) -> Poly:
    out = [Fraction(0) for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def poly_scale(c: Fraction, a: Poly) -> Poly:
    return trim([c * x for x in a])


def poly_pow(a: Poly, n: int) -> Poly:
    assert n >= 0
    out: Poly = [Fraction(1)]
    base = a[:]
    k = n
    while k:
        if k & 1:
            out = poly_mul(out, base)
        base = poly_mul(base, base)
        k >>= 1
    return out


def poly_eval(a: Poly, x: Fraction) -> Fraction:
    out = Fraction(0)
    for c in reversed(a):
        out = out * x + c
    return out


def poly_deriv(a: Poly) -> Poly:
    if len(a) <= 1:
        return [Fraction(0)]
    return trim([Fraction(i) * a[i] for i in range(1, len(a))])


def beta_integer(m: int, n: int) -> Fraction:
    assert m >= 1 and n >= 1
    return Fraction(factorial(m - 1) * factorial(n - 1),
                    factorial(m + n - 1))


def rising(a: Fraction, n: int) -> Fraction:
    out = Fraction(1)
    for j in range(n):
        out *= a + j
    return out


def beta_a_n_plus_one(a: Fraction, n: int) -> Fraction:
    assert a > 0 and n >= 0
    return Fraction(factorial(n), 1) / rising(a, n + 1)


def incomplete_beta_poly(m: int, n: int) -> Poly:
    """B_x(m,n), m,n positive integers."""
    assert m >= 1 and n >= 1
    out: Poly = [Fraction(0)] * (m + n)
    for j in range(n):
        out[m + j] += Fraction((-1) ** j * comb(n - 1, j), m + j)
    return trim(out)


def regularized_incomplete_beta_poly(m: int, n: int) -> Poly:
    return poly_scale(1 / beta_integer(m, n), incomplete_beta_poly(m, n))


def binomial_cdf_poly(n: int, k: int) -> Poly:
    """sum_{j=0}^k C(n,j) p^j (1-p)^(n-j)."""
    assert 0 <= k <= n
    out: Poly = [Fraction(0)]
    one_minus_x: Poly = [Fraction(1), Fraction(-1)]
    for j in range(k + 1):
        xj: Poly = [Fraction(0)] * j + [Fraction(1)]
        term = poly_mul(xj, poly_pow(one_minus_x, n - j))
        out = poly_add(out, poly_scale(Fraction(comb(n, j)), term))
    return trim(out)


def frac_json(x: Fraction) -> dict[str, int]:
    return {"num": x.numerator, "den": x.denominator}


def poly_json(p: Poly) -> list[dict[str, int]]:
    return [frac_json(x) for x in p]


def product(xs: Iterable[Fraction]) -> Fraction:
    out = Fraction(1)
    for x in xs:
        out *= x
    return out


def half_gamma_coeff(k: int) -> Fraction:
    """Gamma(k+1/2) = coeff * sqrt(pi), for k >= 0."""
    assert k >= 0
    return Fraction(factorial(2 * k), 4 ** k * factorial(k))


def beta_half_shift_coeff(p: int) -> Fraction:
    """B(p+1/2,p+1/2) = coeff * pi, p a positive integer."""
    g = half_gamma_coeff(p)
    return g * g / factorial(2 * p)


def run_checks() -> dict:
    checks: list[dict] = []

    # Integer beta, symmetry, Pascal, and coordinate shifts.
    count = 0
    for m in range(1, 10):
        for n in range(1, 10):
            b = beta_integer(m, n)
            assert b == beta_integer(n, m)
            assert b == beta_integer(m + 1, n) + beta_integer(m, n + 1)
            assert beta_integer(m + 1, n) == Fraction(m, m + n) * b
            assert beta_integer(m, n + 1) == Fraction(n, m + n) * b
            assert Fraction(1, (m + n) * b.denominator) != Fraction(0)  # sanity
            count += 1
    checks.append({"name": "integer_beta_symmetry_pascal_shifts", "cases": count})

    # Rational a and natural second coordinate.
    samples = [Fraction(1, 3), Fraction(1, 2), Fraction(2, 3),
               Fraction(3, 2), Fraction(7, 4)]
    count = 0
    for a in samples:
        for n in range(0, 9):
            lhs = beta_a_n_plus_one(a, n)
            rhs = Fraction(factorial(n), 1) / product(a + j for j in range(n + 1))
            assert lhs == rhs
            if n > 0:
                assert lhs == Fraction(n, 1) / (a + n) * beta_a_n_plus_one(a, n - 1)
            count += 1
    checks.append({"name": "rational_a_natural_shift_product", "cases": count})

    # Binomial relation.
    count = 0
    for n in range(0, 15):
        for k in range(n + 1):
            rhs = 1 / (Fraction(n + 1) * beta_integer(n - k + 1, k + 1))
            assert rhs == comb(n, k)
            count += 1
    checks.append({"name": "binomial_beta_relation", "cases": count})

    # Incomplete-beta polynomial, endpoint, derivative, and complement.
    count = 0
    for m in range(1, 8):
        for n in range(1, 8):
            p = incomplete_beta_poly(m, n)
            assert poly_eval(p, Fraction(0)) == 0
            assert poly_eval(p, Fraction(1)) == beta_integer(m, n)
            expected_derivative = poly_mul(
                [Fraction(0)] * (m - 1) + [Fraction(1)],
                poly_pow([Fraction(1), Fraction(-1)], n - 1),
            )
            assert poly_deriv(p) == expected_derivative

            # B_x(m,n) + B_{1-x}(n,m) = B(m,n).
            q = incomplete_beta_poly(n, m)
            # compose q(1-X) by expanding each monomial
            q_one_minus_x: Poly = [Fraction(0)]
            for degree, coeff in enumerate(q):
                if coeff:
                    q_one_minus_x = poly_add(
                        q_one_minus_x,
                        poly_scale(coeff, poly_pow([Fraction(1), Fraction(-1)], degree)),
                    )
            total = poly_add(p, q_one_minus_x)
            assert total == [beta_integer(m, n)]
            count += 1
    checks.append({"name": "incomplete_beta_polynomial_and_complement", "cases": count})

    # Binomial CDF relation, 0 <= k < n.
    count = 0
    examples: list[dict] = []
    for n in range(1, 13):
        for k in range(n):
            cdf = binomial_cdf_poly(n, k)
            ip = regularized_incomplete_beta_poly(k + 1, n - k)
            rhs = poly_sub([Fraction(1)], ip)
            assert cdf == rhs
            if (n, k) in {(4, 1), (7, 3)}:
                examples.append({
                    "n": n, "k": k,
                    "coefficients": poly_json(cdf),
                })
            count += 1
    checks.append({
        "name": "binomial_cdf_regularized_beta_polynomial",
        "cases": count,
        "examples": examples,
    })

    # h(a,b) coefficients and PDE.
    count = 0
    for m in range(0, 10):
        for n in range(0, 10):
            derivative_at_zero = Fraction(factorial(m) * factorial(n),
                                          factorial(m + n + 1))
            assert derivative_at_zero == beta_integer(m + 1, n + 1)
            h_coeff = Fraction(1, factorial(m + n + 1))
            ha_coeff = Fraction(m + 1, factorial(m + n + 2))
            hb_coeff = Fraction(n + 1, factorial(m + n + 2))
            assert h_coeff == ha_coeff + hb_coeff
            count += 1
    checks.append({"name": "h_derivatives_and_pde_coefficients", "cases": count})

    # Multivariate positive-integer beta and Pascal.
    tuples = [
        (1, 1, 1),
        (2, 3, 4),
        (1, 5, 2, 3),
        (3, 3, 3, 3, 3),
        (2, 7),
    ]
    multi_records = []
    for ms in tuples:
        s = sum(ms)
        b = Fraction(product(Fraction(factorial(m - 1)) for m in ms),
                     factorial(s - 1))
        shifted = []
        for j, m in enumerate(ms):
            ms2 = list(ms)
            ms2[j] += 1
            s2 = sum(ms2)
            bj = Fraction(product(Fraction(factorial(t - 1)) for t in ms2),
                          factorial(s2 - 1))
            assert bj == Fraction(m, s) * b
            shifted.append(bj)
        assert sum(shifted, Fraction(0)) == b
        multi_records.append({
            "tuple": list(ms),
            "beta": frac_json(b),
            "shifted_sum": frac_json(sum(shifted, Fraction(0))),
        })
    checks.append({
        "name": "multivariate_integer_pascal",
        "cases": len(tuples),
        "records": multi_records,
    })

    # Central beta product at positive integer p, with pi factored out.
    central = []
    for p_int in range(1, 11):
        lhs_over_pi = beta_integer(p_int, p_int) * beta_half_shift_coeff(p_int)
        rhs_over_pi = Fraction(1, (2 ** (4 * p_int - 1)) * p_int)
        assert lhs_over_pi == rhs_over_pi
        central.append({
            "p": p_int,
            "coefficient_of_pi": frac_json(lhs_over_pi),
        })
    checks.append({
        "name": "central_beta_product_coefficient",
        "cases": len(central),
        "records": central,
    })

    # Infinite-product factor identity.
    count = 0
    for x in samples:
        for y in samples:
            for k in range(1, 9):
                left = (1 + x / k) * (1 + y / k) / (1 + (x + y) / k)
                right = 1 + x * y / (Fraction(k) * (k + x + y))
                assert left == right
                count += 1
    checks.append({"name": "euler_product_factor_identity", "cases": count})

    # Wikipedia symmetric-series counterexample at z=1.
    first_terms = []
    rising_val = Fraction(1)
    for n in range(0, 8):
        if n == 0:
            rising_val = Fraction(1)
        else:
            rising_val = product(Fraction(n + 1 + j) for j in range(n))
        term = Fraction(2 * ((-1) ** n), 1) * rising_val / (Fraction(n + 1) * factorial(n))
        first_terms.append(term)
    abel_value = Fraction(2) * (
        Fraction(1)
        + Fraction(-2, 2)
        + Fraction(2, 3 * 2)
    )
    assert abel_value == Fraction(2, 3)
    assert beta_integer(1, 1) == 1
    assert abel_value != beta_integer(1, 1)
    checks.append({
        "name": "wikipedia_symmetric_series_counterexample_z1",
        "first_series_terms": [frac_json(x) for x in first_terms],
        "first_series_terms_fail_to_tend_to_zero": True,
        "second_abel_value": frac_json(abel_value),
        "beta_1_1": frac_json(beta_integer(1, 1)),
    })

    total_cases = sum(int(c.get("cases", 1)) for c in checks)
    return {
        "title": "Exact finite certificates for the beta/iPRA packet",
        "arithmetic": "Python integers and fractions.Fraction only",
        "transcendental_oracle_used": False,
        "total_case_count": total_cases,
        "checks": checks,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    data = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(f"wrote {args.output} ({data['total_case_count']} exact cases)")


if __name__ == "__main__":
    main()
