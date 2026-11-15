#!/usr/bin/env python3
"""Exact certificate and regression checks for the accompanying Apéry proof.

The symbolic polynomial identity is checked for formal variables. Finite
sample checks are diagnostics, not a proof of the universal iPRA theorem.
No floating-point calculation is used for a mathematical assertion.

Requires Python >= 3.10 and SymPy. Run from any working directory.
"""
from __future__ import annotations

from fractions import Fraction as Q
from functools import cache
from math import comb, factorial, gcd
from pathlib import Path
import json
import sys

import sympy as sp


@cache
def harmonic(s: int, n: int) -> Q:
    return sum((Q(1, j ** s) for j in range(1, n + 1)), Q(0))


def coefficient(n: int, k: int) -> int:
    return (-1) ** (n - k) * comb(n, k) * comb(n + k, k)


@cache
def apery_a(n: int) -> int:
    return sum(coefficient(n, k) ** 2 for k in range(n + 1))


@cache
def gamma(n: int, k: int) -> Q:
    return sum((Q(coefficient(n, k) * coefficient(n, l), l - k)
                for l in range(n + 1) if l != k), Q(0))


@cache
def apery_b(n: int) -> Q:
    diagonal = sum((coefficient(n, k) ** 2 * harmonic(3, k)
                    for k in range(n + 1)), Q(0))
    off_diagonal = sum((Q(coefficient(n, k) * coefficient(n, l), l - k)
                        * (harmonic(2, k) - harmonic(2, l))
                        for k in range(n + 1)
                        for l in range(k + 1, n + 1)), Q(0))
    return diagonal + off_diagonal


@cache
def d(n: int) -> int:
    out = 1
    for j in range(1, n + 1):
        out = out // gcd(out, j) * j
    return out


def recurrence_p(n: int) -> int:
    return (2 * n + 1) * (17 * n * n + 17 * n + 5)


def rational_r(n: int, t: int) -> Q:
    value = Q(1, t * t)
    for j in range(1, n + 1):
        value *= Q(t - j, t + j) ** 2
    return value


def derivative_r(n: int, t: int) -> Q:
    if 1 <= t <= n:
        return Q(0)
    logarithmic_factor = (sum((Q(1, t - j) for j in range(1, n + 1)), Q(0))
                          - sum((Q(1, t + j) for j in range(n + 1)), Q(0)))
    return 2 * rational_r(n, t) * logarithmic_factor


def derivative_sum(n: int, tmax: int) -> Q:
    return -sum((derivative_r(n, t) for t in range(1, tmax + 1)), Q(0)) / 2


def finite_boundary(n: int, tmax: int) -> Q:
    return sum((coefficient(n, k) ** 2
                * (harmonic(3, tmax + k) - harmonic(3, tmax))
                + gamma(n, k)
                * (harmonic(2, tmax + k) - harmonic(2, tmax))
                for k in range(n + 1)), Q(0))


def fast_a_values(maximum: int) -> list[int]:
    """Exact recurrence, used only after independent finite-sum comparisons."""
    values = [1, 5]
    for n in range(1, maximum):
        numerator = recurrence_p(n) * values[-1] - n ** 3 * values[-2]
        den = (n + 1) ** 3
        assert numerator % den == 0
        values.append(numerator // den)
    return values[:maximum + 1]


def exact_fraction_text(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"


def main() -> None:
    report: dict[str, object] = {
        "status": "all checks passed",
        "arithmetic": "exact integers, fractions, and symbolic polynomials",
        "scope": "certificate checks and finite regressions; not a Lean or iPRA proof checker",
        "lean_status": "uncompiled specifications and outline; final internal derivation not supplied",
        "python_version": sys.version.split()[0],
        "sympy_version": sp.__version__,
    }

    # A single bivariate polynomial identity, valid symbolically.
    n, t, u = sp.symbols("n t u")
    pn = (2 * n + 1) * (17 * n ** 2 + 17 * n + 5)
    sn = lambda x: 4 * (2 * n + 1) * (-2 * x ** 2 + x + (2 * n + 1) ** 2)
    lhs = ((n + 1) ** 3 * (t - n - 1) ** 2 * (t - n) ** 2
           - pn * (t - n) ** 2 * (t + n + 1) ** 2
           + n ** 3 * (t + n) ** 2 * (t + n + 1) ** 2)
    rhs = sn(t + 1) * t ** 4 - sn(t) * (t - n) ** 2 * (t + n + 1) ** 2
    assert sp.Poly(sp.expand(lhs - rhs), n, t).is_zero
    growth = n ** 3 - 45 * n ** 2 - 69 * n - 27
    assert sp.expand(growth.subs(n, u + 48)) == u ** 3 + 99 * u ** 2 + 2523 * u + 3573
    assert sp.expand(t * (2 * t - 1) - 2 * (t - 1) ** 2) == 3 * t - 2
    report["symbolic_certificates"] = {
        "telescoper_residual": "zero polynomial",
        "growth_shift": "u^3+99u^2+2523u+3573",
        "zeta_tail_numerator_difference": "3t-2",
    }

    small = {
        "3^7<7^4": 3 ** 7 < 7 ** 4,
        "3^10<2^16": 3 ** 10 < 2 ** 16,
        "8^6>2*7^6": 8 ** 6 > 2 * 7 ** 6,
        "768<1023": 768 < 1023,
    }
    constant = 2 ** 22 * 3 ** 15 * 7 ** 7
    small["A^3<28^41"] = constant ** 3 < 28 ** 41
    assert all(small.values())
    report["fixed_comparisons"] = small
    report["multinomial_base_A"] = constant

    # Initial values, arithmetic integrality, and recurrence normalization.
    rows = []
    for k in range(21):
        a, b = apery_a(k), apery_b(k)
        assert a > 0
        assert a >= 4 ** k
        assert (d(k) ** 3 * b).denominator == 1
        assert sum((gamma(k, j) for j in range(k + 1)), Q(0)) == 0
        alternate_b = sum((coefficient(k, j) ** 2 * harmonic(3, j)
                           + gamma(k, j) * harmonic(2, j)
                           for j in range(k + 1)), Q(0))
        assert b == alternate_b
        if k <= 6:
            rows.append({"n": k, "a_n": a, "b_n": exact_fraction_text(b)})
        if k >= 1:
            assert (k + 1) ** 3 * apery_a(k + 1) == recurrence_p(k) * a - k ** 3 * apery_a(k - 1)
            assert (k + 1) ** 3 * apery_b(k + 1) == recurrence_p(k) * b - k ** 3 * apery_b(k - 1)
        assert a * apery_b(k + 1) - apery_a(k + 1) * b == Q(6, (k + 1) ** 3)
    assert rows[0]["a_n"] == 1 and apery_b(0) == 0
    assert rows[1]["a_n"] == 5 and apery_b(1) == 6
    report["initial_values"] = rows
    report["coefficient_recurrence_integrality_checks"] = "n=0,...,20, with successor values as needed"

    # Partial fractions and the exact finite error identity.
    error_count = 0
    for k in range(1, 9):
        for tmax in (k, k + 1, k + 7, 30):
            f = derivative_sum(k, tmax)
            err = finite_boundary(k, tmax)
            assert f == apery_a(k) * harmonic(3, tmax) - apery_b(k) + err
            assert abs(f) <= 3
            assert abs(err) <= Q((k + 1) ** 3 * 64 ** k, tmax ** 2)
            error_count += 1
        for arg in range(1, 20):
            partial = sum((Q(coefficient(k, j) ** 2, (arg + j) ** 2)
                           + 2 * gamma(k, j) / (arg + j)
                           for j in range(k + 1)), Q(0))
            assert rational_r(k, arg) == partial
    report["finite_partial_fraction_error_checks"] = error_count

    for m in range(1, 30):
        for tt in (m, m + 1, m + 20):
            assert 0 <= harmonic(3, tt) - harmonic(3, m) <= Q(1, 2 * m * m)
    report["zeta_tail_checks"] = 29 * 3

    # The lcm step is checked as divisibility, not a floating-point inequality.
    for j in range(2001):
        w = j - j // 2 - j // 3 - j // 7 - j // 42
        assert w >= 0
        if 1 <= j <= 41:
            assert w >= 1
    for m in range(1, 41):
        multi = comb(42 * m, 21 * m) * comb(21 * m, 14 * m) * comb(7 * m, 6 * m)
        assert factorial(42 * m) == multi * factorial(21 * m) * factorial(14 * m) * factorial(6 * m) * factorial(m)
        assert (d(m) * multi) % d(42 * m) == 0
        assert multi <= constant ** m
        factor = 21 ** (21 * m) * 14 ** (14 * m) * 6 ** (6 * m)
        assert 42 ** (42 * m) == constant ** m * factor
    report["floor_checks"] = "j=0,...,2000"
    report["multinomial_divisibility_checks"] = "m=1,...,40"

    for k in range(3):
        nn = 42 ** k
        assert d(nn) ** 3 <= 28 ** nn
    report["sparse_lcm_checks"] = [1, 42, 1764]

    # Independently compare the fast recurrence with the defining sum first.
    vals = fast_a_values(1765)
    for nn in range(61):
        assert vals[nn] == apery_a(nn)
    for nn in range(48, 1765):
        assert vals[nn + 1] >= 32 * vals[nn]
    report["growth_checks"] = "n=48,...,1764"

    # First actual prescribed index, q=1. We do NOT try to sum Z_N.
    nn, q = 1764, 1
    assert 8 * q * d(nn) ** 3 < vals[nn]
    height = (nn + 1) ** 3 * vals[nn + 1]
    cutoff = vals[nn] * height
    assert cutoff >= vals[nn] ** 2
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(100_000)
    report["first_prescribed_index"] = {
        "q": q, "n": nn, "budget_8qD3_lt_a": True,
        "cutoff_bit_length": cutoff.bit_length(),
        "cutoff_decimal_digits": len(str(cutoff)),
        "Z_cutoff_evaluated": False,
    }
    for q in range(1, 101):
        assert 42 ** (q - 1) >= q
        assert 1764 * q >= 6 * (q + 243)
        assert q <= 2 ** q
    report["index_inequality_regressions"] = "q=1,...,100"

    path = Path(__file__).with_name("verification_report.json")
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
