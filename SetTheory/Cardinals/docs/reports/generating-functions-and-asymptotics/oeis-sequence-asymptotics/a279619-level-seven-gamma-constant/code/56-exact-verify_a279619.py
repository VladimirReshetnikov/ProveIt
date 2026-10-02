#!/usr/bin/env python3
"""Reproduce the exact and numerical checks for the A279619 report.

Requirements:
    python >= 3.10
    mpmath
    sympy

No network access is used.  The recurrence is evaluated with exact Python
integers; all asymptotic coefficients are derived with exact SymPy rationals.
"""
from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from typing import Sequence

import mpmath as mp
import sympy as sp


@dataclass(frozen=True)
class Constants:
    gamma_product: mp.mpf
    c_constant: mp.mpf
    f_critical: mp.mpf
    f_subcritical: mp.mpf
    t_constant: mp.mpf
    singular_amplitude: mp.mpf


def generate_c(max_n: int) -> list[int]:
    """Generate c_0,...,c_max_n exactly from the defining recurrence."""
    if max_n < 0:
        raise ValueError("max_n must be nonnegative")
    c = [0] * (max_n + 1)
    c[0] = 1
    if max_n >= 1:
        c[1] = 2
    for n in range(1, max_n):
        numerator = (
            (26 * n * n + 13 * n + 2) * c[n]
            + 3 * (3 * n - 1) * (3 * n - 2) * c[n - 1]
        )
        denominator = (n + 1) ** 2
        quotient, remainder = divmod(numerator, denominator)
        if remainder:
            raise ArithmeticError(
                f"integrality check failed at n={n}: remainder={remainder}"
            )
        c[n + 1] = quotient
    return c


def constants(dps: int) -> Constants:
    mp.mp.dps = dps
    g = mp.gamma(mp.mpf(1) / 7) * mp.gamma(mp.mpf(2) / 7) * mp.gamma(mp.mpf(4) / 7)
    c_const = mp.sqrt(3 * mp.pi) / g
    f_critical = 3 * g / (8 * mp.pi**2)
    f_subcritical = 5 * g / (16 * mp.pi**2)
    t_const = 3 * mp.sqrt(3) / (4 * mp.pi ** mp.mpf("1.5"))
    singular_amplitude = -2 * mp.pi * mp.sqrt(3) / g
    return Constants(g, c_const, f_critical, f_subcritical, t_const, singular_amplitude)


def derive_alpha(count: int) -> list[sp.Rational]:
    """Derive alpha_0,...,alpha_{count-1} from the formal recurrence."""
    if count < 1:
        return []
    t = sp.symbols("t")
    beta = sp.Rational(-3, 2)
    # Two extra symbols/orders make the triangular solve robust.
    a = sp.symbols(f"a0:{count + 2}")
    series_a = sum(a[j] * t**j for j in range(count + 2))
    identity = (
        27 * (1 + t) ** (beta + 2) * series_a.subs(t, t / (1 + t))
        - (26 + 13 * t + 2 * t**2) * series_a
        - (1 - t + sp.Rational(2, 9) * t**2)
        * (1 - t) ** beta
        * series_a.subs(t, t / (1 - t))
    )
    expanded = sp.series(identity, t, 0, count + 4).removeO().expand()
    solved: dict[sp.Symbol, sp.Expr] = {a[0]: sp.Integer(1)}
    for power in range(2, count + 1):
        target = a[power - 1]
        equation = sp.simplify(expanded.coeff(t, power).subs(solved))
        roots = sp.solve(sp.Eq(equation, 0), target)
        if len(roots) != 1:
            raise ArithmeticError(f"unexpected solve result for alpha_{power-1}: {roots}")
        solved[target] = sp.factor(roots[0])
    return [sp.Rational(solved[a[j]]) for j in range(count)]


def derive_b(count: int) -> list[sp.Rational]:
    """Derive b_0,...,b_{count-1} from the singular Frobenius recurrence."""
    if count < 1:
        return []
    values = [sp.Rational(0)] * count
    values[0] = sp.Rational(1)
    b_minus_one = sp.Rational(0)
    for m in range(0, count - 1):
        previous = b_minus_one if m == 0 else values[m - 1]
        numerator = (
            (1044 * m * m + 1548 * m + 593) * values[m]
            - (36 * m * m - 1) * previous
        )
        denominator = 504 * (m + 1) * (2 * m + 3)
        values[m + 1] = sp.factor(numerator / denominator)
    return values


def mp_rational(q: sp.Rational) -> mp.mpf:
    return mp.mpf(int(q.p)) / int(q.q)


def scaled_q(cn: int, n: int) -> mp.mpf:
    return mp.mpf(cn) * mp.mpf(n) ** mp.mpf("1.5") / mp.mpf(27) ** n


def partial_sum(c: Sequence[int], x: mp.mpf, n: int) -> mp.mpf:
    total = mp.mpf(0)
    power = mp.mpf(1)
    for k in range(n + 1):
        if k:
            power *= x
        total += mp.mpf(c[k]) * power
    return total


def corrected_constant(constants_: Constants, alpha: Sequence[sp.Rational], n: int, order: int) -> mp.mpf:
    factor = mp.mpf(0)
    for j in range(order + 1):
        factor += mp_rational(alpha[j]) / mp.mpf(n) ** j
    return constants_.c_constant * factor


def run(max_n: int, dps: int, alpha_count: int, b_count: int) -> None:
    if max_n < 10:
        raise ValueError("max_n must be at least 10 for the standard checks")
    sys.set_int_max_str_digits(max(10000, max_n * 8))
    mp.mp.dps = dps

    c = generate_c(max_n)
    const = constants(dps)
    alpha = derive_alpha(alpha_count)
    b = derive_b(b_count)

    expected_initial = [
        1,
        2,
        22,
        336,
        6006,
        117348,
        2428272,
        52303680,
        1160427510,
        26337699740,
        608642155660,
        14272471122560,
    ]
    assert c[: len(expected_initial)] == expected_initial

    # Exact consistency of the four central constants.
    assert mp.almosteq(-const.singular_amplitude / (2 * mp.sqrt(mp.pi)), const.c_constant)
    assert mp.almosteq(
        -const.f_critical * const.singular_amplitude / mp.sqrt(mp.pi),
        const.t_constant,
    )
    assert mp.almosteq(mp.mpf(5) / 6 * const.f_critical, const.f_subcritical)

    print("A279619 exact verification")
    print("=" * 72)
    print(f"generated exact terms: c_0 through c_{max_n}")
    print("initial terms:", c[:12])
    print()
    print("gamma product G7 =")
    print(mp.nstr(const.gamma_product, dps))
    print("C_c = sqrt(3*pi)/G7 =")
    print(mp.nstr(const.c_constant, dps))
    print("F(1/27) = 3*G7/(8*pi^2) =")
    print(mp.nstr(const.f_critical, dps))
    print("F(1/125) = 5*G7/(16*pi^2) =")
    print(mp.nstr(const.f_subcritical, dps))
    print("B_0 = -2*pi*sqrt(3)/G7 =")
    print(mp.nstr(const.singular_amplitude, dps))
    print("C_t = 3*sqrt(3)/(4*pi^(3/2)) =")
    print(mp.nstr(const.t_constant, dps))
    print()

    print("alpha coefficients")
    for j, value in enumerate(alpha):
        print(f"alpha_{j} = {value}")
    print()
    print("singular Frobenius coefficients b_j")
    for j, value in enumerate(b):
        print(f"b_{j} = {value}")
    print()

    sample_n = [10, 20, 50, 100, 200, 500, 1000, 2000, max_n]
    sample_n = sorted(set(n for n in sample_n if n <= max_n))
    print("scaled convergence")
    print("n | Q_n | Q_n/C-1 | residual after alpha_3, divided by C")
    for n in sample_n:
        qn = scaled_q(c[n], n)
        lead_error = qn / const.c_constant - 1
        approx3 = corrected_constant(const, alpha, n, min(3, len(alpha) - 1))
        residual3 = (qn - approx3) / const.c_constant
        print(
            f"{n:6d} | {mp.nstr(qn, 22):>24} | "
            f"{mp.nstr(lead_error, 12):>15} | {mp.nstr(residual3, 12):>15}"
        )
    print()

    print("critical tail")
    print("N | exact remainder | remainder/(2*C/sqrt(N+1))")
    for n in [10, 50, 100, 500, 1000, max_n]:
        if n > max_n:
            continue
        remainder = const.f_critical - partial_sum(c, mp.mpf(1) / 27, n)
        leading_tail = 2 * const.c_constant / mp.sqrt(n + 1)
        print(
            f"{n:6d} | {mp.nstr(remainder, 18):>20} | "
            f"{mp.nstr(remainder / leading_tail, 14):>16}"
        )
    print()

    # Fast special-value check.  At x=1/125, N=50 is normally enough for
    # far more than 30 decimal places, but we use the available range.
    fast_n = min(max_n, 50)
    fast_sum = partial_sum(c, mp.mpf(1) / 125, fast_n)
    print(f"F(1/125) partial sum through n={fast_n}:")
    print(mp.nstr(fast_sum, dps))
    print("absolute error:")
    print(mp.nstr(abs(const.f_subcritical - fast_sum), dps))
    print()
    print("all checks passed")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=5000)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument("--alpha-count", type=int, default=11)
    parser.add_argument("--b-count", type=int, default=8)
    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()
    run(args.max_n, args.dps, args.alpha_count, args.b_count)
