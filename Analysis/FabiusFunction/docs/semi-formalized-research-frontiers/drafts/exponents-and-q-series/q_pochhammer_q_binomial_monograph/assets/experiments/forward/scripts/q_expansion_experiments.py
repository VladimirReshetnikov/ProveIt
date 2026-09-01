#!/usr/bin/env python3
"""Numerical and symbolic checks for q_analog_expansions_report.tex.

The program deliberately avoids specialized q-series packages.  It implements
finite Gaussian polynomials by Pascal recursion and infinite products by direct
high-precision summation of logarithms.  This keeps every numerical check close
to the formulas proved in the report.

Dependencies
------------
    Python 3.10+
    mpmath
    sympy

Run
---
    python q_expansion_experiments.py

The script prints:
  * the first coefficients of finite/infinite q-Pochhammer products at q=0;
  * symbolic q=1 cumulant polynomials for Gaussian coefficients;
  * exact checks of the Taylor jet through order four at q=1;
  * exact checks of the value and first derivative at q=-1;
  * numerical remainder tests for the q^x-Pochhammer and q-gamma expansions;
  * a radial root-of-unity expansion using a cyclic quantum dilogarithm;
  * the double-scaling expansion [N choose alpha N]_{exp(-tau/N)}.

All asymptotic comparisons use more digits than are displayed.  The purpose is
verification and reproducibility, not high-performance evaluation.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Sequence

import mpmath as mp
import sympy as sp

mp.mp.dps = 80


def gaussian_coefficients(n: int, k: int) -> list[int]:
    """Return coefficients of the Gaussian polynomial [n choose k]_q.

    The recurrence used is
        [r choose s]_q = [r-1 choose s]_q + q^(r-s)[r-1 choose s-1]_q.
    Coefficients are exact Python integers.
    """
    if not (0 <= k <= n):
        return [0]
    k = min(k, n - k)
    rows: list[list[int]] = [[1]] + [[0] for _ in range(k)]
    for r in range(1, n + 1):
        for s in range(min(r, k), 0, -1):
            shift = r - s
            left = rows[s]
            right = [0] * shift + rows[s - 1]
            size = max(len(left), len(right))
            left = left + [0] * (size - len(left))
            right = right + [0] * (size - len(right))
            rows[s] = [left[i] + right[i] for i in range(size)]
    return rows[k]


def eval_poly(coeffs: Sequence[int | mp.mpf | mp.mpc], q: mp.mpf | mp.mpc):
    """Evaluate coefficients in ascending order by Horner's rule."""
    value = mp.mpc(0)
    for coefficient in reversed(coeffs):
        value = value * q + coefficient
    return value


def derivative_at_minus_one(coeffs: Sequence[int]) -> int:
    """Evaluate the exact derivative P'(-1) for an integer polynomial."""
    return sum(j * coefficient * ((-1) ** (j - 1)) for j, coefficient in enumerate(coeffs) if j)


def qpoch_finite(a, q, n: int):
    product = mp.mpc(1)
    qj = mp.mpc(1)
    for _ in range(n):
        product *= 1 - a * qj
        qj *= q
    return product


def log_qpoch_infinite(a, q, tolerance=mp.mpf("1e-72")):
    """Compute log (a;q)_infinity using the branch reached term by term.

    This is reliable in the tests below because |a|<1 and |q|<1, so every
    factor remains away from the logarithmic branch cut used by mpmath.
    """
    total = mp.mpc(0)
    qj = mp.mpc(1)
    for _ in range(1_000_000):
        total += mp.log(1 - a * qj)
        qj *= q
        if abs(a * qj) < tolerance:
            return total
    raise RuntimeError("infinite product did not converge at the requested tolerance")


def bernoulli_polynomial(degree: int, x):
    """Evaluate the Bernoulli polynomial B_degree(x) with B_1(x)=x-1/2."""
    symbol = sp.Symbol("x")
    expression = sp.bernoulli(degree, symbol)
    return mp.mpf(str(sp.N(expression.subs(symbol, sp.Float(str(x), 90)), 85)))


def qx_pochhammer_log_asymptotic(x, t, even_order: int):
    r"""Expansion of log (exp(-x t); exp(-t))_infinity.

    even_order is the largest even power t^(2r) retained.  The exceptional
    linear term B_2(x)t/4 is always included.
    """
    x = mp.mpf(x)
    t = mp.mpf(t)
    value = (
        -mp.pi**2 / (6 * t)
        + (mp.mpf("0.5") - x) * mp.log(t)
        + mp.log(2 * mp.pi) / 2
        - mp.log(mp.gamma(x))
        + bernoulli_polynomial(2, x) * t / 4
    )
    for r in range(1, even_order // 2 + 1):
        b = mp.mpf(str(sp.bernoulli(2 * r)))
        value -= (
            b
            * bernoulli_polynomial(2 * r + 1, x)
            * t ** (2 * r)
            / (2 * r * mp.factorial(2 * r + 1))
        )
    return value


def qgamma_log_exact(x, t):
    q = mp.e ** (-t)
    return (1 - x) * mp.log(1 - q) + log_qpoch_infinite(q, q) - log_qpoch_infinite(q**x, q)


def qgamma_log_asymptotic(x, t, even_order: int):
    """Expansion of log Gamma_q(x), q=exp(-t), through t^even_order."""
    x = mp.mpf(x)
    t = mp.mpf(t)
    value = mp.log(mp.gamma(x)) + (x - 1) * (2 - x) * t / 4
    for r in range(1, even_order // 2 + 1):
        b = mp.mpf(str(sp.bernoulli(2 * r)))
        bracket = 1 - x + bernoulli_polynomial(2 * r + 1, x) / (2 * r + 1)
        value += b * bracket * t ** (2 * r) / (2 * r * mp.factorial(2 * r))
    return value


def eulerian_rational(u, j: int):
    r"""Return E_j(u)=(u d/du)^j(1/(1-u))."""
    if j == 0:
        return 1 / (1 - u)
    # For j>=1 this rational function is Li_{-j}(u), including by analytic
    # continuation at roots of unity u != 1.
    return mp.polylog(-j, u)


def cyclic_dilogarithm(a, zeta, m: int):
    r"""D_zeta(a)=product_{s=1}^{m-1}(1-zeta^s a)^s."""
    total = mp.mpc(1)
    for s in range(1, m):
        total *= (1 - zeta**s * a) ** s
    return total


def root_of_unity_coefficient(a, m: int, j: int, cutoff: int = 500):
    r"""Coefficient C_j in the radial expansion at a primitive m-th root.

    q = zeta*exp(-t), |a|<1, and
      log(a;q)_infinity = -Li_2(a^m)/(m^2 t) + C_0 + sum C_j t^j.

    The exponentially convergent sum is truncated at ``cutoff``.  For the
    numerical examples a=0.2, so 500 is far beyond what is needed.
    """
    zeta = mp.e ** (2j * mp.pi / m)
    nonresonant = mp.mpc(0)
    for r in range(1, cutoff + 1):
        if r % m:
            nonresonant += a**r * r ** (j - 1) * eulerian_rational(zeta**r, j)
    nonresonant *= (-1) ** (j + 1) / mp.factorial(j)

    b = mp.mpf(str(sp.bernoulli(j + 1)))
    resonant = -b * m ** (j - 1) * mp.polylog(1 - j, a**m) / mp.factorial(j + 1)
    return nonresonant + resonant


def root_of_unity_log_asymptotic(a, m: int, t, order: int):
    zeta = mp.e ** (2j * mp.pi / m)
    constant = mp.log(1 - a**m) / 2 - mp.log(cyclic_dilogarithm(a, zeta, m)) / m
    value = -mp.polylog(2, a**m) / (m * m * t) + constant
    for j in range(1, order + 1):
        value += root_of_unity_coefficient(a, m, j) * t**j
    return value


def log_qbinomial_exact(n: int, k: int, q):
    """Stable logarithm for 0<q<1."""
    k = min(k, n - k)
    return mp.fsum(mp.log1p(-(q**j)) for j in range(n - k + 1, n + 1)) - mp.fsum(
        mp.log1p(-(q**j)) for j in range(1, k + 1)
    )


def double_scaling_log_qbinomial(n: int, alpha, tau, max_r: int = 2):
    r"""All-order odd-power double-scaling approximation.

    q=exp(-tau/n), k=alpha*n.  max_r=1 keeps 1/n; max_r=2 also keeps 1/n^3,
    etc.  The formula assumes alpha*n is integral.
    """
    alpha = mp.mpf(alpha)
    tau = mp.mpf(tau)

    def phi(beta):
        return mp.polylog(2, mp.e ** (-beta * tau))

    action = (phi(1) - phi(alpha) - phi(1 - alpha) + mp.pi**2 / 6) / tau
    constant = -mp.log(2 * mp.pi * n / tau) / 2 + mp.log(
        (1 - mp.e ** (-tau))
        / ((1 - mp.e ** (-alpha * tau)) * (1 - mp.e ** (-(1 - alpha) * tau)))
    ) / 2
    value = n * action + constant

    def c1(beta):
        return tau * mp.coth(beta * tau / 2) / 24

    value += (c1(1) - c1(alpha) - c1(1 - alpha)) / n
    for r in range(2, max_r + 1):
        b = mp.mpf(str(sp.bernoulli(2 * r)))

        def coefficient(beta):
            return b * tau ** (2 * r - 1) * mp.polylog(
                2 - 2 * r, mp.e ** (-beta * tau)
            ) / mp.factorial(2 * r)

        value += (coefficient(1) - coefficient(alpha) - coefficient(1 - alpha)) / n ** (
            2 * r - 1
        )
    return value


def zero_expansion_coefficients(a_symbol, degree: int) -> list[sp.Expr]:
    """Coefficients of product_{j>=1}(1-a q^j) through q^degree."""
    q = sp.Symbol("q")
    product = sp.Integer(1)
    for j in range(1, degree + 1):
        product = sp.series(product * (1 - a_symbol * q**j), q, 0, degree + 1).removeO()
    return [sp.factor(sp.expand(product).coeff(q, r)) for r in range(degree + 1)]


def print_symbolic_data() -> None:
    n, k, j = sp.symbols("n k j", integer=True, nonnegative=True)
    d = sp.Symbol("D")
    power_sum = lambda p, upper: sp.summation(j**p, (j, 1, upper))

    print("\nSYMBOLIC COEFFICIENT DATA")
    print("-------------------------")
    for p in (2, 4, 6):
        delta = sp.expand(power_sum(p, n) - power_sum(p, k) - power_sum(p, n - k))
        reduced = sp.factor(sp.rem(delta, k**2 - n * k + d, k))
        print(f"Delta_{p} = {reduced}")

    h = sp.Symbol("h")
    t = -sp.log(1 + h)
    delta_4 = d * (n + 1) * (n * (n + 1) - d)
    log_normalized = -d * t / 2 + d * (n + 1) * t**2 / 24 - delta_4 * t**4 / 2880
    h_series = sp.exp(log_normalized).series(h, 0, 5).removeO().expand()
    print("\n[n choose k]_(1+h) / binomial(n,k) through h^4:")
    for degree in range(5):
        print(f"  [h^{degree}] = {sp.factor(h_series.coeff(h, degree))}")

    a = sp.Symbol("a")
    coefficients = zero_expansion_coefficients(a, 8)
    print("\nproduct_{j>=1}(1-a q^j) through q^8:")
    for degree, coefficient in enumerate(coefficients):
        print(f"  [q^{degree}] = {coefficient}")



def check_q_one_four_jet() -> None:
    """Check the normalized Taylor coefficients at q=1 through (q-1)^4.

    If P(q)=sum_j c_j q^j, then the coefficient of h^r in P(1+h) is
        sum_j c_j * binomial(j, r).
    This makes the check exact over the rational numbers and independent of
    symbolic series expansion in SymPy.
    """
    print("\nEXACT q=1 FOUR-JET CHECKS")
    print("-------------------------")
    failures = []
    for n in range(1, 21):
        for k in range(n + 1):
            coefficients = gaussian_coefficients(n, k)
            denominator = comb(n, k)
            d = k * (n - k)
            expected = [
                Fraction(1),
                Fraction(d, 2),
                Fraction(d * (3 * d + n - 5), 24),
                Fraction(d * (d - 2) * (d + n - 3), 48),
                Fraction(
                    d
                    * (
                        15 * d**3
                        + 30 * d**2 * n
                        - 150 * d**2
                        + 5 * d * n**2
                        - 168 * d * n
                        + 487 * d
                        - 2 * n**3
                        - 4 * n**2
                        + 218 * n
                        - 500
                    ),
                    5760,
                ),
            ]
            actual = []
            for r in range(5):
                numerator = sum(
                    coefficient * comb(j, r)
                    for j, coefficient in enumerate(coefficients)
                    if j >= r
                )
                actual.append(Fraction(numerator, denominator))
            if actual != expected:
                failures.append((n, k, actual, expected))
    if failures:
        raise AssertionError(f"q=1 four-jet failures: {failures[:3]}")
    print("All 230 pairs 0 <= k <= n <= 20 satisfy the Taylor formula through order four.")

def check_minus_one_jet() -> None:
    print("\nEXACT q=-1 CHECKS")
    print("-----------------")
    failures = []
    for n in range(1, 21):
        for k in range(n + 1):
            coefficients = gaussian_coefficients(n, k)
            value = int(eval_poly(coefficients, mp.mpf(-1)).real)
            derivative = derivative_at_minus_one(coefficients)
            a, eps = divmod(n, 2)
            b, delta = divmod(k, 2)
            if eps == 0 and delta == 1:
                expected_value = 0
                expected_derivative = (a - b) * comb(a, b)
            else:
                expected_value = comb(a, b)
                expected_derivative = -(k * (n - k) // 2) * expected_value
            if value != expected_value or derivative != expected_derivative:
                failures.append((n, k, value, derivative, expected_value, expected_derivative))
    if failures:
        raise AssertionError(f"q=-1 jet failures: {failures[:3]}")
    print("All 230 pairs 0 <= k <= n <= 20 satisfy the stated value/derivative formulas.")


def numerical_tests() -> None:
    print("\nNUMERICAL ASYMPTOTIC TESTS")
    print("--------------------------")

    x = mp.mpf("2.5")
    t = mp.mpf("0.1")
    exact = log_qpoch_infinite(mp.e ** (-x * t), mp.e ** (-t))
    approximation = qx_pochhammer_log_asymptotic(x, t, even_order=6)
    print("q^x-Pochhammer, x=2.5, t=0.1, through t^6")
    print("  absolute error =", mp.nstr(abs(exact - approximation), 18))

    x = mp.mpf("3.7")
    t = mp.mpf("0.08")
    exact = qgamma_log_exact(x, t)
    approximation = qgamma_log_asymptotic(x, t, even_order=6)
    print("q-gamma, x=3.7, t=0.08, through t^6")
    print("  absolute error =", mp.nstr(abs(exact - approximation), 18))

    a = mp.mpf("0.2")
    m = 3
    t = mp.mpf("0.05")
    zeta = mp.e ** (2j * mp.pi / m)
    exact = log_qpoch_infinite(a, zeta * mp.e ** (-t))
    approximation = root_of_unity_log_asymptotic(a, m, t, order=6)
    print("root of unity, m=3, a=0.2, t=0.05, through t^6")
    print("  absolute error =", mp.nstr(abs(exact - approximation), 18))

    n = 100
    alpha = mp.mpf("0.4")
    tau = mp.mpf("1.7")
    q = mp.e ** (-tau / n)
    exact = log_qbinomial_exact(n, int(alpha * n), q)
    approximation_1 = double_scaling_log_qbinomial(n, alpha, tau, max_r=1)
    approximation_3 = double_scaling_log_qbinomial(n, alpha, tau, max_r=2)
    print("double scaling, N=100, alpha=0.4, tau=1.7")
    print("  error through 1/N   =", mp.nstr(exact - approximation_1, 18))
    print("  error through 1/N^3 =", mp.nstr(exact - approximation_3, 18))


def main() -> None:
    print_symbolic_data()
    check_q_one_four_jet()
    check_minus_one_jet()
    numerical_tests()


if __name__ == "__main__":
    main()
