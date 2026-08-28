#!/usr/bin/env python3
"""Numerical experiments for the Fabius--Rvachev integral-transform report.

The script deliberately uses only reproducible deterministic calculations except
for one optional Monte-Carlo sanity check (disabled by default).  It verifies:

* the rational moment recurrence for X = sum_{j>=1} 2^{-j} U_j;
* a grid fixed point for the Fabius distribution function F;
* the order-statistic spacing identity for mixed powers F^p(1-F)^q;
* the Cauchy-transform functional-differential equation for the up-law;
* the sinc-product energy representation of int_0^1 F(x)^2 dx;
* concentration of the balanced beta-normalized mixed integral.

The normalization used throughout is
    hat f(xi) = integral f(x) exp(-2*pi*i*x*xi) dx,
and sinc(t) means sin(t)/t.  NumPy's np.sinc(y) is sin(pi*y)/(pi*y),
so Phi(xi) = product_{j>=0} np.sinc(xi/2^j).

The grid solver is not a replacement for exact dyadic arithmetic.  It is a
compact independent check of formulas in the report.  All printed accuracy
claims are therefore conservative.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable

import numpy as np
from scipy.integrate import quad
from scipy.special import betaln, comb


@dataclass(frozen=True)
class FabiusGrid:
    """Uniform-grid approximation of the bounded Fabius CDF on [0, 1]."""

    x: np.ndarray
    f: np.ndarray

    def F(self, x: np.ndarray | float) -> np.ndarray | float:
        """Linearly interpolate F; clamp outside [0,1] to the CDF values."""
        return np.interp(x, self.x, self.f, left=0.0, right=1.0)

    def G(self, u: np.ndarray | float) -> np.ndarray | float:
        """Linearly interpolate the inverse CDF G=F^{-1}."""
        return np.interp(u, self.f, self.x, left=0.0, right=1.0)


def build_fabius_grid(power: int = 17, iterations: int = 36) -> FabiusGrid:
    """Solve F(x)=int_0^{2x}F(t)dt on [0,1/2], then reflect.

    On a grid with 2**power subintervals, doubling a left-half grid point lands
    exactly on another grid point.  A trapezoidal cumulative integral therefore
    makes each fixed-point step inexpensive and deterministic.
    """

    n = 1 << power
    x = np.linspace(0.0, 1.0, n + 1)
    f = x.copy()  # symmetric monotone seed
    half = n // 2
    dx = 1.0 / n

    for _ in range(iterations):
        cumulative = np.empty_like(f)
        cumulative[0] = 0.0
        cumulative[1:] = np.cumsum((f[:-1] + f[1:]) * (0.5 * dx))

        new = np.empty_like(f)
        left_indices = np.arange(half + 1)
        new[: half + 1] = cumulative[2 * left_indices]
        # Enforce exact endpoint/symmetry constraints, including F(1/2)=1/2.
        new[0] = 0.0
        new[half] = 0.5
        new[half + 1 :] = 1.0 - new[half - 1 :: -1]
        new[-1] = 1.0
        f = new

    # Monotonicity is theoretically exact; remove tiny floating reversals before
    # using the array as the abscissa of inverse interpolation.
    f = np.maximum.accumulate(f)
    return FabiusGrid(x=x, f=f)


def rational_moments(max_n: int) -> list[Fraction]:
    """Return d_n=E[X^n] exactly via the rational recurrence.

    (n+1)(2^n-1)d_n = sum_{k=0}^{n-1} binom(n+1,k)d_k.
    """

    d = [Fraction(1)]
    for n in range(1, max_n + 1):
        rhs = sum(Fraction(math.comb(n + 1, k)) * d[k] for k in range(n))
        d.append(rhs / ((n + 1) * (2**n - 1)))
    return d


def centered_even_moments(max_m: int) -> list[Fraction]:
    """Return c_m=E[(2X-1)^(2m)] using c_m=2 d_{2m+1}/(2m+1)."""

    d = rational_moments(2 * max_m + 1)
    return [Fraction(2) * d[2 * m + 1] / (2 * m + 1) for m in range(max_m + 1)]


def s1_from_moments(z: complex, c: Iterable[Fraction]) -> complex:
    """Evaluate S_1(z)=E[(z-Y)^(-1)] by its |z|>1 moment series."""

    total = 0.0 + 0.0j
    for m, cm in enumerate(c):
        total += float(cm) / (z ** (2 * m + 1))
    return total


def s1_prime_from_moments(z: complex, c: Iterable[Fraction]) -> complex:
    """Differentiate the convergent moment series term by term."""

    total = 0.0 + 0.0j
    for m, cm in enumerate(c):
        total -= (2 * m + 1) * float(cm) / (z ** (2 * m + 2))
    return total


def phi_up(xi: float, terms: int = 64) -> float:
    """Fourier transform Phi(xi)=product_{j>=0}sinc(pi*xi/2^j)."""

    js = np.arange(terms, dtype=float)
    return float(np.prod(np.sinc(xi / np.exp2(js))))


def integrate_unit_intervals(
    integrand: Callable[[float], float], upper: int, epsabs: float = 2e-12
) -> tuple[float, float]:
    """Integrate an oscillatory function interval-by-interval on [0, upper]."""

    value = 0.0
    error = 0.0
    for k in range(upper):
        v, e = quad(integrand, float(k), float(k + 1), epsabs=epsabs, epsrel=2e-11, limit=160)
        value += v
        error += e
    return value, error


def direct_mixed_integral(
    grid: FabiusGrid, p: int, q: int, h: Callable[[np.ndarray], np.ndarray]
) -> float:
    """Direct grid quadrature of h(x) F(x)^p (1-F(x))^q."""

    values = h(grid.x) * grid.f**p * (1.0 - grid.f) ** q
    return float(np.trapezoid(values, grid.x))


def order_statistic_rhs(
    grid: FabiusGrid,
    p: int,
    q: int,
    H: Callable[[float], float],
) -> float:
    """Evaluate the adjacent-order-statistic side by beta quadrature.

    If N=p+q, then F(Z_{k:N}) is Beta(k,N+1-k).  This turns each
    order-statistic expectation into a one-dimensional integral involving G.
    """

    n = p + q

    def expected_H(k: int) -> float:
        log_norm = betaln(k, n + 1 - k)

        def integrand(u: float) -> float:
            if u <= 0.0 or u >= 1.0:
                return 0.0
            log_weight = (k - 1) * math.log(u) + (n - k) * math.log1p(-u) - log_norm
            return H(float(grid.G(u))) * math.exp(log_weight)

        value, _ = quad(integrand, 0.0, 1.0, epsabs=2e-11, epsrel=2e-10, limit=250)
        return value

    gap = expected_H(p + 1) - expected_H(p)
    return gap / float(comb(n, p, exact=True))


def fractional_spacing_rhs(
    grid: FabiusGrid, p: int, q: int, x0: float, nu: float
) -> float:
    """Order-statistic formula for the Riemann--Liouville primitive."""

    n = p + q

    def truncated_power_expectation(k: int) -> float:
        log_norm = betaln(k, n + 1 - k)

        def integrand(u: float) -> float:
            z = float(grid.G(u))
            if z >= x0 or u <= 0.0 or u >= 1.0:
                return 0.0
            log_weight = (k - 1) * math.log(u) + (n - k) * math.log1p(-u) - log_norm
            return (x0 - z) ** nu * math.exp(log_weight)

        value, _ = quad(integrand, 0.0, 1.0, epsabs=3e-11, epsrel=3e-10, limit=250)
        return value

    return (
        truncated_power_expectation(p) - truncated_power_expectation(p + 1)
    ) / (math.gamma(nu + 1.0) * float(comb(n, p, exact=True)))


def direct_fractional_primitive(
    grid: FabiusGrid, p: int, q: int, x0: float, nu: float
) -> float:
    """Direct Riemann--Liouville integral of order nu at x0."""

    mask = grid.x <= x0
    x = grid.x[mask]
    f = grid.f[mask]
    kernel = np.maximum(x0 - x, 0.0) ** (nu - 1.0)
    values = kernel * f**p * (1.0 - f) ** q / math.gamma(nu)
    return float(np.trapezoid(values, x))


def balanced_K(grid: FabiusGrid, m: int) -> float:
    """Compute K_m=(2m+1)C(2m,m) int F^m(1-F)^m dx stably."""

    f = grid.f
    interior = (f > 0.0) & (f < 1.0)
    logw = np.full_like(f, -np.inf)
    logw[interior] = m * (np.log(f[interior]) + np.log1p(-f[interior]))
    shift = float(np.max(logw))
    scaled = np.exp(logw - shift)
    log_integral = math.log(float(np.trapezoid(scaled, grid.x))) + shift
    log_beta = 2.0 * math.lgamma(m + 1.0) - math.lgamma(2.0 * m + 2.0)
    return math.exp(log_integral - log_beta)


def write_results(output: Path, grid_power: int) -> None:
    """Run all experiments and write a human-readable result ledger."""

    grid = build_fabius_grid(power=grid_power)
    lines: list[str] = []
    emit = lines.append

    emit("FABIUS--RVACHEV INTEGRAL-TRANSFORM NUMERICAL CHECKS")
    emit("=" * 67)
    emit(f"Uniform grid: 2^{grid_power} subintervals")
    emit("")

    emit("1. Fixed-point and exact-value checks")
    f_quarter = float(grid.F(0.25))
    exact_quarter = 5.0 / 72.0
    emit(f"F(1/4), grid              = {f_quarter:.16g}")
    emit(f"F(1/4), exact 5/72         = {exact_quarter:.16g}")
    emit(f"absolute error             = {abs(f_quarter-exact_quarter):.3e}")
    symmetry_error = float(np.max(np.abs(grid.f + grid.f[::-1] - 1.0)))
    emit(f"max symmetry residual      = {symmetry_error:.3e}")
    emit("")

    emit("2. Exact rational moments")
    d = rational_moments(8)
    for n, value in enumerate(d):
        emit(f"d_{n} = {value}  ~= {float(value):.16g}")
    c = centered_even_moments(36)
    emit("Centered even moments c_m=E[(2X-1)^(2m)] (first six):")
    for m in range(6):
        emit(f"c_{m} = {c[m]}")
    emit("")

    emit("3. Adjacent-order-statistic spacing theorem")
    p, q = 2, 3
    direct = direct_mixed_integral(grid, p, q, np.exp)
    rhs = order_statistic_rhs(grid, p, q, math.exp)
    emit(f"Integral exp(x) F(x)^{p}(1-F(x))^{q} dx = {direct:.16g}")
    emit(f"Order-statistic RHS                       = {rhs:.16g}")
    emit(f"absolute residual                         = {abs(direct-rhs):.3e}")

    x0, nu = 0.71, 1.65
    direct_frac = direct_fractional_primitive(grid, p, q, x0, nu)
    rhs_frac = fractional_spacing_rhs(grid, p, q, x0, nu)
    emit(f"RL primitive order {nu:g} at x={x0:g}, direct = {direct_frac:.16g}")
    emit(f"RL primitive order {nu:g}, spacing RHS       = {rhs_frac:.16g}")
    emit(f"absolute residual                             = {abs(direct_frac-rhs_frac):.3e}")
    emit("")

    emit("4. Cauchy-transform functional-differential equation")
    for z in [2.0 + 0.0j, 1.7 + 0.4j, 2.5 - 0.3j]:
        lhs = s1_prime_from_moments(z, c)
        rhs_c = 2.0 * (s1_from_moments(2.0 * z + 1.0, c) - s1_from_moments(2.0 * z - 1.0, c))
        emit(f"z={z!s:>10}: |S1'(z)-2(S1(2z+1)-S1(2z-1))| = {abs(lhs-rhs_c):.3e}")
    emit("")

    emit("5. Sinc-product energy and the F^2 constant")
    a2_grid = float(np.trapezoid(grid.f**2, grid.x))
    phi2, phi2_err = integrate_unit_intervals(lambda t: phi_up(t) ** 2, upper=64)

    def gini_integrand(t: float) -> float:
        if abs(t) < 1.0e-7:
            return 4.0 * math.pi**2 / 9.0
        ph = phi_up(t)
        return (1.0 - ph * ph) / (t * t)

    gini_core, gini_err = integrate_unit_intervals(gini_integrand, upper=128)
    # For t>=128, Phi(t)^2 is numerically negligible; integrate 1/t^2 exactly.
    gini_weighted = gini_core + 1.0 / 128.0
    a2_from_gini = 0.5 - gini_weighted / (4.0 * math.pi**2)
    sum_rule = phi2 + gini_weighted / (4.0 * math.pi**2)
    emit(f"A2 from F grid                          = {a2_grid:.16g}")
    emit(f"integral_0^64 Phi(xi)^2 dxi            = {phi2:.16g} (quad err <= {phi2_err:.2e})")
    emit(f"A2 from Gini/sinc complement           = {a2_from_gini:.16g}")
    emit(f"sum-rule left side (target 1/2)        = {sum_rule:.16g}")
    emit(f"sum-rule residual                      = {abs(sum_rule-0.5):.3e}")
    emit("")

    emit("6. Balanced beta localization")
    emit("K_m=(2m+1) C(2m,m) int F^m(1-F)^m; theorem: K_m downarrow 1/2")
    emit("m        K_m                    K_m-1/2              log(delta)/(log m)^2")
    for m in [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000]:
        km = balanced_K(grid, m)
        delta = max(km - 0.5, np.finfo(float).tiny)
        ratio = math.log(delta) / (math.log(m) ** 2) if m > 1 else float("nan")
        emit(f"{m:<8d} {km:.16g}   {delta:.8e}   {ratio: .8f}")
    emit(f"Predicted limiting ratio: {-1.0/(8.0*math.log(2.0)):.12f}")
    emit("The convergence is expected to be extremely slow; the grid also reaches")
    emit("its precision floor for the largest m.  These rows are diagnostic, not")
    emit("a numerical proof of the logarithmic asymptotic.")
    emit("")

    emit("7. Integrability contrast (interpretive numerical note)")
    emit("Negative moments E[X^{-s}] are finite for every fixed s>0, whereas")
    emit("the Lebesgue integral of F(x)^{-s} over x in (0,1) diverges.  The report")
    emit("proves this contrast from the quadratic endpoint logarithm.")

    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--grid-power",
        type=int,
        default=17,
        help="use 2**POWER uniform subintervals (default: 17)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("numerical_results.txt"),
        help="result ledger path",
    )
    args = parser.parse_args()
    if not 12 <= args.grid_power <= 20:
        raise SystemExit("--grid-power must lie between 12 and 20")
    write_results(args.output, args.grid_power)
    print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
