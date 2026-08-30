#!/usr/bin/env python3
"""Numerical and symbolic checks for the Fabius--Rvachev frontier report.

The report proves its main statements analytically.  This script serves four
more modest purposes:

1. evaluate Rvachev's up-function from its rapidly convergent period-two
   Fourier series and check the exact midpoint/endpoint transmutation law;
2. solve the inverse-midpoint fixed-point equation and compare the resulting
   flat defect with its leading endpoint approximation F(delta/2)/2;
3. construct the inverse-moment Appell polynomials from Bernoulli cumulants,
   verify their exact q-binomial scale closure symbolically, and test the
   cardinal reproduction formulas numerically;
4. generate the tables and figures included in the report.

No Internet access is used.  Required packages are mpmath, SymPy, NumPy, and
Matplotlib.  All truncation parameters are centralized below so that higher
precision runs are easy to reproduce.

Usage
-----
    python frontier_experiments.py

Outputs are written next to this file, under ``results/`` and ``figures/``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import ceil, floor, factorial
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import sympy as sp

# Matplotlib is imported only after a noninteractive backend is selected.
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"
FIGURES = ROOT / "figures"
RESULTS.mkdir(exist_ok=True)
FIGURES.mkdir(exist_ok=True)


@dataclass(frozen=True)
class Settings:
    """Precision and truncation parameters used by the experiments."""

    decimal_digits: int = 70
    fourier_modes: int = 420
    product_factors: int = 240
    reproduction_max_scale: int = 5


SETTINGS = Settings()
mp.mp.dps = SETTINGS.decimal_digits


def sinc_pi(x: mp.mpf) -> mp.mpf:
    """Return sin(pi*x)/(pi*x), with the removable value at x=0."""

    if x == 0:
        return mp.mpf(1)
    return mp.sin(mp.pi * x) / (mp.pi * x)


def hat_up(xi: mp.mpf, factors: int = SETTINGS.product_factors) -> mp.mpf:
    r"""Evaluate \hat{up}(xi) from the infinite sinc product.

    Under the Fourier convention

        \hat f(xi) = integral f(x) exp(-2*pi*i*x*xi) dx,

    Rvachev's function satisfies

        \hat{up}(xi) = product_{n>=0} sinc(pi*xi/2^n).

    The omitted tail differs from 1 by O(xi^2 4^{-factors}), which is much
    smaller than the working precision for the half-integer frequencies used
    below.
    """

    value = mp.mpf(1)
    scale = mp.mpf(1)
    for _ in range(factors):
        value *= sinc_pi(xi / scale)
        scale *= 2
    return value


def half_integer_coefficients(
    modes: int = SETTINGS.fourier_modes,
) -> tuple[mp.mpf, ...]:
    r"""Fourier coefficients \hat{up}(m+1/2), m=0,...,modes-1."""

    return tuple(hat_up(mp.mpf(m) + mp.mpf("0.5")) for m in range(modes))


COEFFS_MP = half_integer_coefficients()
COEFFS_FLOAT = np.asarray([float(c) for c in COEFFS_MP], dtype=float)
FREQUENCIES_FLOAT = (2 * np.arange(SETTINGS.fourier_modes) + 1) * np.pi


def up_mpf(x: mp.mpf, coeffs: Sequence[mp.mpf] = COEFFS_MP) -> mp.mpf:
    r"""Evaluate up(x) on [-1,1] from its period-two cosine series.

    Periodizing the compactly supported C-infinity function with period two
    gives

        up(x) = 1/2 + sum_{m>=0} \hat{up}(m+1/2)
                             cos((2m+1) pi x).

    All nonzero integer Fourier coefficients vanish, so only half-integer
    frequencies remain.  Values outside the support are returned as zero.
    """

    x = mp.mpf(x)
    if abs(x) > 1:
        return mp.mpf(0)
    total = mp.mpf("0.5")
    for m, coefficient in enumerate(coeffs):
        total += coefficient * mp.cos((2 * m + 1) * mp.pi * x)
    return total


def up_float(values: np.ndarray | Sequence[float] | float) -> np.ndarray:
    """Vectorized double-precision version of :func:`up_mpf` for plotting."""

    array = np.asarray(values, dtype=float)
    flat = array.reshape(-1)
    out = np.zeros_like(flat)
    inside = np.abs(flat) <= 1.0
    if np.any(inside):
        phases = np.outer(flat[inside], FREQUENCIES_FLOAT)
        out[inside] = 0.5 + np.cos(phases) @ COEFFS_FLOAT
    return out.reshape(array.shape)


def fabius_mpf(x: mp.mpf) -> mp.mpf:
    """Evaluate the bounded Fabius distribution function on the real line."""

    x = mp.mpf(x)
    if x <= 0:
        return mp.mpf(0)
    if x >= 1:
        return mp.mpf(1)
    return up_mpf(x - 1)


def fabius_float(values: np.ndarray | Sequence[float] | float) -> np.ndarray:
    """Vectorized double-precision Fabius evaluator on the real line."""

    array = np.asarray(values, dtype=float)
    out = np.zeros_like(array)
    out[array >= 1.0] = 1.0
    interior = (array > 0.0) & (array < 1.0)
    if np.any(interior):
        out[interior] = up_float(array[interior] - 1.0)
    return out


def exact_dyadic_values(max_n: int = 12) -> list[Fraction]:
    r"""Return exact values V_n=F(2^{-n}) from the triangular recurrence.

    The recurrence used in the repository is

        V_n = 2^{-n(n-1)/2}/(2^n-1)
              * sum_{k=0}^{n-1} 2^{k(k-1)/2} V_k/(n-k+1)!.

    Fractions are used throughout, so this experiment is exact.
    """

    values = [Fraction(1, 1)]  # V_0 = F(1) = 1
    for n in range(1, max_n + 1):
        total = Fraction(0, 1)
        for k in range(n):
            total += (
                Fraction(2 ** (k * (k - 1) // 2), factorial(n - k + 1))
                * values[k]
            )
        prefactor = Fraction(1, 2 ** (n * (n - 1) // 2) * (2**n - 1))
        values.append(prefactor * total)
    return values


def midpoint_identity_table() -> list[tuple[mp.mpf, mp.mpf]]:
    """Residuals in F(1/2+h)=1/2+2h-F(h)."""

    rows: list[tuple[mp.mpf, mp.mpf]] = []
    for h_text in ("0.05", "0.10", "0.20", "0.30", "0.45"):
        h = mp.mpf(h_text)
        residual = fabius_mpf(mp.mpf("0.5") + h) - (
            mp.mpf("0.5") + 2 * h - fabius_mpf(h)
        )
        rows.append((h, residual))
    return rows


def inverse_midpoint_h(delta: mp.mpf) -> mp.mpf:
    r"""Solve delta=2h-F(h) by monotone fixed-point iteration.

    With z=delta/2 the equation is h=z+F(h)/2.  For 0<delta<1/2,
    F'(h)/2<1 at the solution, and the iteration started at h_0=z increases
    monotonically to the unique fixed point.
    """

    delta = mp.mpf(delta)
    if not (0 <= delta < mp.mpf("0.5")):
        raise ValueError("delta must lie in [0, 1/2)")
    z = delta / 2
    h = z
    tolerance = mp.power(10, -(SETTINGS.decimal_digits - 12))
    for _ in range(200):
        next_h = z + fabius_mpf(h) / 2
        if abs(next_h - h) < tolerance:
            return next_h
        h = next_h
    raise RuntimeError("fixed-point iteration did not converge")


def inverse_defect_table() -> list[tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]]:
    """Return delta, exact defect E, F(delta/2)/2, and their ratio."""

    rows = []
    for delta_text in ("0.25", "0.20", "0.15", "0.10", "0.075", "0.05"):
        delta = mp.mpf(delta_text)
        z = delta / 2
        h = inverse_midpoint_h(delta)
        defect = h - z
        leading = fabius_mpf(z) / 2
        rows.append((delta, defect, leading, defect / leading))
    return rows


def bernoulli_cumulant(order: int) -> sp.Rational:
    r"""Return the exact cumulant kappa_order of the up distribution.

    Odd cumulants vanish.  For order=2m,

        kappa_{2m} = 2^{2m-1} B_{2m} / (m(2^{2m}-1)).
    """

    if order % 2:
        return sp.Rational(0)
    m = order // 2
    return sp.Rational(2 ** (2 * m - 1), m * (2 ** (2 * m) - 1)) * sp.bernoulli(2 * m)


def build_appell_polynomials(max_degree: int = 12) -> tuple[sp.Symbol, sp.Symbol, list[sp.Expr]]:
    r"""Construct A_n(x;Q) with generating function exp(x t)/M_Q(t).

    Here Q=4^r encodes dyadic dilation.  The logarithm of the generating
    function is

        x t - sum_{m>=1} kappa_{2m} Q^m t^{2m}/(2m)!.

    Truncating this logarithm at degree ``max_degree`` is exact for all
    coefficients through that degree.
    """

    t, x, Q = sp.symbols("t x Q")
    log_generating = x * t
    for m in range(1, max_degree // 2 + 1):
        order = 2 * m
        log_generating -= bernoulli_cumulant(order) * Q**m * t**order / sp.factorial(order)
    series = sp.exp(log_generating).series(t, 0, max_degree + 1).removeO().expand()
    polynomials = [
        sp.factor(sp.factorial(n) * series.coeff(t, n))
        for n in range(max_degree + 1)
    ]
    return x, Q, polynomials


X_SYMBOL, Q_SYMBOL, APPELL = build_appell_polynomials(12)


def q_binomial(n: int, k: int, q: sp.Rational) -> sp.Expr:
    """Gaussian binomial coefficient evaluated at a rational q."""

    if k < 0 or k > n:
        return sp.Integer(0)
    if k == 0 or k == n:
        return sp.Integer(1)
    numerator = sp.prod(1 - q ** (n - j) for j in range(k))
    denominator = sp.prod(1 - q ** (j + 1) for j in range(k))
    return sp.cancel(sp.sympify(numerator) / sp.sympify(denominator))


def verify_q_closures(max_degree: int = 12) -> list[tuple[int, int, bool]]:
    r"""Verify the exact q-binomial closure for every A_n through max_degree.

    For d=floor(n/2), N=d+1, q=1/4, and arbitrary starting scale R,

        sum_{j=0}^N (-1)^j q^{j(j-1)/2} [N choose j]_q
            A_n(x; R q^{-j}) = 0.
    """

    q = sp.Rational(1, 4)
    R = sp.symbols("R")
    checks: list[tuple[int, int, bool]] = []
    for n in range(max_degree + 1):
        degree = n // 2
        N = degree + 1
        expression = sp.Integer(0)
        for j in range(N + 1):
            weight = (-1) ** j * q ** (j * (j - 1) // 2) * q_binomial(N, j, q)
            expression += weight * APPELL[n].subs(Q_SYMBOL, R * q ** (-j))
        checks.append((n, N, sp.simplify(sp.expand(expression)) == 0))
    return checks


def sympy_rational_to_mpf(value: sp.Expr) -> mp.mpf:
    """Convert an exact SymPy rational/integer to mpmath without float loss."""

    value = sp.Rational(value)
    return mp.mpf(int(value.p)) / mp.mpf(int(value.q))


def eval_exact_poly(poly: sp.Expr, variable: sp.Symbol, value: mp.mpf) -> mp.mpf:
    """Evaluate a univariate exact polynomial by Horner's rule in mpmath."""

    coefficients = sp.Poly(poly, variable).all_coeffs()
    result = mp.mpf(0)
    for coefficient in coefficients:
        result = result * value + sympy_rational_to_mpf(coefficient)
    return result


def up_scaled_mpf(r: int, x: mp.mpf) -> mp.mpf:
    """The normalized dilation U_r(x)=2^{-r} up(2^{-r}x)."""

    scale = mp.mpf(2) ** r
    if abs(x) > scale:
        return mp.mpf(0)
    return up_mpf(x / scale) / scale


def reproduction_errors(max_scale: int = SETTINGS.reproduction_max_scale) -> list[tuple[int, int, mp.mpf]]:
    r"""Numerically test sum_k A_n^{(r)}(k) U_r(x-k)=x^n.

    Only finitely many k contribute because U_r is supported on
    [-2^r,2^r].  Five nonlattice sample points are used at each scale.  The
    returned error is the largest absolute residual over those points.
    """

    samples = [mp.mpf(s) for s in ("-0.83", "-0.41", "0.07", "0.37", "0.79")]
    rows: list[tuple[int, int, mp.mpf]] = []
    for r in range(max_scale + 1):
        support = 2**r
        scale_polys = [sp.expand(APPELL[n].subs(Q_SYMBOL, 4**r)) for n in range(r + 1)]
        max_errors = [mp.mpf(0) for _ in range(r + 1)]
        for point in samples:
            k_min = ceil(float(point - support))
            k_max = floor(float(point + support))
            kernel_values = {
                k: up_scaled_mpf(r, point - k)
                for k in range(k_min, k_max + 1)
            }
            for n, polynomial in enumerate(scale_polys):
                total = mp.mpf(0)
                for k, kernel_value in kernel_values.items():
                    total += eval_exact_poly(polynomial, X_SYMBOL, mp.mpf(k)) * kernel_value
                residual = abs(total - point**n)
                max_errors[n] = max(max_errors[n], residual)
        rows.extend((r, n, max_errors[n]) for n in range(r + 1))
    return rows


def zero_multiplicity(m: int) -> int:
    r"""Multiplicity of the zero of \hat{up} at a nonzero integer m."""

    if m == 0:
        raise ValueError("m must be nonzero")
    n = abs(m)
    valuation = 0
    while n % 2 == 0:
        valuation += 1
        n //= 2
    return valuation + 1


def write_text_results() -> None:
    """Run all checks and write a human-readable result ledger."""

    midpoint = midpoint_identity_table()
    inverse = inverse_defect_table()
    dyadic = exact_dyadic_values(12)
    closures = verify_q_closures(12)
    reproduction = reproduction_errors()

    lines: list[str] = []
    lines.append("FABIUS--RVACHEV FRONTIER EXPERIMENTS")
    lines.append("=" * 44)
    lines.append("")
    lines.append(f"mpmath decimal digits: {SETTINGS.decimal_digits}")
    lines.append(f"Fourier half-integer modes: {SETTINGS.fourier_modes}")
    lines.append(f"sinc-product factors per coefficient: {SETTINGS.product_factors}")
    lines.append("")

    lines.append("1. Exact midpoint/endpoint transmutation residuals")
    lines.append("   identity: F(1/2+h) = 1/2 + 2h - F(h)")
    for h, residual in midpoint:
        lines.append(f"   h={mp.nstr(h, 8):>8s}  residual={mp.nstr(residual, 8)}")
    lines.append("")

    lines.append("2. Inverse midpoint flat defect")
    lines.append("   E(delta)=F^{-1}(1/2+delta)-1/2-delta/2")
    lines.append("   comparison: E(delta) ~ F(delta/2)/2")
    for delta, defect, leading, ratio in inverse:
        lines.append(
            "   delta={:>7s}  E={}  F(delta/2)/2={}  ratio={}".format(
                mp.nstr(delta, 7), mp.nstr(defect, 12), mp.nstr(leading, 12), mp.nstr(ratio, 12)
            )
        )
    lines.append("")

    lines.append("3. Exact dyadic endpoint values V_n=F(2^{-n})")
    for n, value in enumerate(dyadic):
        lines.append(
            f"   n={n:2d}  V_n={value.numerator}/{value.denominator}"
            f"  decimal={float(value):.16e}"
        )
    lines.append("")

    lines.append("4. Bernoulli cumulants of the up distribution")
    for order in range(2, 12, 2):
        lines.append(f"   kappa_{order} = {sp.sstr(bernoulli_cumulant(order))}")
    lines.append("")

    lines.append("5. Inverse-moment Appell polynomials A_n(x;Q)")
    for n in range(9):
        lines.append(f"   A_{n}(x;Q) = {sp.sstr(APPELL[n])}")
    lines.append("")

    lines.append("6. Exact q-binomial scale closures (q=1/4)")
    for n, N, passed in closures:
        lines.append(f"   degree n={n:2d}, closure order N={N:2d}: {'PASS' if passed else 'FAIL'}")
    lines.append("")

    lines.append("7. Cardinal reproduction maximum residuals")
    lines.append("   max over x in {-0.83,-0.41,0.07,0.37,0.79}")
    for r, n, error in reproduction:
        lines.append(f"   r={r:2d}, n={n:2d}: {mp.nstr(error, 8)}")
    lines.append("")

    (RESULTS / "numerical_results.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")

    # Machine-readable CSV versions of the two principal numerical tables.
    with (RESULTS / "inverse_defect.csv").open("w", encoding="utf-8", newline="") as handle:
        handle.write("delta,defect,leading_endpoint_term,ratio\n")
        for delta, defect, leading, ratio in inverse:
            handle.write(
                f"{mp.nstr(delta, 30)},{mp.nstr(defect, 30)},"
                f"{mp.nstr(leading, 30)},{mp.nstr(ratio, 30)}\n"
            )

    with (RESULTS / "reproduction_errors.csv").open("w", encoding="utf-8", newline="") as handle:
        handle.write("scale_r,degree_n,max_abs_residual\n")
        for r, n, error in reproduction:
            handle.write(f"{r},{n},{mp.nstr(error, 30)}\n")


def make_inverse_defect_figure() -> None:
    """Plot the inverse defect and its leading endpoint approximation."""

    deltas = np.linspace(0.04, 0.28, 49)
    defects: list[float] = []
    leading_terms: list[float] = []
    for delta_float in deltas:
        delta = mp.mpf(str(delta_float))
        z = delta / 2
        h = inverse_midpoint_h(delta)
        defects.append(float(h - z))
        leading_terms.append(float(fabius_mpf(z) / 2))

    fig, ax = plt.subplots(figsize=(7.2, 4.5))
    ax.semilogy(deltas, defects, label=r"$E(\delta)$")
    ax.semilogy(deltas, leading_terms, label=r"$F(\delta/2)/2$")
    ax.set_xlabel(r"$\delta$")
    ax.set_ylabel("flat defect")
    ax.set_title("Inverse-midpoint defect and endpoint proxy")
    ax.grid(True, which="both", alpha=0.25)
    ax.legend()
    fig.tight_layout()
    fig.savefig(FIGURES / "inverse_midpoint_defect.png", dpi=220)
    fig.savefig(FIGURES / "inverse_midpoint_defect.pdf")
    plt.close(fig)


def make_zero_multiplicity_figure() -> None:
    """Plot the exact dyadic zero-multiplicity ladder at integers 1,...,64."""

    integers = np.arange(1, 65)
    multiplicities = np.asarray([zero_multiplicity(int(m)) for m in integers])
    fig, ax = plt.subplots(figsize=(7.2, 4.2))
    markerline, stemlines, baseline = ax.stem(integers, multiplicities)
    # No explicit colors or styles are imposed; Matplotlib defaults are kept.
    ax.set_xlabel(r"integer frequency $m$")
    ax.set_ylabel(r"$\operatorname{ord}_m \widehat{\mathrm{up}}$")
    ax.set_title(r"Dyadic zero multiplicities: $1+\nu_2(m)$")
    ax.set_xlim(0, 65)
    ax.set_ylim(0, int(multiplicities.max()) + 1)
    ax.grid(True, axis="y", alpha=0.25)
    fig.tight_layout()
    fig.savefig(FIGURES / "zero_multiplicity_ladder.png", dpi=220)
    fig.savefig(FIGURES / "zero_multiplicity_ladder.pdf")
    plt.close(fig)


def main() -> None:
    write_text_results()
    make_inverse_defect_figure()
    make_zero_multiplicity_figure()
    print(f"Wrote results to {RESULTS}")
    print(f"Wrote figures to {FIGURES}")


if __name__ == "__main__":
    main()
