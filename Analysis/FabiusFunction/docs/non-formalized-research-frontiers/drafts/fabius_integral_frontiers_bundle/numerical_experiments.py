#!/usr/bin/env python3
"""Numerical experiments for the Fabius--Rvachev integral-frontier report.

The script constructs Rvachev's up-function by Fourier inversion of

    up_hat(xi) = product_{n>=0} sinc(pi*xi/2^n),

using a Fourier-series discretization on a period-four interval.  The true
function is supported on [-1,1], so period four prevents overlap of periodic
copies.  It then verifies the new identities in the accompanying report:

* the integer antiderivative ladder for F and up;
* weighted monomial antiderivative series;
* bilateral Laplace-transform products;
* the Mellin/binomial moment interpolation D(z);
* the exact pushforward law of normalized derivatives;
* the closed primitive of the inverse Fabius function;
* the small but nonzero log-periodic obstruction to a naive fractional
  derivative/dilation identity.

The calculations are checks, not substitutes for the proofs in the report.
All quadrature is performed on the FFT grid unless otherwise noted.

Usage
-----
    python numerical_experiments.py

Outputs are written next to the script:
    numerical_results.txt
    functions_and_primitives.png
    pushforward_cdf.png
    fractional_defect.png

Dependencies: numpy, scipy, matplotlib, mpmath.
"""

from __future__ import annotations

import math
from pathlib import Path
from typing import Callable, Iterable

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy.integrate import cumulative_trapezoid, simpson
from scipy.interpolate import PchipInterpolator


HERE = Path(__file__).resolve().parent


def build_up_fft(
    n_grid: int = 2**18,
    period: float = 4.0,
    n_product_factors: int = 36,
) -> tuple[np.ndarray, np.ndarray]:
    """Return an equispaced approximation of up on [-1,1].

    With the Fourier convention

        f_hat(xi) = integral f(x) exp(-2*pi*i*x*xi) dx,

    the periodic Fourier-series coefficient on an interval of length L is
    f_hat(k/L)/L.  NumPy's inverse FFT has a 1/N normalization, hence its
    coefficient array must be multiplied by N/L.
    """
    if n_grid <= 0 or n_grid & (n_grid - 1):
        raise ValueError("n_grid must be a positive power of two")
    if period <= 2.0:
        raise ValueError("period must exceed the support diameter 2")

    dx = period / n_grid
    frequencies = np.fft.fftfreq(n_grid, d=dx)
    transform = np.ones(n_grid, dtype=float)

    # np.sinc(y) means sin(pi*y)/(pi*y), exactly matching each factor.
    for n in range(n_product_factors):
        transform *= np.sinc(frequencies / (2**n))

    coefficient_array = (n_grid / period) * transform
    periodic_values = np.fft.ifft(coefficient_array).real
    centered_values = np.fft.fftshift(periodic_values)
    centered_grid = (np.arange(n_grid) - n_grid // 2) * dx

    support_mask = (centered_grid >= -1.0) & (centered_grid <= 1.0)
    x = centered_grid[support_mask]
    up = centered_values[support_mask]

    # Roundoff can create signed noise of order 1e-16 where the exact value is 0.
    up[np.abs(up) < 5e-15] = 0.0
    up = np.maximum(up, 0.0)
    up[0] = 0.0
    up[-1] = 0.0
    return x, up


def thue_morse_sign(k: np.ndarray) -> np.ndarray:
    """Return (-1)^(binary digit sum of k), vectorized for nonnegative ints."""
    return np.fromiter(
        (1.0 if int(v).bit_count() % 2 == 0 else -1.0 for v in k),
        dtype=float,
        count=len(k),
    )


def global_self_differential_extension(
    y: np.ndarray,
    up_interpolator: PchipInterpolator,
) -> np.ndarray:
    """Evaluate the signed block extension mathcal F on y >= 0.

    On the block [2k,2k+2],
        mathcal F(y) = epsilon_k up(y-2k-1),
    where epsilon_k is the Thue--Morse sign.
    """
    y = np.asarray(y, dtype=float)
    if np.any(y < 0):
        raise ValueError("this helper is intended for y >= 0")
    k = np.floor(y / 2.0).astype(np.int64)
    local_coordinate = y - (2.0 * k + 1.0)
    values = np.asarray(up_interpolator(local_coordinate), dtype=float)
    return thue_morse_sign(k) * values


def bilateral_mgf_product(s: complex, factors: int = 80) -> complex:
    """M(s)=integral exp(s*x) up(x) dx as an infinite sinh product."""
    result = 1.0 + 0.0j
    for j in range(1, factors + 1):
        z = s / (2**j)
        if abs(z) < 1e-8:
            factor = 1.0 + z * z / 6.0 + z**4 / 120.0
        else:
            factor = np.sinh(z) / z
        result *= factor
    return complex(result)


def global_laplace_product(s: float, factors: int = 80) -> float:
    """Laplace transform of the global signed extension mathcal F.

    Block decomposition gives

      L(s)=exp(-s) M(s) product_{j>=1}(1-exp(-2^j s)),  s>0.
    """
    if s <= 0:
        raise ValueError("s must be positive")
    q_product = 1.0
    for j in range(1, factors + 1):
        q = math.exp(-(2**j) * s)
        q_product *= 1.0 - q
        if q < 1e-18:
            break
    return math.exp(-s) * bilateral_mgf_product(s, factors).real * q_product


def mellin_D_quadrature(z: complex, x_up: np.ndarray, up: np.ndarray) -> complex:
    """D(z)=integral_{-1}^1 ((1+t)/2)^z up(t) dt."""
    base = (1.0 + x_up) / 2.0
    values = np.zeros_like(base, dtype=np.complex128)
    positive = base > 0.0
    values[positive] = np.power(base[positive].astype(np.complex128), z) * up[positive]
    values[~positive] = 0.0
    return complex(simpson(values, x=x_up))


def mellin_D_series(z: complex, moments: Iterable[float]) -> complex:
    """Evaluate 2^{-z} sum_{j>=0} binom(z,2j)c_j."""
    z_mp = mp.mpc(z)
    total = mp.mpc(0)
    for j, c_j in enumerate(moments):
        total += mp.binomial(z_mp, 2 * j) * mp.mpf(float(c_j))
    return complex(mp.power(2, -z_mp) * total)


def monotone_inverse_interpolator(
    x: np.ndarray,
    y: np.ndarray,
) -> Callable[[np.ndarray | float], np.ndarray]:
    """Build a robust linear inverse after removing numerical plateaus."""
    monotone = np.maximum.accumulate(np.clip(y, 0.0, 1.0))
    unique_y, unique_indices = np.unique(monotone, return_index=True)
    unique_x = x[unique_indices]

    # Guarantee exact endpoints even if floating-point underflow created plateaus.
    if unique_y[0] > 0.0:
        unique_y = np.insert(unique_y, 0, 0.0)
        unique_x = np.insert(unique_x, 0, 0.0)
    if unique_y[-1] < 1.0:
        unique_y = np.append(unique_y, 1.0)
        unique_x = np.append(unique_x, 1.0)

    def inverse(v: np.ndarray | float) -> np.ndarray:
        return np.interp(v, unique_y, unique_x)

    return inverse


def verify_and_write() -> None:
    x_up, up = build_up_fft()
    dx = x_up[1] - x_up[0]
    midpoint = (len(x_up) - 1) // 2

    # F(x)=up(x-1) on [0,1].
    x_f = x_up[: midpoint + 1] + 1.0
    fabius = up[: midpoint + 1].copy()
    fabius[0] = 0.0
    fabius[-1] = 1.0

    up_interp = PchipInterpolator(x_up, up, extrapolate=False)
    f_interp = PchipInterpolator(x_f, fabius, extrapolate=False)
    inverse_f = monotone_inverse_interpolator(x_f, fabius)

    lines: list[str] = []
    lines.append("FABIUS--RVACHEV INTEGRAL FRONTIER: NUMERICAL CHECKS")
    lines.append("=" * 66)
    lines.append(f"FFT grid spacing: {dx:.17g}")
    lines.append(f"Integral of up: {simpson(up, x=x_up):.16g}")
    lines.append(f"Integral of F:  {simpson(fabius, x=x_f):.16g}")
    lines.append("")

    # ------------------------------------------------------------------
    # Core constants and moments.
    # ------------------------------------------------------------------
    moments = np.array(
        [simpson((x_up ** (2 * j)) * up, x=x_up) for j in range(321)],
        dtype=float,
    )
    f2 = float(simpson(fabius**2, x=x_f))
    f3 = float(simpson(fabius**3, x=x_f))
    up2 = float(simpson(up**2, x=x_up))
    lines.append("Selected constants")
    lines.append(f"  int_0^1 F(x)^2 dx   = {f2:.15f}")
    lines.append(f"  int_0^1 F(x)^3 dx   = {f3:.15f}")
    lines.append(f"  int_-1^1 up(x)^2 dx = {up2:.15f}")
    lines.append(f"  check up^2 = 2 F^2: error {abs(up2 - 2*f2):.3e}")
    for j in range(6):
        lines.append(f"  c_{j} = int x^{2*j} up(x) dx = {moments[j]:.15f}")
    lines.append("")

    # ------------------------------------------------------------------
    # Integer antiderivative ladders.
    # ------------------------------------------------------------------
    lines.append("Integer antiderivative ladders")
    current_f = fabius.copy()
    for n in range(1, 6):
        current_f = cumulative_trapezoid(current_f, x_f, initial=0.0)
        predicted = (2 ** (n * (n - 1) // 2)) * f_interp(x_f / (2**n))
        error = float(np.max(np.abs(current_f - predicted)))
        lines.append(f"  F, order {n}: max grid error {error:.3e}")

    current_up = up.copy()
    for n in range(1, 6):
        current_up = cumulative_trapezoid(current_up, x_up, initial=0.0)
        predicted = (2 ** (n * (n - 1) // 2)) * f_interp((x_up + 1.0) / (2**n))
        error = float(np.max(np.abs(current_up - predicted)))
        lines.append(f"  up, order {n}: max grid error {error:.3e}")
    lines.append("")

    # ------------------------------------------------------------------
    # Fractional/negative monomial weighted primitive series.
    # ------------------------------------------------------------------
    lines.append("Weighted monomial primitive series at x=0.73")
    x0 = 0.73

    # For high order k the closed scaled-F expression underflows in ordinary
    # double precision.  The mathematically identical Volterra ladder is
    # therefore generated by cumulative integration for this numerical check.
    primitive_ladder = [fabius.copy()]
    ladder_value = fabius.copy()
    for _ in range(100):
        ladder_value = cumulative_trapezoid(ladder_value, x_f, initial=0.0)
        primitive_ladder.append(ladder_value.copy())

    from scipy.integrate import quad

    for alpha in (-1.5, -0.5, 0.5, 2.5):
        direct = float(
            quad(
                lambda q: (q**alpha) * float(f_interp(q)) if q > 0.0 else 0.0,
                0.0,
                x0,
                epsabs=1e-13,
                limit=500,
            )[0]
        )
        partial = 0.0
        falling = 1.0
        for k in range(100):
            if k > 0:
                falling *= alpha - (k - 1)
            a_k1 = float(np.interp(x0, x_f, primitive_ladder[k + 1]))
            partial += ((-1.0) ** k) * falling * (x0 ** (alpha - k)) * a_k1
        lines.append(
            f"  alpha={alpha:4.1f}: direct={direct:.15e}, "
            f"series={partial:.15e}, error={abs(direct-partial):.3e}"
        )
    lines.append("")

    # ------------------------------------------------------------------
    # Bilateral Laplace product and one-sided F transform.
    # ------------------------------------------------------------------
    lines.append("Laplace-transform checks")
    for s in (1.0, 2.0, -3.0, 1.0 + 2.0j):
        direct_m = complex(simpson(np.exp(s * x_up) * up, x=x_up))
        product_m = bilateral_mgf_product(s)
        direct_f = complex(simpson(np.exp(s * x_f) * fabius, x=x_f))
        formula_f = (np.exp(s) - np.exp(s / 2.0) * bilateral_mgf_product(s / 2.0)) / s
        lines.append(
            f"  s={s!s:>8}: |M_quad-M_prod|={abs(direct_m-product_m):.3e}, "
            f"|F_quad-F_formula|={abs(direct_f-formula_f):.3e}"
        )
    lines.append("")

    # ------------------------------------------------------------------
    # Entire Mellin interpolation D(z).
    # ------------------------------------------------------------------
    lines.append("Mellin/binomial interpolation checks")
    for z in (-3.0, -1.0, 0.5, 2.0, 1.0 + 2.0j):
        direct = mellin_D_quadrature(z, x_up, up)
        series = mellin_D_series(z, moments)
        lines.append(
            f"  z={z!s:>8}: D_quad={direct:.13g}, D_series={series:.13g}, "
            f"error={abs(direct-series):.3e}"
        )

    # Logarithmic inverse moments D^(k)(0).
    base = (1.0 + x_up) / 2.0
    log_base = np.zeros_like(base)
    positive = base > 0.0
    log_base[positive] = np.log(base[positive])
    lines.append("  logarithmic inverse moments")
    for k in range(1, 5):
        value = float(simpson(up * (log_base**k), x=x_up))
        lines.append(f"    int_0^1 log(I(y))^{k} dy = {value:.15f}")
    lines.append("")

    # ------------------------------------------------------------------
    # Exact pushforward law of all normalized derivatives.
    # ------------------------------------------------------------------
    lines.append("Derivative pushforward checks")
    sample_count = 200_000
    sample_x = (np.arange(sample_count) + 0.5) / sample_count
    f_sample = np.clip(f_interp(sample_x), 0.0, 1.0)
    for m in range(1, 7):
        normalized = np.abs(
            global_self_differential_extension((2**m) * sample_x, up_interp)
        )
        normalized = np.clip(normalized, 0.0, 1.0)
        moment_error = max(
            abs(float(np.mean(normalized**p) - np.mean(f_sample**p)))
            for p in (0.5, 1.0, 2.0, 3.0, 5.0)
        )
        sorted_error = float(
            np.max(np.abs(np.sort(normalized) - np.sort(f_sample)))
        )
        lines.append(
            f"  m={m}: max tested moment error {moment_error:.3e}; "
            f"sorted-sample discrepancy {sorted_error:.3e}"
        )
    lines.append("")

    # ------------------------------------------------------------------
    # Closed primitive of the inverse Fabius function.
    # ------------------------------------------------------------------
    lines.append("Inverse-Fabius primitive checks")
    y_grid = np.linspace(0.0, 1.0, 400_001)
    i_grid = inverse_f(y_grid)
    i_primitive = cumulative_trapezoid(i_grid, y_grid, initial=0.0)
    for y0 in (0.1, 0.25, 0.5, 0.8, 0.95):
        q = float(inverse_f(y0))
        formula = y0 * q - float(f_interp(q / 2.0))
        direct = float(np.interp(y0, y_grid, i_primitive))
        lines.append(
            f"  y={y0:.2f}: direct={direct:.15e}, formula={formula:.15e}, "
            f"error={abs(direct-formula):.3e}"
        )
    lines.append("")

    # ------------------------------------------------------------------
    # Direct integral transforms of the inverse Fabius function.
    # ------------------------------------------------------------------
    lines.append("Inverse exponential/Stieltjes transform checks")
    for s in (0.7, -1.3, 0.4 + 1.1j):
        direct = complex(simpson(np.exp(s * i_grid), x=y_grid))
        formula = np.exp(s / 2.0) * bilateral_mgf_product(s / 2.0)
        lines.append(
            f"  exponential s={s!s:>10}: error={abs(direct-formula):.3e}"
        )

    z_stieltjes = 1.4 + 0.6j
    direct_stieltjes = complex(simpson(1.0 / (z_stieltjes - i_grid), x=y_grid))
    w = 2.0 * z_stieltjes - 1.0
    cauchy_up = complex(simpson(up / (w - x_up), x=x_up))
    formula_stieltjes = 2.0 * cauchy_up
    lines.append(
        f"  Stieltjes z={z_stieltjes!s:>10}: "
        f"error={abs(direct_stieltjes-formula_stieltjes):.3e}"
    )
    lines.append("")

    # ------------------------------------------------------------------
    # Fractional derivative/dilation obstruction.
    # ------------------------------------------------------------------
    lines.append("Fractional derivative/dilation defect")
    lines.append(
        "  E_alpha(s)=2^{alpha(alpha-1)/2} L(s/2^alpha)/(s^alpha L(s)); "
        "integer alpha gives 1."
    )
    for alpha in (0.25, 0.5, 0.75):
        values = []
        for s in (0.3, 0.7, 1.0, 1.3, 3.1):
            value = (
                2 ** (alpha * (alpha - 1.0) / 2.0)
                * global_laplace_product(s / (2**alpha))
                / ((s**alpha) * global_laplace_product(s))
            )
            values.append(value - 1.0)
        lines.append(
            f"  alpha={alpha:.2f}: min(E-1)={min(values):+.8e}, "
            f"max(E-1)={max(values):+.8e}"
        )
    lines.append("")

    # ------------------------------------------------------------------
    # Figures.
    # ------------------------------------------------------------------
    fig, ax = plt.subplots(figsize=(8.2, 4.8))
    ax.plot(x_up, up, label=r"$\operatorname{up}(x)$")
    ax.plot(x_f, fabius, label=r"$F(x)$")
    ax.plot(x_f, f_interp(x_f / 2.0), label=r"$\int_0^xF(t)\,dt=F(x/2)$")
    ax.set_xlabel("x")
    ax.set_ylabel("value")
    ax.set_title("Fabius, Rvachev up, and the first primitive")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(HERE / "functions_and_primitives.png", dpi=180)
    plt.close(fig)

    # Empirical CDF of |F^(4)|/Q_4 and the exact target I(a).
    m = 4
    normalized = np.abs(
        global_self_differential_extension((2**m) * sample_x, up_interp)
    )
    normalized = np.clip(normalized, 0.0, 1.0)
    a_grid = np.linspace(0.0, 1.0, 1001)
    sorted_normalized = np.sort(normalized)
    empirical_cdf = np.searchsorted(sorted_normalized, a_grid, side="right") / sample_count
    exact_cdf = inverse_f(a_grid)
    fig, ax = plt.subplots(figsize=(7.6, 4.8))
    ax.plot(a_grid, empirical_cdf, label=r"empirical CDF of $|F^{(4)}|/Q_4$")
    ax.plot(a_grid, exact_cdf, "--", label=r"exact target $F^{-1}(a)$")
    ax.set_xlabel("a")
    ax.set_ylabel("cumulative probability")
    ax.set_title("Derivative equimeasurability")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(HERE / "pushforward_cdf.png", dpi=180)
    plt.close(fig)

    # One log-period of the exact fractional defect.
    alpha = 0.5
    t_grid = np.linspace(0.0, 1.0, 1001)
    s_grid = 2.0**t_grid
    defect = np.array(
        [
            2 ** (alpha * (alpha - 1.0) / 2.0)
            * global_laplace_product(float(s / (2**alpha)))
            / ((float(s) ** alpha) * global_laplace_product(float(s)))
            - 1.0
            for s in s_grid
        ]
    )
    fig, ax = plt.subplots(figsize=(7.6, 4.8))
    ax.plot(t_grid, defect)
    ax.set_xlabel(r"$t=\log_2 s$")
    ax.set_ylabel(r"$E_{1/2}(2^t)-1$")
    ax.set_title("Nonzero log-periodic fractional-scaling defect")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(HERE / "fractional_defect.png", dpi=180)
    plt.close(fig)

    (HERE / "numerical_results.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    verify_and_write()
