#!/usr/bin/env python3
"""Reproducible numerical experiments for the frontier Fabius--Rvachev report.

The script studies the geometric-uniform random series

    X_q = (1-q) * sum_{n>=0} q^n U_n,       U_n ~ Uniform[0,1],

and its centered version Y_q = X_q - 1/2.  For 0<q<1, X_q is supported
on [0,1]; q=1/2 is the Fabius/Rvachev case (up to the standard affine
normalization).

Outputs
-------
figures/density_family.pdf
    Densities for q=0.3, 0.5, 0.7, 0.9; the subdyadic central plateau is
    visible for q<1/2.
figures/edgeworth_profile.pdf
    The scaled CDF correction (F_q-Phi)/(1-q), compared with its predicted
    first Edgeworth limit phi H_3 / 20.
figures/kolmogorov_scaling.pdf
    Numerical Kolmogorov distance divided by 1-q, compared with the exact
    candidate limiting constant.
figures/periodic_phase.pdf and figures/periodic_phase_normalized.pdf
    The exact centered dilation-periodic functions P_q for q=1/2, 1/3, 0.7,
    both on their native scales and normalized by the first Fourier mode.
figures/zero_count_discrepancy.pdf
    Exact reciprocal-integer zero-count discrepancy, equal to a base-B
    digit-sum term.
figures/large_deviation_rate.pdf
    Numerical Legendre transform of the limiting scaled cumulant-generating
    function, together with its quadratic and quartic central expansions.
figures/legendre_heat_scaling.pdf
    High-precision tests of the proposed Legendre heat-kernel double scaling.
data/*.csv, data/*.txt, data/*.json
    Numerical tables, Fourier checks, exact q-moment polynomial data, and an
    aggregate metadata record containing all headline error bounds.

The FFT density calculation is deterministic.  It samples the entire
characteristic function

    C_q(t) = product_n sinc((1-q)q^n t/2)

on a Fourier grid, then uses inverse FFT on a period much larger than the
support.  The very small unmultiplied tail is replaced by its quadratic
(log-sinc) approximation; the omitted fourth-order term is far below the
reported precision under the selected stopping tolerance.

No random sampling is used.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp
from scipy.integrate import cumulative_trapezoid
from scipy.special import ndtr
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss


@dataclass(frozen=True)
class DensityGrid:
    """A centered density h_q(x) and its numerical CDF on a uniform grid."""

    x: np.ndarray
    density: np.ndarray
    cdf: np.ndarray


def centered_characteristic(t: np.ndarray, q: float, tail_argument_tol: float = 1e-7) -> np.ndarray:
    """Evaluate the centered characteristic function C_q(t).

    For negative q, signs of the geometric coefficients disappear because
    sinc is even; the prefactor remains 1-q.  The function therefore also
    gives a direct numerical check of the negative-q affine duality.

    Parameters
    ----------
    t:
        Real Fourier frequencies.
    q:
        Parameter with -1 < q < 1.
    tail_argument_tol:
        Stop multiplying explicit sinc factors when the largest remaining
        argument is below this threshold.  The remaining product is replaced
        by exp(-t^2 * tail_variance / 2), the quadratic log-sinc tail.
    """
    if not (-1.0 < q < 1.0):
        raise ValueError("q must satisfy -1 < q < 1")

    t = np.asarray(t, dtype=float)
    if q == 0.0:
        # Y_0 is Uniform[-1/2,1/2].  numpy.sinc(x)=sin(pi*x)/(pi*x).
        return np.sinc(t / (2.0 * np.pi))

    phi = np.ones_like(t)
    t_max = float(np.max(np.abs(t)))
    n = 0
    while True:
        coefficient = (1.0 - q) * (q**n)
        argument = coefficient * t / 2.0
        phi *= np.sinc(argument / np.pi)
        n += 1

        next_max_argument = abs(1.0 - q) * (abs(q) ** n) * t_max / 2.0
        if next_max_argument < tail_argument_tol:
            break
        if n > 20000:
            raise RuntimeError("Characteristic-product truncation did not converge")

    # Var of the omitted centered sum.  Since log sinc(z)=-z^2/6+O(z^4),
    # its characteristic function is exp(-Var*t^2/2) to quadratic order.
    tail_variance = ((1.0 - q) ** 2) * (q ** (2 * n)) / (12.0 * (1.0 - q * q))
    phi *= np.exp(-0.5 * tail_variance * t * t)
    return phi


def fft_centered_density(q: float, period: float = 2.0, grid_size: int = 65536) -> DensityGrid:
    """Recover h_q on a centered grid by inverse FFT.

    The chosen period is larger than the support for all positive q used in
    the report.  For negative q callers should enlarge ``period`` according
    to the support width (1+|q|)/(1-|q|).
    """
    if grid_size <= 0 or grid_size & (grid_size - 1):
        raise ValueError("grid_size must be a positive power of two")

    dx = period / grid_size
    frequencies = 2.0 * np.pi * np.fft.fftfreq(grid_size, d=dx)
    characteristic = centered_characteristic(frequencies, q)
    density = np.fft.fftshift(np.fft.ifft(characteristic)).real / dx
    x = (np.arange(grid_size) - grid_size // 2) * dx

    # Only roundoff-level negative values occur for the smooth cases.  Clip
    # them before CDF integration, then normalize to exactly one numerically.
    density = np.maximum(density, 0.0)
    mass = float(np.trapezoid(density, x))
    density /= mass
    cdf = np.concatenate(([0.0], cumulative_trapezoid(density, x)))
    cdf /= cdf[-1]
    return DensityGrid(x=x, density=density, cdf=cdf)


def standard_deviation(q: float) -> float:
    """Exact standard deviation of Y_q."""
    return math.sqrt((1.0 - q) / (12.0 * (1.0 + q)))


def standardized_cumulant_4(q: float) -> float:
    """Exact excess kurtosis of the standardized law."""
    return -(6.0 / 5.0) * (1.0 - q * q) / (1.0 + q * q)


def normal_density(z: np.ndarray) -> np.ndarray:
    return np.exp(-0.5 * z * z) / math.sqrt(2.0 * math.pi)


def edgeworth_cdf(z: np.ndarray, q: float) -> np.ndarray:
    """First symmetric Edgeworth approximation for the standardized CDF."""
    phi = normal_density(z)
    h3 = z**3 - 3.0 * z
    return ndtr(z) - standardized_cumulant_4(q) * phi * h3 / 24.0


def candidate_kolmogorov_constant() -> float:
    """max_x |phi(x) H_3(x)| / 20 in closed numerical form."""
    root = math.sqrt(3.0 - math.sqrt(6.0))
    return (
        math.sqrt(6.0) * root * math.exp(-0.5 * root * root)
        / (20.0 * math.sqrt(2.0 * math.pi))
    )


def make_density_figure(figures: Path) -> None:
    """Plot the geometric-uniform densities on their natural [0,1] support."""
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for q in (0.3, 0.5, 0.7, 0.9):
        grid = fft_centered_density(q)
        natural_x = grid.x + 0.5
        mask = (natural_x >= -0.01) & (natural_x <= 1.01)
        ax.plot(natural_x[mask], grid.density[mask], label=fr"$q={q}$")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$g_q(x)$")
    ax.set_title("Geometric-uniform densities")
    ax.set_xlim(-0.01, 1.01)
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(figures / "density_family.pdf", bbox_inches="tight")
    fig.savefig(figures / "density_family.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


def edgeworth_experiments(figures: Path, data: Path) -> list[dict[str, float]]:
    """Compute CDF errors and plot the scaled first correction profile."""
    q_values = (0.70, 0.80, 0.90, 0.95, 0.97, 0.98, 0.99)
    rows: list[dict[str, float]] = []
    c_star = candidate_kolmogorov_constant()

    profile_q = (0.90, 0.95, 0.98)
    fig_profile, ax_profile = plt.subplots(figsize=(7.2, 4.6))

    for q in q_values:
        grid = fft_centered_density(q)
        sigma = standard_deviation(q)
        z = grid.x / sigma
        gaussian_cdf = ndtr(z)
        edge_cdf = edgeworth_cdf(z, q)
        kolmogorov = float(np.max(np.abs(grid.cdf - gaussian_cdf)))
        edge_error = float(np.max(np.abs(grid.cdf - edge_cdf)))
        rows.append(
            {
                "q": q,
                "kolmogorov_distance": kolmogorov,
                "kolmogorov_over_1_minus_q": kolmogorov / (1.0 - q),
                "edgeworth_sup_error": edge_error,
                "edgeworth_error_over_1_minus_q_squared": edge_error / (1.0 - q) ** 2,
                "candidate_limit": c_star,
            }
        )

        if q in profile_q:
            mask = np.abs(z) <= 4.0
            scaled = (grid.cdf[mask] - gaussian_cdf[mask]) / (1.0 - q)
            ax_profile.plot(z[mask], scaled, label=fr"$q={q}$")

    z_ref = np.linspace(-4.0, 4.0, 1601)
    limit_profile = normal_density(z_ref) * (z_ref**3 - 3.0 * z_ref) / 20.0
    ax_profile.plot(z_ref, limit_profile, linestyle="--", linewidth=2.0, label="predicted limit")
    ax_profile.set_xlabel(r"$z$")
    ax_profile.set_ylabel(r"$(G_q(z)-\Phi(z))/(1-q)$")
    ax_profile.set_title("First non-Gaussian correction")
    ax_profile.legend()
    ax_profile.grid(alpha=0.25)
    fig_profile.tight_layout()
    fig_profile.savefig(figures / "edgeworth_profile.pdf", bbox_inches="tight")
    fig_profile.savefig(figures / "edgeworth_profile.png", dpi=180, bbox_inches="tight")
    plt.close(fig_profile)

    fig_k, ax_k = plt.subplots(figsize=(7.2, 4.6))
    q_array = np.array([row["q"] for row in rows])
    ratio_array = np.array([row["kolmogorov_over_1_minus_q"] for row in rows])
    ax_k.plot(q_array, ratio_array, marker="o", label="FFT experiment")
    ax_k.axhline(c_star, linestyle="--", label=fr"candidate limit $C_\ast={c_star:.8f}$")
    ax_k.set_xlabel(r"$q$")
    ax_k.set_ylabel(r"$d_K(G_q,\Phi)/(1-q)$")
    ax_k.set_title("Kolmogorov-distance scaling")
    ax_k.legend()
    ax_k.grid(alpha=0.25)
    fig_k.tight_layout()
    fig_k.savefig(figures / "kolmogorov_scaling.pdf", bbox_inches="tight")
    fig_k.savefig(figures / "kolmogorov_scaling.png", dpi=180, bbox_inches="tight")
    plt.close(fig_k)

    with (data / "edgeworth_errors.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def kappa_kernel(x: float) -> float:
    """kappa(x)=log((1-exp(-x))/x), evaluated stably."""
    return math.log(-math.expm1(-x) / x)


def periodic_phase_value(u: float, q: float, tolerance: float = 1e-15) -> float:
    r"""Evaluate the exact dilation-periodic function

        P_q(u) = Lambda_q(q^{-u}) + L(u^2-u)/2 + T_q(q^{-u}),

    where Lambda_q(a)=sum_{n>=1} kappa(a q^n) and
    T_q(a)=sum_{m>=0} log(1-exp(-a q^{-m})).
    """
    if not (0.0 < q < 1.0):
        raise ValueError("periodic phase is implemented for 0<q<1")
    L = math.log(1.0 / q)
    a = q ** (-u)

    lam = 0.0
    x = a * q
    for _ in range(100000):
        term = kappa_kernel(x)
        lam += term
        if abs(term) < tolerance * (1.0 - q):
            break
        x *= q
    else:
        raise RuntimeError("Lambda series did not converge")

    tail = 0.0
    x = a
    for _ in range(100000):
        # log(1-exp(-x)) is stable as log(-expm1(-x)); once exp(-x) is
        # below tolerance, all later terms are negligible super-exponentially.
        exp_neg = math.exp(-x) if x < 745.0 else 0.0
        if exp_neg < tolerance:
            break
        tail += math.log1p(-exp_neg)
        x /= q
    else:
        raise RuntimeError("forward tail did not converge")

    return lam + 0.5 * L * (u * u - u) + tail


def periodic_phase_experiments(figures: Path, data: Path) -> list[dict[str, float]]:
    """Plot periodic phases and validate the first Fourier coefficients."""
    q_values = (0.5, 1.0 / 3.0, 0.7)
    sample_count = 1024
    u = np.arange(sample_count) / sample_count
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    fig_normalized, ax_normalized = plt.subplots(figsize=(7.2, 4.6))
    checks: list[dict[str, float]] = []
    mp.mp.dps = 50

    for q in q_values:
        values = np.array([periodic_phase_value(float(ui), q) for ui in u])
        centered = values - float(np.mean(values))

        # numpy.fft.fft uses the same e^{-2 pi i k j/N} convention as the
        # Fourier coefficient integral in the report.
        coefficients = np.fft.fft(values) / sample_count
        first_harmonic_scale = 2.0 * abs(coefficients[1])
        ax.plot(u, centered, label=fr"$q={q:.6g}$")
        ax_normalized.plot(
            u, centered / first_harmonic_scale, label=fr"$q={q:.6g}$"
        )
        L = math.log(1.0 / q)
        for k in (1, 2, 3):
            chi = 2j * mp.pi * k / L
            predicted = -mp.gamma(-chi) * mp.zeta(1 - chi) / L
            numerical = complex(coefficients[k])
            predicted_complex = complex(predicted)
            abs_error = abs(numerical - predicted_complex)
            checks.append(
                {
                    "q": q,
                    "k": k,
                    "numerical_real": numerical.real,
                    "numerical_imag": numerical.imag,
                    "predicted_real": predicted_complex.real,
                    "predicted_imag": predicted_complex.imag,
                    "absolute_error": abs_error,
                }
            )

    ax.set_xlabel(r"$u$")
    ax.set_ylabel(r"$P_q(u)-\int_0^1P_q(v)\,dv$")
    ax.set_title("Exact dilation-periodic endpoint phase (actual amplitude)")
    ax.set_xlim(0.0, 1.0)
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(figures / "periodic_phase.pdf", bbox_inches="tight")
    fig.savefig(figures / "periodic_phase.png", dpi=180, bbox_inches="tight")
    plt.close(fig)

    ax_normalized.set_xlabel(r"$u$")
    ax_normalized.set_ylabel("centered phase / first-harmonic amplitude")
    ax_normalized.set_title("Normalized dilation-periodic endpoint phase")
    ax_normalized.set_xlim(0.0, 1.0)
    ax_normalized.legend()
    ax_normalized.grid(alpha=0.25)
    fig_normalized.tight_layout()
    fig_normalized.savefig(figures / "periodic_phase_normalized.pdf", bbox_inches="tight")
    fig_normalized.savefig(
        figures / "periodic_phase_normalized.png", dpi=180, bbox_inches="tight"
    )
    plt.close(fig_normalized)

    with (data / "periodic_fourier_check.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(checks[0].keys()))
        writer.writeheader()
        writer.writerows(checks)
    return checks


def base_digit_sum(number: int, base: int) -> int:
    """Sum the digits of a nonnegative integer in a prescribed base."""
    if number < 0 or base < 2:
        raise ValueError("number must be nonnegative and base at least two")
    total = 0
    while number:
        total += number % base
        number //= base
    return total


def reciprocal_zero_count(M: int, base: int) -> int:
    r"""Count positive zeros through rho=c_B M, with multiplicity, for q=1/B.

    The theorem in the report gives

        N^+_{1/B}(c_B M) = (B M - s_B(M))/(B-1).
    """
    return (base * M - base_digit_sum(M, base)) // (base - 1)


def zero_count_experiments(figures: Path, data: Path) -> list[dict[str, float | int]]:
    """Verify and plot the exact base-digit zero-count discrepancy."""
    maximum_M = 2048
    rows: list[dict[str, float | int]] = []
    fig, ax = plt.subplots(figsize=(7.2, 4.6))

    for base in (2, 3):
        M_values = np.arange(1, maximum_M + 1)
        exact = np.array([reciprocal_zero_count(int(M), base) for M in M_values])
        main = base * M_values / (base - 1.0)
        discrepancy = exact - main
        ax.plot(M_values, discrepancy, linewidth=0.8, label=fr"$B={base}$")

        # Independent floor-sum verification of every row.
        for M, count, delta in zip(M_values, exact, discrepancy, strict=True):
            floor_sum = 0
            divisor = 1
            while divisor <= M:
                floor_sum += int(M // divisor)
                divisor *= base
            if floor_sum != count:
                raise AssertionError("digit-sum and floor-sum zero counts disagree")
            rows.append(
                {
                    "base": base,
                    "M": int(M),
                    "zero_count": int(count),
                    "main_term": float(base * M / (base - 1.0)),
                    "discrepancy": float(delta),
                    "digit_sum": base_digit_sum(int(M), base),
                }
            )

    ax.set_xlabel(r"$M$")
    ax.set_ylabel(r"$N^+_{1/B}(c_BM)-BM/(B-1)$")
    ax.set_title("Zero-count fluctuations are digit sums")
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(figures / "zero_count_discrepancy.pdf", bbox_inches="tight")
    fig.savefig(figures / "zero_count_discrepancy.png", dpi=180, bbox_inches="tight")
    plt.close(fig)

    with (data / "zero_counts.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def q_moment_polynomials(data: Path, maximum_n: int = 30, full_coefficients_through: int = 20) -> list[dict[str, int | bool]]:
    r"""Generate normalized even-moment polynomials and test positivity.

    Let V_j be iid Uniform[-1,1], S_q=sum q^j V_j, r=q^2, and
    m_n(r)=E[S_q^{2n}].  Define

        P_n(r)=(r;r)_n m_n(r),
        Q_n(r)=(2n+1)!! P_n(r).

    The recurrence used here is polynomial from the outset:

      P_n = sum_{k=1}^n binom(2n,2k)/(2k+1) * r^{n-k} P_{n-k}
            * product_{j=n-k+1}^{n-1}(1-r^j).

    The report conjectures that every coefficient of Q_n is a positive
    integer.  This script checks the statement through ``maximum_n``.
    """
    r = sp.symbols("r")
    P: list[sp.Poly] = [sp.Poly(1, r, domain=sp.QQ)]
    summaries: list[dict[str, int | bool]] = []
    coefficient_rows: list[dict[str, int | str]] = []
    displayed: list[str] = []

    for n in range(1, maximum_n + 1):
        polynomial = sp.Poly(0, r, domain=sp.QQ)
        for k in range(1, n + 1):
            factor = sp.Poly(r ** (n - k), r, domain=sp.QQ)
            for j in range(n - k + 1, n):
                factor *= sp.Poly(1 - r**j, r, domain=sp.QQ)
            multiplier = sp.Rational(sp.binomial(2 * n, 2 * k), 2 * k + 1)
            polynomial += P[n - k] * factor * multiplier
        P.append(polynomial)

        Q = polynomial.mul_ground(sp.factorial2(2 * n + 1))
        coefficients_descending = Q.all_coeffs()
        all_integral = all(coefficient.q == 1 for coefficient in coefficients_descending)
        all_positive = all(coefficient > 0 for coefficient in coefficients_descending)
        expected_degree = n * (n - 1) // 2
        summaries.append(
            {
                "n": n,
                "degree": int(Q.degree()),
                "expected_triangular_degree": expected_degree,
                "coefficient_count": len(coefficients_descending),
                "all_integral": all_integral,
                "all_strictly_positive": all_positive,
                "constant_coefficient": int(Q.TC()),
                "leading_coefficient": int(Q.LC()),
                "sum_of_coefficients_Qn_at_1": int(sum(coefficients_descending)),
            }
        )

        if n <= full_coefficients_through:
            for (power,), coefficient in Q.terms():
                coefficient_rows.append(
                    {"n": n, "power_of_r": int(power), "coefficient": str(coefficient)}
                )
        if n <= 6:
            displayed.append(f"Q_{n}(r) = {sp.sstr(Q.as_expr())}")

    with (data / "moment_polynomial_summary.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(summaries[0].keys()))
        writer.writeheader()
        writer.writerows(summaries)
    with (data / "moment_polynomial_coefficients.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(coefficient_rows[0].keys()))
        writer.writeheader()
        writer.writerows(coefficient_rows)
    (data / "first_q_moment_polynomials.txt").write_text("\n".join(displayed) + "\n", encoding="utf-8")
    return summaries


def duality_check(data: Path) -> list[dict[str, float]]:
    """Check C_{-r}(t)=C_r(c_r t) on a deterministic frequency grid."""
    rows: list[dict[str, float]] = []
    t = np.linspace(-120.0, 120.0, 24001)
    for r in (0.2, 0.4, 0.7, 0.9):
        c = (1.0 + r) / (1.0 - r)
        left = centered_characteristic(t, -r)
        right = centered_characteristic(c * t, r)
        rows.append(
            {
                "r": r,
                "affine_scale": c,
                "max_absolute_characteristic_error": float(np.max(np.abs(left - right))),
            }
        )
    with (data / "negative_q_duality_check.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def derivative_norm_table(data: Path, maximum_m: int = 8) -> None:
    """Write exact subdyadic derivative-norm predictions for sample q values."""
    rows: list[dict[str, float | int]] = []
    for q in (0.25, 1.0 / 3.0, 0.5):
        for m in range(maximum_m + 1):
            norm = (1.0 - q) ** (-(m + 1)) * q ** (-m * (m + 1) / 2.0)
            plateau_half_width = 0.5 * (q**m) * max(1.0 - 2.0 * q, 0.0)
            rows.append(
                {
                    "q": q,
                    "derivative_order_m": m,
                    "predicted_sup_norm": norm,
                    "peak_or_plateau_half_width": plateau_half_width,
                }
            )
    with (data / "subdyadic_derivative_norms.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)




def _log_sinhc_positive(z: np.ndarray) -> np.ndarray:
    """Stable log(sinh(z)/z) for a nonnegative numpy array."""
    z = np.asarray(z, dtype=float)
    result = np.empty_like(z)
    small = z < 1e-4
    zs = z[small]
    result[small] = zs**2 / 6.0 - zs**4 / 180.0 + zs**6 / 2835.0
    large = ~small
    zl = z[large]
    result[large] = zl - np.log(2.0 * zl) + np.log1p(-np.exp(-2.0 * zl))
    return result


def _half_coth_minus_reciprocal(z: np.ndarray) -> np.ndarray:
    """Stable (coth(z)-1/z)/2 for nonnegative z."""
    z = np.asarray(z, dtype=float)
    result = np.empty_like(z)
    small = z < 1e-4
    zs = z[small]
    result[small] = 0.5 * (zs / 3.0 - zs**3 / 45.0 + 2.0 * zs**5 / 945.0)
    medium = (~small) & (z < 350.0)
    zm = z[medium]
    result[medium] = 0.5 * (1.0 + 2.0 / np.expm1(2.0 * zm) - 1.0 / zm)
    large = z >= 350.0
    zl = z[large]
    result[large] = 0.5 * (1.0 - 1.0 / zl)
    return result


def large_deviation_experiment(figures: Path, data: Path) -> list[dict[str, float]]:
    r"""Compute the q->1 large-deviation rate function.

    For the centered variable X_q-1/2 and speed 1/(1-q), the limiting scaled
    cumulant-generating function is

      Lambda(theta) = integral_0^1 log(sinh(theta*u/2)/(theta*u/2)) du/u.

    The rate function is its Legendre transform.  Gauss--Legendre quadrature
    and monotone root finding are used; no simulation is involved.
    """
    nodes, weights = leggauss(360)
    u = (nodes + 1.0) / 2.0
    weights = weights / 2.0

    def scaled_cgf(theta: float) -> float:
        if theta == 0.0:
            return 0.0
        z = abs(theta) * u / 2.0
        return float(np.sum(weights * _log_sinhc_positive(z) / u))

    def scaled_cgf_derivative(theta: float) -> float:
        if theta == 0.0:
            return 0.0
        sign = 1.0 if theta > 0 else -1.0
        z = abs(theta) * u / 2.0
        return sign * float(np.sum(weights * _half_coth_minus_reciprocal(z)))

    positive_y = np.concatenate(
        [np.linspace(0.0, 0.40, 81), np.linspace(0.405, 0.49, 18)]
    )
    rows: list[dict[str, float]] = []
    positive_rate: list[float] = []
    for y in positive_y:
        if y == 0.0:
            theta = 0.0
            rate = 0.0
        else:
            upper = 1.0
            while scaled_cgf_derivative(upper) < y:
                upper *= 2.0
            theta = brentq(
                lambda value: scaled_cgf_derivative(value) - y,
                0.0,
                upper,
                xtol=1e-13,
                rtol=1e-13,
            )
            rate = theta * y - scaled_cgf(theta)
        positive_rate.append(rate)
        rows.append(
            {
                "centered_position_y": float(y),
                "saddle_theta": float(theta),
                "rate_I": float(rate),
                "quadratic_12_y_squared": float(12.0 * y * y),
            }
        )

    y_full = np.concatenate((-positive_y[:0:-1], positive_y))
    rate_full = np.concatenate((np.array(positive_rate[:0:-1]), np.array(positive_rate)))
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ax.plot(y_full, rate_full, label=r"$I(1/2+y)$")
    ax.plot(y_full, 12.0 * y_full * y_full, linestyle="--", label=r"quadratic core $12y^2$")
    ax.set_xlabel(r"$y=x-1/2$")
    ax.set_ylabel("rate")
    ax.set_title(r"Large-deviation bridge as $q\uparrow1$")
    ax.set_xlim(-0.5, 0.5)
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(figures / "large_deviation_rate.pdf", bbox_inches="tight")
    fig.savefig(figures / "large_deviation_rate.png", dpi=180, bbox_inches="tight")
    plt.close(fig)

    with (data / "large_deviation_rate.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def high_precision_uniform_series_moments(q: mp.mpf, maximum_n: int) -> list[mp.mpf]:
    """Return m_n=E[(sum q^j V_j)^(2n)] for V_j~Uniform[-1,1]."""
    r = q * q
    moments = [mp.mpf(1)]
    for n in range(1, maximum_n + 1):
        rhs = mp.mpf(0)
        for k in range(1, n + 1):
            rhs += (
                mp.binomial(2 * n, 2 * k)
                * r ** (n - k)
                * moments[n - k]
                / (2 * k + 1)
            )
        moments.append(rhs / (1 - r**n))
    return moments


def normalized_legendre_expectation(
    q: mp.mpf, m: int, moments: list[mp.mpf]
) -> mp.mpf:
    r"""Compute E[P_{2m}(2X_q-1)] / P_{2m}(0) at high precision.

    Direct quadrature is badly conditioned when m is moderately large: the
    expectation is a cancellation of large polynomial terms.  The exact
    monomial expansion of P_{2m}, combined with the moment recurrence, is
    stable when evaluated with sufficient arbitrary precision.
    """
    expectation = mp.mpf(0)
    for j in range(m + 1):
        coefficient = (
            (-1) ** (m - j)
            * mp.factorial(2 * m + 2 * j)
            / (
                2 ** (2 * m)
                * mp.factorial(m - j)
                * mp.factorial(m + j)
                * mp.factorial(2 * j)
            )
        )
        expectation += coefficient * (1 - q) ** (2 * j) * moments[j]
    value_at_zero = (-1) ** m * mp.binomial(2 * m, m) / 4**m
    return expectation / value_at_zero


def legendre_heat_experiment(figures: Path, data: Path) -> list[dict[str, float | int]]:
    r"""Test the proposed Legendre heat-kernel double scaling.

    With v_q=Var(2X_q-1), the conjectured limit is

      E[P_{2m}(2X_q-1)] / P_{2m}(0)
          -> exp(-tau^2/2),
      tau=(2m+1/2)*sqrt(v_q),

    as q approaches one and m grows so that tau remains bounded.
    """
    mp.mp.dps = 180
    q_values = (mp.mpf("0.90"), mp.mpf("0.95"), mp.mpf("0.98"), mp.mpf("0.99"))
    tau_cap = mp.mpf("3.1")
    rows: list[dict[str, float | int]] = []
    fig, ax = plt.subplots(figsize=(7.2, 4.6))

    for q in q_values:
        variance = (1 - q) / (3 * (1 + q))
        maximum_m = int(mp.floor((tau_cap / mp.sqrt(variance) - mp.mpf("0.5")) / 2))
        moments = high_precision_uniform_series_moments(q, maximum_m)
        tau_values: list[float] = []
        ratios: list[float] = []
        for m in range(1, maximum_m + 1):
            tau = (2 * m + mp.mpf("0.5")) * mp.sqrt(variance)
            ratio = normalized_legendre_expectation(q, m, moments)
            limit = mp.e ** (-tau * tau / 2)
            tau_values.append(float(tau))
            ratios.append(float(ratio))
            rows.append(
                {
                    "q": float(q),
                    "m": m,
                    "tau": float(tau),
                    "normalized_legendre_expectation": float(ratio),
                    "heat_kernel_prediction": float(limit),
                    "absolute_error": float(abs(ratio - limit)),
                }
            )
        ax.plot(tau_values, ratios, marker="o", markersize=3, label=fr"$q={float(q):.2f}$")

    tau_reference = np.linspace(0.0, float(tau_cap), 1000)
    ax.plot(
        tau_reference,
        np.exp(-0.5 * tau_reference * tau_reference),
        linestyle="--",
        linewidth=2.0,
        label=r"$e^{-\tau^2/2}$",
    )
    ax.set_xlabel(r"$\tau=(2m+1/2)\sqrt{v_q}$")
    ax.set_ylabel(r"$\mathbb{E}P_{2m}(2X_q-1)/P_{2m}(0)$")
    ax.set_title("Legendre heat-kernel double scaling")
    ax.legend()
    ax.grid(alpha=0.25)
    fig.tight_layout()
    fig.savefig(figures / "legendre_heat_scaling.pdf", bbox_inches="tight")
    fig.savefig(figures / "legendre_heat_scaling.png", dpi=180, bbox_inches="tight")
    plt.close(fig)

    with (data / "legendre_heat_scaling.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Directory containing figures/ and data/ (default: project root)",
    )
    args = parser.parse_args()
    output_root = args.output_root.resolve()
    figures = output_root / "figures"
    data = output_root / "data"
    figures.mkdir(parents=True, exist_ok=True)
    data.mkdir(parents=True, exist_ok=True)

    make_density_figure(figures)
    edge_rows = edgeworth_experiments(figures, data)
    phase_rows = periodic_phase_experiments(figures, data)
    zero_rows = zero_count_experiments(figures, data)
    moment_rows = q_moment_polynomials(data)
    duality_rows = duality_check(data)
    derivative_norm_table(data)
    legendre_rows = legendre_heat_experiment(figures, data)
    large_deviation_rows = large_deviation_experiment(figures, data)

    metadata = {
        "candidate_kolmogorov_constant": candidate_kolmogorov_constant(),
        "largest_q_in_edgeworth_table": max(row["q"] for row in edge_rows),
        "largest_periodic_fourier_absolute_error": max(row["absolute_error"] for row in phase_rows),
        "zero_count_rows": len(zero_rows),
        "moment_positivity_checked_through_n": max(row["n"] for row in moment_rows),
        "all_moment_checks_passed": all(
            row["all_integral"] and row["all_strictly_positive"]
            and row["degree"] == row["expected_triangular_degree"]
            for row in moment_rows
        ),
        "largest_negative_q_duality_error": max(
            row["max_absolute_characteristic_error"] for row in duality_rows
        ),
        "largest_legendre_heat_error_q_0_99": max(
            row["absolute_error"] for row in legendre_rows if row["q"] == 0.99
        ),
        "large_deviation_rate_at_y_0_49": max(
            row["rate_I"] for row in large_deviation_rows
        ),
    }
    (data / "experiment_metadata.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(metadata, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
