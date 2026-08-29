#!/usr/bin/env python3
"""Reproducible experiments for Atomic Functions Beyond the Critical Dyadic Case.

The script regenerates every figure and CSV table cited by the LaTeX report.  It uses
only NumPy, Matplotlib, and mpmath.  The random seed is fixed, and the truncation of the
random series is chosen from a deterministic worst-case tail bound.

Usage
-----
    python experiments.py --output .

The output directory will receive ``figures/`` and ``data/`` subdirectories.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Callable, Iterable

import matplotlib

# Use a deterministic, noninteractive backend so the script works on servers and in CI.
matplotlib.use("Agg")
matplotlib.rcParams["pdf.fonttype"] = 42
matplotlib.rcParams["ps.fonttype"] = 42

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

SEED = 20260828


def save_figure(fig: plt.Figure, stem: Path) -> None:
    """Save one Matplotlib figure in vector and raster form."""
    stem.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".png"), dpi=220, bbox_inches="tight")
    plt.close(fig)


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, object]]) -> None:
    """Write dictionaries to a UTF-8 CSV with a stable column order."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def sinc(x: np.ndarray | float) -> np.ndarray | float:
    """Unnormalized sinc, sin(x)/x, evaluated stably through NumPy's normalized sinc."""
    return np.sinc(np.asarray(x) / np.pi)


def phi_a(t: np.ndarray, a: float, tail_argument: float = 1.0e-8) -> np.ndarray:
    """Evaluate Phi_a(t) = product_{j>=1} sinc(t a^{-j}) on a NumPy grid.

    The product is stopped once the largest omitted argument is below ``tail_argument``.
    The logarithm of the omitted tail is then O(tail_argument**2/(a**2-1)), far below
    the plotting and quadrature accuracy used here.
    """
    t = np.asarray(t, dtype=float)
    max_t = float(np.max(np.abs(t))) if t.size else 0.0
    if max_t == 0.0:
        return np.ones_like(t)
    j_max = max(1, int(math.ceil(math.log(max_t / tail_argument, a))))
    product = np.ones_like(t)
    scale = 1.0 / a
    for _ in range(1, j_max + 1):
        product *= sinc(t * scale)
        scale /= a
    return product


def generate_gap_hierarchy(fig_dir: Path, data_dir: Path, a: float = 2.6, depth: int = 8) -> None:
    """Plot the exact generation/degree hierarchy of complementary Cantor gaps."""
    b = 1.0 / (a - 1.0)
    b1 = (a - 2.0) / (a * (a - 1.0))
    gaps: list[tuple[float, float]] = [(-b1, b1)]
    rows: list[dict[str, object]] = []

    fig, ax = plt.subplots(figsize=(10.2, 5.7))
    for n in range(depth + 1):
        for index, (left, right) in enumerate(gaps):
            ax.plot([left, right], [n, n], linewidth=4.0, solid_capstyle="butt")
            rows.append(
                {
                    "base_a": a,
                    "generation": n,
                    "gap_index": index,
                    "left": left,
                    "right": right,
                    "length": right - left,
                    "exact_polynomial_degree": n,
                }
            )
        next_gaps: list[tuple[float, float]] = []
        for left, right in gaps:
            next_gaps.append(((left - 1.0) / a, (right - 1.0) / a))
            next_gaps.append(((left + 1.0) / a, (right + 1.0) / a))
        gaps = sorted(next_gaps)

    ax.set_xlim(-b, b)
    ax.set_ylim(depth + 0.7, -0.7)
    ax.set_xlabel("x")
    ax.set_ylabel("gap generation = exact polynomial degree")
    ax.set_title(f"Complementary gap hierarchy for a={a:g}")
    ax.grid(True, axis="x", alpha=0.3)
    save_figure(fig, fig_dir / "gap_hierarchy_a_2_6")
    write_csv(
        data_dir / "gap_hierarchy_a_2_6.csv",
        ["base_a", "generation", "gap_index", "left", "right", "length", "exact_polynomial_degree"],
        rows,
    )


def tube_volume(eps: np.ndarray, a: float) -> np.ndarray:
    """Exact inner tube volume from the gap-length geometric series."""
    ell0 = 2.0 * (a - 2.0) / (a * (a - 1.0))
    x = np.log(ell0 / (2.0 * eps)) / math.log(a)
    n = np.floor(x).astype(int)
    return 2.0 * eps * (2.0 ** (n + 1) - 1.0) + ell0 * (2.0 / a) ** (n + 1) / (1.0 - 2.0 / a)


def tube_profile(theta: np.ndarray, a: float) -> np.ndarray:
    """The one-periodic limiting profile in the exact tube formula."""
    ell0 = 2.0 * (a - 2.0) / (a * (a - 1.0))
    d = math.log(2.0) / math.log(a)
    return ell0**d * (
        2.0 ** (2.0 - d - theta)
        + 2.0 ** (1.0 - d) * a ** ((d - 1.0) * (1.0 - theta)) / (1.0 - 2.0 / a)
    )


def generate_tube_oscillation(fig_dir: Path, data_dir: Path, a: float = 3.0) -> None:
    """Plot exact normalized tube volume against its logarithmic-periodic profile."""
    ell0 = 2.0 * (a - 2.0) / (a * (a - 1.0))
    d = math.log(2.0) / math.log(a)
    x = np.linspace(0.02, 12.0, 7000)
    eps = 0.5 * ell0 * a ** (-x)
    normalized = eps ** (d - 1.0) * tube_volume(eps, a)
    profile = tube_profile(np.mod(x, 1.0), a)

    fig, ax = plt.subplots(figsize=(10.2, 5.6))
    ax.plot(x, normalized, label="exact normalized tube volume")
    ax.plot(x, profile, linestyle="--", label="one-periodic profile")
    ax.set_xlabel(r"$\log_a(\ell_0/(2\varepsilon))$")
    ax.set_ylabel(r"$\varepsilon^{D_a-1}V_a(\varepsilon)$")
    ax.set_title(f"Log-periodic tube oscillation for a={a:g}")
    ax.legend()
    ax.grid(True, alpha=0.3)
    save_figure(fig, fig_dir / "tube_oscillation_a_3")

    sample = np.linspace(0.1, 10.0, 200)
    sample_eps = 0.5 * ell0 * a ** (-sample)
    rows = [
        {
            "base_a": a,
            "log_scale_x": float(xx),
            "epsilon": float(ee),
            "normalized_tube_volume": float(nn),
            "periodic_profile": float(pp),
            "difference": float(nn - pp),
        }
        for xx, ee, nn, pp in zip(
            sample,
            sample_eps,
            sample_eps ** (d - 1.0) * tube_volume(sample_eps, a),
            tube_profile(np.mod(sample, 1.0), a),
        )
    ]
    write_csv(
        data_dir / "tube_oscillation_a_3.csv",
        ["base_a", "log_scale_x", "epsilon", "normalized_tube_volume", "periodic_profile", "difference"],
        rows,
    )


def generate_degree_critical_limit(fig_dir: Path, data_dir: Path) -> None:
    """Show convergence of the rescaled geometric degree law to Exp(1)."""
    bases = [3.0, 2.5, 2.2, 2.05]
    x = np.linspace(0.0, 5.0, 1800)
    fig, ax = plt.subplots(figsize=(10.2, 5.6))
    rows: list[dict[str, object]] = []

    for a in bases:
        p = (a - 2.0) / a
        n = np.floor(x / p).astype(int)
        cdf = 1.0 - (1.0 - p) ** (n + 1)
        ax.plot(x, cdf, label=f"a={a:g}")
        sup_error = float(np.max(np.abs(cdf - (1.0 - np.exp(-x)))))
        rows.append({"base_a": a, "p_a": p, "sup_grid_error_to_exp_cdf": sup_error})

    ax.plot(x, 1.0 - np.exp(-x), linestyle="--", linewidth=2.0, label="Exp(1) limit")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$P(p_aN_a\leq x)$")
    ax.set_title("Critical local-degree limit")
    ax.legend()
    ax.grid(True, alpha=0.3)
    save_figure(fig, fig_dir / "degree_critical_limit")
    write_csv(data_dir / "degree_critical_limit.csv", ["base_a", "p_a", "sup_grid_error_to_exp_cdf"], rows)


def kappa_kernel(u: np.ndarray) -> np.ndarray:
    """kappa(u)=log((1-exp(-u))/u), with stable cancellation at the origin."""
    u = np.asarray(u, dtype=float)
    return np.log((-np.expm1(-u)) / u)


def lambda_a(u: np.ndarray, a: float, small_argument: float = 1.0e-13) -> np.ndarray:
    """Compute Lambda_a(u)=sum_{j>=1} kappa(u a^{-j})."""
    u = np.asarray(u, dtype=float)
    maximum = float(np.max(u))
    j_max = max(1, int(math.ceil(math.log(maximum / small_argument, a))))
    total = np.zeros_like(u)
    scale = 1.0 / a
    for _ in range(1, j_max + 1):
        total += kappa_kernel(u * scale)
        scale /= a
    return total


def r_a(x: np.ndarray, a: float, exp_cutoff: float = 42.0) -> np.ndarray:
    """Compute R_a(x)=sum_{n>=0} log(1-exp(-a^(x+n)))."""
    x = np.asarray(x, dtype=float)
    # For x in the ranges used here, 64 terms is excessive but harmless.  Break once
    # every exponential argument is large enough that the next term is below roundoff.
    total = np.zeros_like(x)
    n = 0
    while True:
        argument = a ** (x + n)
        total += np.log1p(-np.exp(-argument))
        if float(np.min(argument)) > exp_cutoff:
            break
        n += 1
        if n > 200:
            raise RuntimeError("R_a tail did not converge")
    return total


def periodic_correction(x: np.ndarray, a: float) -> np.ndarray:
    """Exact periodic correction P_a(x) from the report."""
    x = np.asarray(x, dtype=float)
    loga = math.log(a)
    return lambda_a(a**x, a) + 0.5 * loga * x**2 - 0.5 * loga * x + r_a(x, a)


def generate_periodic_correction(fig_dir: Path, data_dir: Path) -> None:
    """Plot centered periodic corrections and audit periodicity/Gamma-zeta modes."""
    bases = [1.2, 1.5, 2.0, 2.6, 3.0, 5.0]
    x = np.linspace(0.0, 1.0, 4097)
    fig, ax = plt.subplots(figsize=(10.2, 5.8))
    periodicity_rows: list[dict[str, object]] = []
    fourier_rows: list[dict[str, object]] = []

    for a in bases:
        values = periodic_correction(x, a)
        centered = values - np.trapezoid(values, x)
        ax.plot(x, centered, label=f"a={a:g}")
        residual_grid = np.linspace(-0.25, 1.25, 2001)
        residual = periodic_correction(residual_grid + 1.0, a) - periodic_correction(residual_grid, a)
        periodicity_rows.append(
            {
                "base_a": a,
                "max_abs_periodicity_residual": float(np.max(np.abs(residual))),
                "rms_periodicity_residual": float(np.sqrt(np.mean(residual**2))),
            }
        )

    ax.set_xlabel("x modulo 1")
    ax.set_ylabel(r"$P_a(x)-\overline{P}_a$")
    ax.set_title("General-base periodic correction")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.3)
    save_figure(fig, fig_dir / "periodic_correction_bases")
    write_csv(
        data_dir / "periodicity_residuals.csv",
        ["base_a", "max_abs_periodicity_residual", "rms_periodicity_residual"],
        periodicity_rows,
    )

    # High-resolution trapezoidal Fourier audit.  The endpoint is omitted because the
    # periodic trapezoidal rule on a uniform half-open grid is spectrally accurate here.
    mp.mp.dps = 60
    m = 2**16
    xf = np.arange(m, dtype=float) / m
    for a in [1.5, 2.0, 2.6, 3.0]:
        values = periodic_correction(xf, a)
        values -= np.mean(values)
        loga = math.log(a)
        for k in [1, 2, 3]:
            numerical = np.mean(values * np.exp(-2j * np.pi * k * xf))
            chi = 2j * mp.pi * k / mp.log(a)
            formula_mp = -mp.gamma(-chi) * mp.zeta(1 - chi) / mp.log(a)
            formula = complex(formula_mp)
            error = numerical - formula
            fourier_rows.append(
                {
                    "base_a": a,
                    "mode_k": k,
                    "numerical_real": numerical.real,
                    "numerical_imag": numerical.imag,
                    "formula_real": formula.real,
                    "formula_imag": formula.imag,
                    "abs_error": abs(error),
                    "relative_error": abs(error) / max(abs(formula), 1.0e-300),
                }
            )
    write_csv(
        data_dir / "gamma_zeta_fourier_validation.csv",
        [
            "base_a",
            "mode_k",
            "numerical_real",
            "numerical_imag",
            "formula_real",
            "formula_imag",
            "abs_error",
            "relative_error",
        ],
        fourier_rows,
    )


def bernoulli_cumulants(a: float, max_order: int) -> np.ndarray:
    """Return cumulants kappa_0,...,kappa_max_order for X_a."""
    cumulants = np.zeros(max_order + 1, dtype=float)
    for m in range(1, max_order // 2 + 1):
        order = 2 * m
        b = float(mp.bernoulli(order))
        cumulants[order] = 2.0**order * b / (order * (a**order - 1.0))
    return cumulants


def moments_from_cumulants(cumulants: np.ndarray) -> np.ndarray:
    """Complete Bell-polynomial recurrence for raw moments."""
    max_order = len(cumulants) - 1
    moments = np.zeros(max_order + 1, dtype=float)
    moments[0] = 1.0
    for n in range(1, max_order + 1):
        moments[n] = sum(
            math.comb(n - 1, j - 1) * cumulants[j] * moments[n - j] for j in range(1, n + 1)
        )
    return moments


def generate_moment_and_gaussian_audits(fig_dir: Path, data_dir: Path, a: float = 2.6) -> None:
    """Generate Bell-moment Monte Carlo validation and the Gaussian cumulant plot."""
    # Gaussian standardized fourth cumulant.
    a_grid = np.linspace(1.0005, 1.28, 900)
    exact = -(6.0 / 5.0) * (a_grid**2 - 1.0) / (a_grid**2 + 1.0)
    first = -(6.0 / 5.0) * (a_grid - 1.0)
    fig, ax = plt.subplots(figsize=(10.2, 5.6))
    ax.plot(a_grid - 1.0, exact, label="exact standardized fourth cumulant")
    ax.plot(a_grid - 1.0, first, linestyle="--", label="first asymptotic term")
    ax.set_xlabel(r"$a-1$")
    ax.set_ylabel(r"$\lambda_4(a)$")
    ax.set_title("Gaussian-limit cumulant scaling")
    ax.legend()
    ax.grid(True, alpha=0.3)
    save_figure(fig, fig_dir / "gaussian_cumulant_limit")

    max_order = 10
    exact_moments = moments_from_cumulants(bernoulli_cumulants(a, max_order))
    rng = np.random.default_rng(SEED)
    sample_count = 250_000
    tail_tolerance = 1.0e-12
    j_max = int(math.ceil(math.log(1.0 / (tail_tolerance * (a - 1.0)), a)))
    samples = np.zeros(sample_count, dtype=float)
    for j in range(1, j_max + 1):
        samples += a ** (-j) * rng.uniform(-1.0, 1.0, sample_count)

    rows: list[dict[str, object]] = []
    for order in range(0, max_order + 1, 2):
        empirical = float(np.mean(samples**order)) if order else 1.0
        exact_value = float(exact_moments[order])
        rows.append(
            {
                "base_a": a,
                "sample_count": sample_count,
                "random_seed": SEED,
                "truncation_index_J": j_max,
                "deterministic_tail_bound": a ** (-j_max) / (a - 1.0),
                "moment_order": order,
                "exact_Bell_moment": exact_value,
                "Monte_Carlo_moment": empirical,
                "absolute_error": empirical - exact_value,
                "relative_error": (empirical - exact_value) / exact_value if exact_value else 0.0,
            }
        )
    write_csv(
        data_dir / "moment_validation_a_2_6.csv",
        [
            "base_a",
            "sample_count",
            "random_seed",
            "truncation_index_J",
            "deterministic_tail_bound",
            "moment_order",
            "exact_Bell_moment",
            "Monte_Carlo_moment",
            "absolute_error",
            "relative_error",
        ],
        rows,
    )


def generate_geometry_norm_table(data_dir: Path) -> None:
    """Tabulate exact geometry, norm multipliers, and spectral moments."""
    rows: list[dict[str, object]] = []
    for a in [2.0, 2.1, 2.6, 3.0, 5.0]:
        b = 1.0 / (a - 1.0)
        for n in range(0, 9):
            c = (a * a / 2.0) ** n * a ** (n * (n - 1) / 2.0)
            r = (2.0 / a) ** n
            rows.append(
                {
                    "base_a": a,
                    "derivative_order_n": n,
                    "support_radius_b": b,
                    "active_support_measure": 2.0 * b * r,
                    "thinning_factor_r": r,
                    "copy_amplitude_c": c,
                    "L1_norm": a ** (n * (n + 1) / 2.0),
                    "Linf_norm": a ** ((n + 1) * (n + 2) / 2.0) / 2.0 ** (n + 1),
                    "L2_multiplier": c * math.sqrt(r),
                    "normalized_spectral_moment": a ** (n * (n + 2)) / 2.0**n,
                }
            )
    write_csv(
        data_dir / "geometry_and_derivative_norms.csv",
        [
            "base_a",
            "derivative_order_n",
            "support_radius_b",
            "active_support_measure",
            "thinning_factor_r",
            "copy_amplitude_c",
            "L1_norm",
            "Linf_norm",
            "L2_multiplier",
            "normalized_spectral_moment",
        ],
        rows,
    )


def generate_spectral_twin(fig_dir: Path, data_dir: Path, a: float = 2.6) -> None:
    """Plot and numerically audit the sinc-product/lognormal moment twins."""
    # The variable y=log z is numerically natural.  For the spectral law,
    # p_Y(y)=exp(y/2) Phi_a(exp(y/2))^2 / I_a.
    y = np.linspace(-35.0, 28.0, 180_001)
    t = np.exp(0.5 * y)
    phi = phi_a(t, a)
    unnormalized = np.exp(0.5 * y) * phi**2
    i_a = float(np.trapezoid(unnormalized, y))
    spectral_y = unnormalized / i_a

    loga = math.log(a)
    mu = 2.0 * loga - math.log(2.0)
    sigma2 = 2.0 * loga
    lognormal_y = np.exp(-0.5 * (y - mu) ** 2 / sigma2) / math.sqrt(2.0 * math.pi * sigma2)

    plot_mask = (y >= -7.0) & (y <= 14.0)
    fig, ax = plt.subplots(figsize=(10.2, 5.8))
    ax.semilogy(y[plot_mask], np.maximum(spectral_y[plot_mask], 1.0e-18), label="sinc-product spectral law")
    ax.semilogy(y[plot_mask], np.maximum(lognormal_y[plot_mask], 1.0e-18), linestyle="--", label="lognormal moment twin")
    ax.set_xlabel(r"$y=\log z$")
    ax.set_ylabel("density of log Z")
    ax.set_title(f"General-base spectral/lognormal twins for a={a:g}")
    ax.legend()
    ax.grid(True, alpha=0.3)
    save_figure(fig, fig_dir / "spectral_lognormal_general_base")

    moment_rows: list[dict[str, object]] = []
    for n in range(0, 7):
        numerical = float(np.trapezoid(np.exp(n * y) * spectral_y, y))
        exact = a ** (n * (n + 2)) / 2.0**n
        lognormal_exact = math.exp(n * mu + 0.5 * n * n * sigma2)
        moment_rows.append(
            {
                "base_a": a,
                "moment_order_n": n,
                "spectral_log_grid_quadrature": numerical,
                "exact_sinc_product_moment": exact,
                "lognormal_moment": lognormal_exact,
                "relative_quadrature_error": (numerical - exact) / exact,
            }
        )
    write_csv(
        data_dir / "spectral_moment_validation_a_2_6.csv",
        [
            "base_a",
            "moment_order_n",
            "spectral_log_grid_quadrature",
            "exact_sinc_product_moment",
            "lognormal_moment",
            "relative_quadrature_error",
        ],
        moment_rows,
    )

    # q-Pearson audit on a logarithmic z grid.  Relative errors are reported only where
    # the two sides are not both numerically negligible, avoiding meaningless division at zeros.
    z = np.geomspace(1.0e-7, 2.0e4, 25_000)

    def w_sp(argument: np.ndarray) -> np.ndarray:
        root = np.sqrt(argument)
        return phi_a(root, a) ** 2 / (i_a * root)

    lhs = w_sp(a * a * z)
    rhs = sinc(np.sqrt(z)) ** 2 * w_sp(z) / a
    abs_error = np.abs(lhs - rhs)
    scale = np.abs(lhs) + np.abs(rhs)
    significant = scale > 1.0e-11 * float(np.max(scale))
    rel_error = abs_error[significant] / scale[significant]
    q_rows = [
        {
            "base_a": a,
            "normalizing_integral_I_a": i_a,
            "grid_points": len(z),
            "max_absolute_residual": float(np.max(abs_error)),
            "rms_absolute_residual": float(np.sqrt(np.mean(abs_error**2))),
            "max_relative_residual_on_significant_grid": float(np.max(rel_error)),
            "rms_relative_residual_on_significant_grid": float(np.sqrt(np.mean(rel_error**2))),
        }
    ]
    write_csv(
        data_dir / "spectral_q_pearson_validation_a_2_6.csv",
        [
            "base_a",
            "normalizing_integral_I_a",
            "grid_points",
            "max_absolute_residual",
            "rms_absolute_residual",
            "max_relative_residual_on_significant_grid",
            "rms_relative_residual_on_significant_grid",
        ],
        q_rows,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("."), help="report directory (default: current directory)")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output = args.output.resolve()
    fig_dir = output / "figures"
    data_dir = output / "data"
    fig_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    generate_gap_hierarchy(fig_dir, data_dir)
    generate_tube_oscillation(fig_dir, data_dir)
    generate_degree_critical_limit(fig_dir, data_dir)
    generate_periodic_correction(fig_dir, data_dir)
    generate_moment_and_gaussian_audits(fig_dir, data_dir)
    generate_geometry_norm_table(data_dir)
    generate_spectral_twin(fig_dir, data_dir)

    print(f"Wrote figures to {fig_dir}")
    print(f"Wrote data tables to {data_dir}")


if __name__ == "__main__":
    main()
