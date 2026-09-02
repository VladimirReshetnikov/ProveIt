#!/usr/bin/env python3
"""Reproducible experiments for generalized Rvachev atomic densities.

For a>1 let

    F_a(t) = product_{j>=1} sinc(t a^{-j}),
    h_a     = inverse Fourier transform of F_a.

Equivalently h_a is the probability density of

    X_a = sum_{j>=1} a^{-j} U_j,   U_j ~ Uniform[-1,1] independently.

The report proves the formulas visualized here.  This script is an audit and
illustration layer only: it checks moments against simulation, verifies the
one-periodicity of a general-base negative-Laplace correction, draws the
Cantor-gap hierarchy for a>2, and illustrates two parameter limits.

Every random experiment has a fixed seed.  No network access is required.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


# ---------------------------------------------------------------------------
# Exact geometry for a > 2
# ---------------------------------------------------------------------------

def support_radius(a: float) -> float:
    """Return b=1/(a-1), so supp(h_a)=[-b,b]."""
    if a <= 1:
        raise ValueError("a must be greater than 1")
    return 1.0 / (a - 1.0)


def central_half_gap(a: float) -> float:
    """Return b_1=(a-2)/(a(a-1)), the half-width of the central gap."""
    if a <= 2:
        raise ValueError("the separated-gap formula requires a>2")
    return (a - 2.0) / (a * (a - 1.0))


def affine_map(interval: tuple[float, float], sign: int, a: float) -> tuple[float, float]:
    """Apply S_sign(x)=(x+sign)/a to an interval; sign is -1 or +1."""
    left, right = interval
    return ((left + sign) / a, (right + sign) / a)


def gap_intervals(a: float, generation: int) -> list[tuple[float, float]]:
    """Return all 2^generation complementary gaps of that generation.

    Generation 0 is the central gap G_0=(-b_1,b_1).  Generation n consists
    of S_w(G_0) over words w of length n in S_-(x)=(x-1)/a and
    S_+(x)=(x+1)/a.
    """
    intervals = [(-central_half_gap(a), central_half_gap(a))]
    for _ in range(generation):
        next_intervals: list[tuple[float, float]] = []
        for interval in intervals:
            next_intervals.append(affine_map(interval, -1, a))
            next_intervals.append(affine_map(interval, +1, a))
        intervals = next_intervals
    return sorted(intervals)


def gap_length(a: float, generation: int) -> float:
    """Length ell_n=ell_0 a^{-n}, ell_0=2(a-2)/(a(a-1))."""
    return 2.0 * central_half_gap(a) * a ** (-generation)


def hausdorff_dimension(a: float) -> float:
    """Similarity dimension D=log(2)/log(a) for the separated IFS."""
    if a <= 2:
        raise ValueError("the separated self-similar-set formula requires a>2")
    return math.log(2.0) / math.log(a)


def tube_volume(a: float, epsilon: float) -> float:
    """Exact inner tube volume of the singular Cantor set inside its gaps.

    The complementary string has 2^n intervals of length ell_n=ell_0 a^{-n}.
    Thus V(eps)=sum_n 2^n min(2 eps,ell_n).  The tail is summed exactly as a
    geometric series, so the only error is floating-point roundoff.
    """
    if a <= 2:
        raise ValueError("tube formula requires a>2")
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    ell0 = gap_length(a, 0)
    ratio = 2.0 / a
    if 2.0 * epsilon >= ell0:
        return 2.0 * support_radius(a)
    x = math.log(ell0 / (2.0 * epsilon), a)
    n = math.floor(x)
    resolved = 2.0 * epsilon * (2.0 ** (n + 1) - 1.0)
    tail = ell0 * ratio ** (n + 1) / (1.0 - ratio)
    return resolved + tail


# ---------------------------------------------------------------------------
# Moments, cumulants, and derivative norms
# ---------------------------------------------------------------------------

def even_cumulant(a: float, m: int) -> mp.mpf:
    r"""Return kappa_{2m}=2^{2m}B_{2m}/(2m(a^{2m}-1))."""
    if a <= 1 or m < 1:
        raise ValueError("require a>1 and m>=1")
    return mp.power(2, 2 * m) * mp.bernoulli(2 * m) / (
        2 * m * (mp.power(a, 2 * m) - 1)
    )


def cumulants(a: float, n_max: int) -> list[mp.mpf]:
    """Return [kappa_0,...,kappa_nmax], with odd cumulants equal to zero."""
    out = [mp.mpf("0")] * (n_max + 1)
    for n in range(2, n_max + 1, 2):
        out[n] = even_cumulant(a, n // 2)
    return out


def moments_from_cumulants(kappa: Sequence[mp.mpf]) -> list[mp.mpf]:
    """Compute moments by the complete-Bell recurrence.

    mu_0=1 and
    mu_n=sum_{j=1}^n binom(n-1,j-1) kappa_j mu_{n-j}.
    """
    n_max = len(kappa) - 1
    mu = [mp.mpf("0")] * (n_max + 1)
    mu[0] = mp.mpf("1")
    for n in range(1, n_max + 1):
        mu[n] = sum(
            math.comb(n - 1, j - 1) * kappa[j] * mu[n - j]
            for j in range(1, n + 1)
        )
    return mu


def standardized_cumulant(a: float, m: int) -> mp.mpf:
    """Return kappa_{2m}/sigma^{2m}, where sigma^2=1/(3(a^2-1))."""
    sigma2 = mp.mpf(1) / (3 * (mp.mpf(a) ** 2 - 1))
    return even_cumulant(a, m) / sigma2**m


def derivative_linf(a: float, n: int) -> float:
    r"""Exact norm for a>=2: ||h_a^(n)||_inf=a^((n+1)(n+2)/2)/2^(n+1)."""
    if a < 2 or n < 0:
        raise ValueError("require a>=2 and n>=0")
    return a ** (((n + 1) * (n + 2)) / 2.0) / (2.0 ** (n + 1))


def derivative_l1(a: float, n: int) -> float:
    r"""Exact norm for a>=2: ||h_a^(n)||_1=a^(n(n+1)/2)."""
    if a < 2 or n < 0:
        raise ValueError("require a>=2 and n>=0")
    return a ** (n * (n + 1) / 2.0)


# ---------------------------------------------------------------------------
# Exact negative-Laplace renormalization for arbitrary base a>1
# ---------------------------------------------------------------------------

def kappa_kernel(u: float) -> float:
    r"""kappa(u)=log((1-exp(-u))/u), evaluated stably for u>0."""
    if u <= 0:
        raise ValueError("u must be positive")
    return math.log(-math.expm1(-u)) - math.log(u)


def laplace_log(a: float, u: float, tol: float = 1e-15) -> float:
    r"""Compute Lambda_a(u)=sum_{j>=1} kappa(u a^{-j})."""
    if a <= 1 or u <= 0:
        raise ValueError("require a>1 and u>0")
    total = 0.0
    j = 1
    while True:
        x = u * a ** (-j)
        total += kappa_kernel(x)
        # For small x, kappa(x)=-x/2+O(x^2).  The remaining terms form a
        # geometric tail; this conservative test is much tighter than the
        # accuracy used in the figures.
        if x < tol * max(1.0, a - 1.0):
            break
        j += 1
        if j > 100000:
            raise RuntimeError("Laplace sum did not converge")
    return total


def forward_tail_log(a: float, x: float, tol: float = 1e-15) -> float:
    r"""Return R_a(x)=sum_{n>=0} log(1-exp(-a^(x+n))).

    R_a is negative and exponentially convergent.  The exact periodic function
    used in the report is

      P_a(x)=Lambda_a(a^x)+(log a)(x^2-x)/2+R_a(x).
    """
    total = 0.0
    n = 0
    while True:
        y = a ** (x + n)
        term = math.log1p(-math.exp(-y)) if y < 745 else 0.0
        total += term
        if abs(term) < tol:
            break
        n += 1
        if n > 100000:
            raise RuntimeError("forward tail did not converge")
    return total


def periodic_correction(a: float, x: float) -> float:
    """Exact one-periodic correction P_a(x)."""
    lna = math.log(a)
    return (
        laplace_log(a, a**x)
        + 0.5 * lna * x * x
        - 0.5 * lna * x
        + forward_tail_log(a, x)
    )


def theoretical_fourier_coefficient(a: float, k: int) -> complex:
    r"""Return -Gamma(-chi_k) zeta(1-chi_k)/log(a), k!=0."""
    if k == 0:
        raise ValueError("the displayed formula is for nonzero Fourier modes")
    chi = 2j * mp.pi * k / mp.log(a)
    return complex(-mp.gamma(-chi) * mp.zeta(1 - chi) / mp.log(a))


# ---------------------------------------------------------------------------
# Fixed-seed random-sum validation
# ---------------------------------------------------------------------------

def sample_xa(a: float, sample_count: int, seed: int = 20260828) -> np.ndarray:
    """Sample X_a after truncating at a deterministic tail below 1e-12."""
    if a <= 1:
        raise ValueError("a must exceed 1")
    j_max = max(1, math.ceil(math.log(1e12 / (a - 1.0), a)))
    rng = np.random.default_rng(seed)
    out = np.zeros(sample_count)
    for j in range(1, j_max + 1):
        out += a ** (-j) * rng.uniform(-1.0, 1.0, size=sample_count)
    return out


# ---------------------------------------------------------------------------
# Figures and data tables
# ---------------------------------------------------------------------------

def make_gap_figure(out_dir: Path) -> None:
    a = 2.6
    max_generation = 7
    fig, ax = plt.subplots(figsize=(9.2, 5.6))
    for n in range(max_generation + 1):
        for left, right in gap_intervals(a, n):
            ax.plot([left, right], [n, n], linewidth=3.0)
    b = support_radius(a)
    ax.set_xlim(-b, b)
    ax.set_ylim(-0.6, max_generation + 0.7)
    ax.set_xlabel(r"position $x$")
    ax.set_ylabel("gap generation / exact local polynomial degree")
    ax.set_title(r"Complementary gaps of $K_a$ for $a=2.6$")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "gap_hierarchy_a_2_6.pdf")
    fig.savefig(out_dir / "gap_hierarchy_a_2_6.png", dpi=180)
    plt.close(fig)


def make_tube_figure(out_dir: Path) -> None:
    a = 3.0
    d = hausdorff_dimension(a)
    ell0 = gap_length(a, 0)
    phase = np.linspace(2.0, 10.0, 1601)
    eps = 0.5 * ell0 * a ** (-phase)
    normalized = np.array([tube_volume(a, e) * e ** (d - 1.0) for e in eps])
    fig, ax = plt.subplots(figsize=(9.2, 5.2))
    ax.plot(phase, normalized)
    ax.set_xlabel(r"$\log_a(\ell_0/(2\varepsilon))$")
    ax.set_ylabel(r"$\varepsilon^{D-1}V(\varepsilon)$")
    ax.set_title(r"Exact lattice tube oscillation for the singular set, $a=3$")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "tube_oscillation_a_3.pdf")
    fig.savefig(out_dir / "tube_oscillation_a_3.png", dpi=180)
    plt.close(fig)


def make_degree_limit_figure(out_dir: Path) -> None:
    # N_a is geometric: P(N=n)=p(1-p)^n, p=(a-2)/a.  Hence pN -> Exp(1).
    fig, ax = plt.subplots(figsize=(9.2, 5.2))
    x = np.linspace(0.0, 6.0, 601)
    ax.plot(x, 1.0 - np.exp(-x), linestyle="--", label=r"$1-e^{-x}$")
    for a in (2.5, 2.2, 2.05, 2.01):
        p = (a - 2.0) / a
        n = np.floor(x / p).astype(int)
        cdf = 1.0 - (1.0 - p) ** (n + 1)
        ax.plot(x, cdf, label=fr"$a={a}$")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("Pr(p_a N_a <= x)")
    ax.set_title("Critical exponential limit of the local polynomial degree")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "degree_critical_limit.pdf")
    fig.savefig(out_dir / "degree_critical_limit.png", dpi=180)
    plt.close(fig)


def make_periodic_correction_figure(out_dir: Path) -> None:
    fig, ax = plt.subplots(figsize=(9.2, 5.2))
    x = np.linspace(0.0, 1.0, 301)
    for a in (2.0, 2.5, 3.0):
        values = np.array([periodic_correction(a, float(t)) for t in x])
        values -= np.trapezoid(values, x)
        ax.plot(x, values, label=fr"$a={a}$")
    ax.set_xlabel(r"phase $x$ modulo $1$")
    ax.set_ylabel(r"$P_a(x)-\int_0^1P_a$")
    ax.set_title("General-base negative-Laplace periodic correction")
    ax.legend()
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "periodic_correction_bases.pdf")
    fig.savefig(out_dir / "periodic_correction_bases.png", dpi=180)
    plt.close(fig)


def make_gaussian_figure(out_dir: Path) -> None:
    # lambda_4=-(6/5)(a^2-1)/(a^2+1) ~ -(6/5)(a-1).
    a_values = 1.0 + np.logspace(-4, -0.25, 250)
    lam4 = np.array([float(standardized_cumulant(float(a), 2)) for a in a_values])
    fig, ax = plt.subplots(figsize=(9.2, 5.2))
    ax.loglog(a_values - 1.0, np.abs(lam4), label=r"exact $|\lambda_4(a)|$")
    ax.loglog(
        a_values - 1.0,
        1.2 * (a_values - 1.0),
        linestyle="--",
        label=r"$(6/5)(a-1)$",
    )
    ax.set_xlabel(r"$a-1$")
    ax.set_ylabel("standardized fourth cumulant magnitude")
    ax.set_title(r"First non-Gaussian correction as $a\downarrow1$")
    ax.legend()
    ax.grid(True, which="both", alpha=0.25)
    fig.tight_layout()
    fig.savefig(out_dir / "gaussian_cumulant_limit.pdf")
    fig.savefig(out_dir / "gaussian_cumulant_limit.png", dpi=180)
    plt.close(fig)


def write_summary_tables(data_dir: Path) -> None:
    with (data_dir / "geometry_and_norms.csv").open("w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow([
            "a", "D=log(2)/log(a)", "central_gap_length", "mean_degree",
            "variance_degree", "n", "Linf_derivative", "L1_derivative",
        ])
        for a in (2.05, 2.2, 2.6, 3.0, 4.0):
            p = (a - 2.0) / a
            mean = (1.0 - p) / p
            variance = (1.0 - p) / (p * p)
            for n in range(0, 6):
                writer.writerow([
                    f"{a:.12g}", f"{hausdorff_dimension(a):.16g}",
                    f"{gap_length(a,0):.16g}", f"{mean:.16g}",
                    f"{variance:.16g}", n, f"{derivative_linf(a,n):.16g}",
                    f"{derivative_l1(a,n):.16g}",
                ])

    a = 2.6
    max_order = 10
    mu = moments_from_cumulants(cumulants(a, max_order))
    samples = sample_xa(a, 250_000)
    with (data_dir / "moment_validation_a_2_6.csv").open("w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(["order", "exact_moment", "monte_carlo_moment", "absolute_error"])
        for n in range(max_order + 1):
            empirical = float(np.mean(samples**n))
            exact = float(mu[n])
            writer.writerow([n, f"{exact:.18g}", f"{empirical:.18g}", f"{abs(empirical-exact):.18g}"])

    with (data_dir / "periodicity_residuals.csv").open("w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(["a", "max_abs_residual_on_grid"])
        grid = np.linspace(-0.4, 1.4, 61)
        for a in (1.2, 1.5, 2.0, 2.6, 3.0, 5.0):
            residual = max(
                abs(periodic_correction(a, float(x + 1.0)) - periodic_correction(a, float(x)))
                for x in grid
            )
            writer.writerow([f"{a:.12g}", f"{residual:.18g}"])

    # Compare a numerical discrete Fourier coefficient to the Gamma-zeta formula.
    with (data_dir / "periodic_fourier_validation.csv").open("w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow([
            "a", "k", "numeric_real", "numeric_imag", "formula_real",
            "formula_imag", "absolute_error",
        ])
        grid = np.arange(4096) / 4096.0
        for a in (2.0, 2.5, 3.0):
            values = np.array([periodic_correction(a, float(x)) for x in grid])
            for k in (1, 2):
                numeric = np.mean(values * np.exp(-2j * np.pi * k * grid))
                formula = theoretical_fourier_coefficient(a, k)
                writer.writerow([
                    a, k, f"{numeric.real:.18g}", f"{numeric.imag:.18g}",
                    f"{formula.real:.18g}", f"{formula.imag:.18g}",
                    f"{abs(numeric-formula):.18g}",
                ])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="output directory (default: directory containing this script)",
    )
    args = parser.parse_args()
    fig_dir = args.output / "figures"
    data_dir = args.output / "data"
    fig_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)

    mp.mp.dps = 50
    make_gap_figure(fig_dir)
    make_tube_figure(fig_dir)
    make_degree_limit_figure(fig_dir)
    make_periodic_correction_figure(fig_dir)
    make_gaussian_figure(fig_dir)
    write_summary_tables(data_dir)
    print(f"Wrote figures to {fig_dir}")
    print(f"Wrote data tables to {data_dir}")


if __name__ == "__main__":
    main()
