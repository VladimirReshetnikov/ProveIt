#!/usr/bin/env python3
"""Numerical experiments for the Jacobi-digit Fabius--Rvachev report.

The report studies the two-parameter compact random series

    X_{q,alpha} = (1-q) * sum_{n>=0} q^n U_{alpha,n},

where the U_{alpha,n} are independent and have density

    rho_alpha(u) = Gamma(alpha+1/2)/(sqrt(pi) Gamma(alpha))
                   * (1-u^2)^(alpha-1),  -1 < u < 1.

This script is deliberately self-contained.  Its exact/theorem-level tables use
closed formulas, Rayleigh-sum recurrences, or high-precision Hankel determinants.
Monte Carlo is used only for visual density estimates and for an independent
sanity check of moments.  Every random calculation uses a fixed seed.

Outputs
-------
figures/*.pdf, figures/*.png
    Publication-ready vector and raster copies of each plot.
data/*.csv
    Machine-readable numerical tables.
numerical_summary.txt
    A compact record of the main numerical findings and parameters.

The script requires Python 3.11+, NumPy, SciPy, pandas, matplotlib, mpmath,
and SymPy.  No network access is used.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
from typing import Iterable, Sequence

import mpmath as mp
import numpy as np
import pandas as pd
import scipy.ndimage as ndi
import scipy.optimize as optimize
import scipy.special as special
import sympy as sp
import matplotlib as mpl

# Embed TrueType outlines in generated PDF figures.  Matplotlib's default
# Type-3 glyphs render correctly but are less suitable for archival search,
# copy/paste, and downstream print workflows.
mpl.rcParams["pdf.fonttype"] = 42
mpl.rcParams["ps.fonttype"] = 42

import matplotlib.pyplot as plt

DEFAULT_SEED = 20260830


def ensure_directories(root: Path) -> tuple[Path, Path]:
    """Create and return the figure and data directories."""
    figure_dir = root / "figures"
    data_dir = root / "data"
    figure_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    return figure_dir, data_dir


def save_figure(fig: plt.Figure, figure_dir: Path, stem: str) -> None:
    """Save one figure in PDF and PNG form, then close it."""
    fig.tight_layout()
    fig.savefig(figure_dir / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(figure_dir / f"{stem}.png", dpi=220, bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Exact analytic ingredients
# ---------------------------------------------------------------------------


def digit_even_moment(alpha: float, m: int) -> float:
    """Return E[U_alpha^(2m)] = (1/2)_m/(alpha+1/2)_m."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    return float(special.poch(0.5, m) / special.poch(alpha + 0.5, m))


def digit_abs_moment(alpha: float, p: float) -> float:
    """Return E|U_alpha|^p for p > -1.

    The beta-integral gives

        E|U_alpha|^p = Gamma((p+1)/2) Gamma(alpha+1/2)
                       / (sqrt(pi) Gamma(alpha+(p+1)/2)).
    """
    if alpha <= 0:
        raise ValueError("alpha must be positive")
    if p <= -1:
        raise ValueError("p must be greater than -1")
    log_value = (
        special.gammaln((p + 1.0) / 2.0)
        + special.gammaln(alpha + 0.5)
        - 0.5 * math.log(math.pi)
        - special.gammaln(alpha + (p + 1.0) / 2.0)
    )
    return math.exp(log_value)


def rayleigh_sums(alpha: float, max_m: int) -> list[float]:
    """Compute R_m(nu) = sum_k j_{nu,k}^(-2m) by Kishore's recurrence.

    Here nu = alpha - 1/2.  The recurrence is

        R_1 = 1/(4(nu+1)),
        R_m = (sum_{r=1}^{m-1} R_r R_{m-r})/(nu+m),  m >= 2.
    """
    if alpha <= 0:
        raise ValueError("alpha must be positive")
    if max_m < 1:
        return [0.0]
    nu = alpha - 0.5
    values = [0.0] * (max_m + 1)
    values[1] = 1.0 / (4.0 * (nu + 1.0))
    for m in range(2, max_m + 1):
        values[m] = sum(values[r] * values[m - r] for r in range(1, m)) / (
            nu + m
        )
    return values


def digit_cumulants(alpha: float, max_order: int) -> list[float]:
    """Return cumulants kappa_0,...,kappa_max_order of U_alpha."""
    cumulants = [0.0] * (max_order + 1)
    rays = rayleigh_sums(alpha, max_order // 2)
    for m in range(1, max_order // 2 + 1):
        cumulants[2 * m] = (
            (-1.0) ** (m + 1)
            * math.factorial(2 * m)
            / m
            * rays[m]
        )
    return cumulants


def cascade_cumulants(alpha: float, q: float, max_order: int) -> list[float]:
    """Return cumulants of X_{q,alpha} through max_order.

    Cumulants add under independent convolution and scale homogeneously, so

        kappa_r(X) = kappa_r(U) (1-q)^r/(1-q^r).
    """
    if not (0.0 < q < 1.0):
        raise ValueError("q must lie in (0,1)")
    base = digit_cumulants(alpha, max_order)
    a = 1.0 - q
    result = [0.0] * (max_order + 1)
    for r in range(1, max_order + 1):
        if base[r] != 0.0:
            result[r] = base[r] * a**r / (1.0 - q**r)
    return result


def moments_from_cumulants(cumulants: Sequence[float]) -> list[float]:
    """Convert cumulants into raw moments by the Bell recurrence.

    If mu_0=1, then

        mu_n = sum_{r=1}^n binom(n-1,r-1) kappa_r mu_{n-r}.
    """
    max_order = len(cumulants) - 1
    moments = [0.0] * (max_order + 1)
    moments[0] = 1.0
    for n in range(1, max_order + 1):
        moments[n] = sum(
            math.comb(n - 1, r - 1) * cumulants[r] * moments[n - r]
            for r in range(1, n + 1)
        )
    return moments


def standardized_cumulants(alpha: float, q: float, max_m: int = 5) -> dict[int, float]:
    """Return lambda_{2m}=kappa_{2m}/kappa_2^m."""
    cumulants = cascade_cumulants(alpha, q, 2 * max_m)
    variance = cumulants[2]
    return {
        2 * m: cumulants[2 * m] / variance**m for m in range(2, max_m + 1)
    }


def recurrence_coefficients(alpha: float, q: float, n_max: int, dps: int = 80) -> list[float]:
    """Compute monic symmetric Jacobi recurrence coefficients beta_1,...,beta_n.

    For the monic orthogonal polynomials p_n,

        p_{n+1}(x) = x p_n(x) - beta_n p_{n-1}(x).

    The Hankel determinant formula is

        beta_n = Delta_n Delta_{n-2}/Delta_{n-1}^2,
        Delta_n = det[mu_{i+j}]_{i,j=0}^n,
        Delta_{-1}=1.

    High precision is used because higher Hankel determinants can be ill
    conditioned even when the final recurrence coefficient is benign.
    """
    mp.mp.dps = dps
    max_order = 2 * n_max
    # Recompute the Rayleigh/Bell chain with mpmath arithmetic.
    nu = mp.mpf(alpha) - mp.mpf("0.5")
    ray = [mp.mpf("0")] * (n_max + 1)
    ray[1] = 1 / (4 * (nu + 1))
    for m in range(2, n_max + 1):
        ray[m] = sum(ray[r] * ray[m - r] for r in range(1, m)) / (nu + m)

    cumulants = [mp.mpf("0")] * (max_order + 1)
    a = mp.mpf(1) - mp.mpf(q)
    qmp = mp.mpf(q)
    for m in range(1, n_max + 1):
        base = (-1) ** (m + 1) * mp.factorial(2 * m) * ray[m] / m
        cumulants[2 * m] = base * a ** (2 * m) / (1 - qmp ** (2 * m))

    moments = [mp.mpf("0")] * (max_order + 1)
    moments[0] = mp.mpf(1)
    for n in range(1, max_order + 1):
        moments[n] = sum(
            mp.binomial(n - 1, r - 1) * cumulants[r] * moments[n - r]
            for r in range(1, n + 1)
        )

    determinants: dict[int, mp.mpf] = {-1: mp.mpf(1)}
    for n in range(0, n_max + 1):
        matrix = mp.matrix([[moments[i + j] for j in range(n + 1)] for i in range(n + 1)])
        determinants[n] = mp.det(matrix)

    betas = []
    for n in range(1, n_max + 1):
        beta = determinants[n] * determinants[n - 2] / determinants[n - 1] ** 2
        betas.append(float(beta))
    return betas


# ---------------------------------------------------------------------------
# Characteristic functions and sampling
# ---------------------------------------------------------------------------


def normalized_bessel_factor(alpha: float, z: np.ndarray | float) -> np.ndarray:
    """Evaluate Jcal_{alpha-1/2}(z), the characteristic function of U_alpha.

    The function is even.  Near zero scipy.special.hyp0f1 is used directly;
    away from zero the normalized Bessel-J representation is faster and more
    stable for the oscillatory plots.
    """
    values = np.asarray(z, dtype=float)
    absolute = np.abs(values)
    result = np.empty_like(absolute)
    small = absolute < 1.0e-5
    if np.any(small):
        result[small] = special.hyp0f1(alpha + 0.5, -(absolute[small] ** 2) / 4.0)
    if np.any(~small):
        nu = alpha - 0.5
        zz = absolute[~small]
        prefactor = math.exp(nu * math.log(2.0) + special.gammaln(nu + 1.0))
        result[~small] = prefactor * zz ** (-nu) * special.jv(nu, zz)
    return result


def cascade_log_abs_cf(alpha: float, q: float, t: np.ndarray) -> np.ndarray:
    """Return log(abs(Phi_{q,alpha}(t))) by summing factor logarithms."""
    t = np.asarray(t, dtype=float)
    a = 1.0 - q
    total = np.zeros_like(t)
    n = 0
    while a * q**n * float(np.max(np.abs(t))) > 1.0e-8:
        factor = normalized_bessel_factor(alpha, a * q**n * t)
        total += np.log(np.maximum(np.abs(factor), 1.0e-300))
        n += 1
    # The omitted tail is in the quadratic regime.  Its logarithm is
    # -Var(U) t^2/2 times the omitted squared weight sum, up to O(t^4 q^{4n}).
    omitted_weight_squares = a * a * q ** (2 * n) / (1.0 - q * q)
    total -= t * t * omitted_weight_squares / (2.0 * (2.0 * alpha + 1.0))
    return total


def sample_cascade(
    alpha: float,
    q: float,
    n_samples: int,
    rng: np.random.Generator,
    tail_tolerance: float = 1.0e-12,
) -> np.ndarray:
    """Sample the random series by truncating when the deterministic tail is tiny."""
    a = 1.0 - q
    samples = np.zeros(n_samples, dtype=float)
    n = 0
    # The total omitted absolute weight after term n-1 is q^n.
    while q**n > tail_tolerance:
        digit = 2.0 * rng.beta(alpha, alpha, size=n_samples) - 1.0
        samples += a * q**n * digit
        n += 1
    return samples


def smooth_histogram(samples: np.ndarray, bins: int = 520, sigma: float = 1.25) -> tuple[np.ndarray, np.ndarray]:
    """Return a lightly smoothed density histogram on [-1,1]."""
    counts, edges = np.histogram(samples, bins=bins, range=(-1.0, 1.0), density=True)
    centers = 0.5 * (edges[:-1] + edges[1:])
    return centers, ndi.gaussian_filter1d(counts, sigma=sigma, mode="nearest")


# ---------------------------------------------------------------------------
# The beta_3 monotonicity discriminant
# ---------------------------------------------------------------------------


def beta3_derivative_polynomial(A: float, x: np.ndarray | float) -> np.ndarray:
    """Polynomial controlling d(beta_3/variance)/d(q^2).

    A=2 alpha+3 and x=q^2.  All omitted factors in the derivative are
    strictly positive for alpha>0 and 0<=q<1, so this polynomial has exactly
    the derivative's sign.
    """
    x = np.asarray(x, dtype=float)
    return (
        A**3 * (x**6 + 4*x**5 + 8*x**4 + 10*x**3 + 8*x**2 + 4*x + 1)
        + A**2 * (10*x**6 + 44*x**5 + 62*x**4 + 20*x**3 - 30*x**2 - 28*x - 6)
        + A * (3*x**6 + 32*x**5 - 18*x**4 - 74*x**3 - 2*x**2 + 48*x + 11)
        - 6*x**6 + 12*x**3 - 6
    )


def minimum_beta3_derivative_polynomial(alpha: float) -> tuple[float, float]:
    """Return min_{0<=x<=1} P_{2alpha+3}(x) and an argmin."""
    A = 2.0 * alpha + 3.0
    result = optimize.minimize_scalar(
        lambda xx: float(beta3_derivative_polynomial(A, xx)),
        bounds=(0.0, 1.0),
        method="bounded",
        options={"xatol": 1.0e-14},
    )
    # Endpoints are checked explicitly because a bounded minimizer need not
    # return an endpoint when the true minimum is attained there.
    candidates = [
        (float(result.fun), float(result.x)),
        (float(beta3_derivative_polynomial(A, 0.0)), 0.0),
        (float(beta3_derivative_polynomial(A, 1.0)), 1.0),
    ]
    return min(candidates, key=lambda pair: pair[0])


def locate_beta3_threshold() -> tuple[float, float]:
    """Locate the observed monotonicity threshold alpha_3^* and tangency x^*."""
    root = optimize.brentq(
        lambda aa: minimum_beta3_derivative_polynomial(aa)[0],
        0.04,
        0.10,
        xtol=2.0e-14,
        rtol=2.0e-14,
    )
    value, xstar = minimum_beta3_derivative_polynomial(root)
    if abs(value) > 1.0e-7:
        raise RuntimeError("threshold minimization did not converge")
    return float(root), float(xstar)


def beta2_over_variance(alpha: float, q: np.ndarray | float) -> np.ndarray:
    q = np.asarray(q, dtype=float)
    return 2.0 - 6.0 / (2.0 * alpha + 3.0) * (1.0 - q*q) / (1.0 + q*q)


def beta3_over_variance(alpha: float, q: np.ndarray | float) -> np.ndarray:
    q = np.asarray(q, dtype=float)
    lambda4 = -6.0 / (2.0 * alpha + 3.0) * (1.0 - q*q) / (1.0 + q*q)
    lambda6 = (
        240.0
        / ((2.0 * alpha + 3.0) * (2.0 * alpha + 5.0))
        * (1.0 - q*q) ** 2
        / (1.0 + q*q + q**4)
    )
    return (6.0 + 9.0 * lambda4 + lambda6 - lambda4**2) / (2.0 + lambda4)


# ---------------------------------------------------------------------------
# Endpoint Laplace product and its periodic residual
# ---------------------------------------------------------------------------


def log_beta_laplace(alpha: float, y: float) -> float:
    """Return log 1F1(alpha;2alpha;-y) for y>=0.

    Direct evaluation is used at moderate y.  At large y we use the algebraic
    Kummer expansion

      1F1(alpha;2alpha;-y)
        ~ Gamma(2alpha)/Gamma(alpha) y^{-alpha}
           sum_r (alpha)_r(1-alpha)_r/(r! y^r).

    The expansion terminates for positive integer alpha.
    """
    if y < 0.0:
        raise ValueError("y must be nonnegative")
    if y == 0.0:
        return 0.0
    if y < 48.0:
        value = float(special.hyp1f1(alpha, 2.0 * alpha, -y))
        if value <= 0.0:
            raise FloatingPointError("unexpected nonpositive beta Laplace transform")
        return math.log(value)

    series = 1.0
    term = 1.0
    previous = abs(term)
    for r in range(1, 24):
        term *= (alpha + r - 1.0) * (1.0 - alpha + r - 1.0) / (r * y)
        # Stop before a divergent asymptotic series turns around.
        if abs(term) > previous and r > 5:
            break
        series += term
        previous = abs(term)
        if abs(term) < 2.0e-16 * abs(series):
            break
    if series <= 0.0:
        # This branch should not be reached for the parameters used below.
        value = float(mp.hyp1f1(alpha, 2.0 * alpha, -y))
        return math.log(value)
    return (
        special.gammaln(2.0 * alpha)
        - special.gammaln(alpha)
        - alpha * math.log(y)
        + math.log(series)
    )


def endpoint_log_laplace_from_log_z(alpha: float, q: float, log_z: float) -> float:
    """Evaluate sum_n log L_alpha(exp(log_z) q^n).

    Here z=2(1-q)s and L_alpha is the Laplace transform of a Beta(alpha,alpha)
    variable.  Summation stops only after the argument is so small that the
    omitted tail is below double-precision plotting accuracy.
    """
    L = math.log(1.0 / q)
    total = 0.0
    n = 0
    while True:
        log_y = log_z - n * L
        if log_y < -30.0:
            # h(y)=-y/2+O(y^2); summing the remaining geometric tail changes
            # the result by much less than 1e-12 here.
            y = math.exp(log_y)
            total -= 0.5 * y / (1.0 - q)
            break
        y = math.exp(log_y)
        total += log_beta_laplace(alpha, y)
        n += 1
        if n > 10000:
            raise RuntimeError("Laplace product failed to terminate")
    return total


# ---------------------------------------------------------------------------
# Data tables
# ---------------------------------------------------------------------------


def generate_cumulant_table(data_dir: Path) -> pd.DataFrame:
    rows: list[dict[str, float]] = []
    for alpha in [0.05, 0.25, 0.5, 1.0, 1.5, 3.0, 10.0]:
        for q in [0.25, 0.5, 0.75, 0.9]:
            cumulants = cascade_cumulants(alpha, q, 10)
            variance = cumulants[2]
            row: dict[str, float] = {
                "alpha": alpha,
                "q": q,
                "variance": variance,
            }
            for m in range(2, 6):
                row[f"lambda_{2*m}"] = cumulants[2*m] / variance**m
            rows.append(row)
    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "standardized_cumulants.csv", index=False)
    return frame


def generate_orthogonal_table(data_dir: Path) -> pd.DataFrame:
    rows: list[dict[str, float]] = []
    for alpha in [0.03, 0.07, 0.25, 0.5, 1.0, 2.0, 5.0]:
        for q in [0.05, 0.25, 0.5, 0.75, 0.95]:
            betas = recurrence_coefficients(alpha, q, n_max=5)
            variance = (1.0 - q) / ((1.0 + q) * (2.0 * alpha + 1.0))
            row: dict[str, float] = {"alpha": alpha, "q": q, "variance": variance}
            for n, beta in enumerate(betas, start=1):
                row[f"beta_{n}"] = beta
                row[f"beta_{n}_over_variance"] = beta / variance
            rows.append(row)
    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "orthogonal_recurrence_coefficients.csv", index=False)
    return frame


def generate_beta3_phase_table(data_dir: Path) -> tuple[pd.DataFrame, float, float]:
    alpha_star, x_star = locate_beta3_threshold()
    alphas = np.unique(
        np.concatenate(
            [
                np.geomspace(0.002, 0.05, 45),
                np.linspace(0.05, 0.10, 81),
                np.geomspace(0.10, 5.0, 70),
            ]
        )
    )
    rows = []
    for alpha in alphas:
        minimum, argmin = minimum_beta3_derivative_polynomial(float(alpha))
        rows.append(
            {
                "alpha": float(alpha),
                "minimum_polynomial": minimum,
                "argmin_x": argmin,
                "argmin_q": math.sqrt(argmin),
            }
        )
    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "beta3_monotonicity_phase.csv", index=False)

    # The resultant polynomial in A=2alpha+3 that contains the tangency value.
    A = sp.symbols("A")
    coefficients = [
        27, 324, -5670, -58320, 2599461, 23888916, -213002432,
        -1553944800, 10096215141, 40741963244, -197857358766,
        -118077559920, 579333364587, 348162442236, -247263068556,
        -54019599840, 57183051600, -12550510656, 918330048,
    ]
    polynomial = sum(c * A ** (18 - i) for i, c in enumerate(coefficients))
    (data_dir / "beta3_threshold_polynomial.txt").write_text(
        "Q(A) = " + str(sp.expand(polynomial)) + "\n"
        + f"A_star = {2.0*alpha_star+3.0:.16f}\n"
        + f"alpha_star = {alpha_star:.16f}\n"
        + f"x_star = {x_star:.16f}\n"
        + f"q_star = {math.sqrt(x_star):.16f}\n",
        encoding="utf-8",
    )
    return frame, alpha_star, x_star


def bessel_zeros_for_alpha(alpha: float, count: int) -> np.ndarray:
    """Return the first positive zeros for selected integer/half-integer orders."""
    nu = alpha - 0.5
    if abs(nu - 0.5) < 1.0e-12:
        return math.pi * np.arange(1, count + 1, dtype=float)
    nearest_integer = round(nu)
    if abs(nu - nearest_integer) < 1.0e-12 and nearest_integer >= 0:
        return special.jn_zeros(int(nearest_integer), count)
    # mpmath handles general orders; this path is slower but deterministic.
    mp.mp.dps = 40
    return np.array([float(mp.besseljzero(nu, k)) for k in range(1, count + 1)])


def generate_rayleigh_validation(data_dir: Path) -> pd.DataFrame:
    rows = []
    count = 240
    for alpha in [0.5, 1.0, 1.5, 2.5]:
        nu = alpha - 0.5
        zeros = bessel_zeros_for_alpha(alpha, count)
        recurrence = rayleigh_sums(alpha, 5)
        beta_shift = nu / 2.0 - 0.25
        for m in range(1, 6):
            partial = float(np.sum(zeros ** (-2 * m)))
            # McMahon's leading zero asymptotic j_{nu,k}~pi(k+beta_shift)
            # supplies a transparent first tail correction.
            tail = float(
                special.zeta(2 * m, count + 1.0 + beta_shift) / math.pi ** (2 * m)
            )
            corrected = partial + tail
            exact = recurrence[m]
            rows.append(
                {
                    "alpha": alpha,
                    "nu": nu,
                    "m": m,
                    "zeros_used": count,
                    "recurrence_value": exact,
                    "corrected_zero_sum": corrected,
                    "relative_error": abs(corrected - exact) / abs(exact),
                }
            )
    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "rayleigh_sum_validation.csv", index=False)
    return frame


def generate_resonance_table(data_dir: Path) -> pd.DataFrame:
    rows = []
    alpha = 1.5  # nu=1; SciPy provides these zeros directly.
    zeros = bessel_zeros_for_alpha(alpha, 90)
    for count in [10, 20, 40, 80]:
        values = []
        for k in range(count):
            for ell in range(k + 1, count):
                values.append(zeros[k] / zeros[ell])
        values = np.sort(np.array(values))
        augmented = np.concatenate(([0.0], values, [1.0]))
        rows.append(
            {
                "alpha": alpha,
                "zero_count": count,
                "number_of_ratios": len(values),
                "maximum_gap": float(np.max(np.diff(augmented))),
                "median_gap": float(np.median(np.diff(augmented))),
            }
        )
    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "resonance_density.csv", index=False)

    detailed_rows = []
    for d in [1, 2, 3, 4]:
        for k in range(12):
            for ell in range(k + 1, 45):
                detailed_rows.append(
                    {
                        "d": d,
                        "k": k + 1,
                        "ell": ell + 1,
                        "q_resonance": float((zeros[k] / zeros[ell]) ** (1.0 / d)),
                    }
                )
    pd.DataFrame(detailed_rows).to_csv(data_dir / "resonance_cloud.csv", index=False)
    return frame


def generate_moment_validation(
    data_dir: Path, rng: np.random.Generator, n_samples: int
) -> pd.DataFrame:
    rows = []
    for alpha, q in [(0.08, 0.4), (0.5, 0.5), (1.0, 0.5), (3.0, 0.8)]:
        samples = sample_cascade(alpha, q, n_samples, rng)
        exact = moments_from_cumulants(cascade_cumulants(alpha, q, 8))
        for order in [2, 4, 6, 8]:
            empirical = float(np.mean(samples**order))
            rows.append(
                {
                    "alpha": alpha,
                    "q": q,
                    "samples": n_samples,
                    "order": order,
                    "exact_moment": exact[order],
                    "empirical_moment": empirical,
                    "relative_error": abs(empirical - exact[order]) / abs(exact[order]),
                }
            )
    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "moment_monte_carlo_validation.csv", index=False)
    return frame


# ---------------------------------------------------------------------------
# Figures
# ---------------------------------------------------------------------------


def figure_digit_densities(figure_dir: Path) -> None:
    x = np.linspace(-0.999, 0.999, 1600)
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.15, 0.5, 1.0, 2.0, 6.0]:
        log_c = special.gammaln(alpha + 0.5) - 0.5 * math.log(math.pi) - special.gammaln(alpha)
        y = np.exp(log_c + (alpha - 1.0) * np.log1p(-(x*x)))
        ax.plot(x, y, label=rf"$\alpha={alpha:g}$")
    ax.set_xlabel(r"$u$")
    ax.set_ylabel(r"$\rho_\alpha(u)$")
    ax.set_title("Jacobi digit densities")
    ax.set_ylim(bottom=0.0, top=4.2)
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "jacobi_digit_densities")


def figure_cascade_density_bridge(
    figure_dir: Path, rng: np.random.Generator, n_samples: int
) -> None:
    q = 0.5
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.035, 0.5, 1.0, 3.0]:
        samples = sample_cascade(alpha, q, n_samples, rng)
        x, y = smooth_histogram(samples)
        ax.plot(x, y, label=rf"$\alpha={alpha:g}$")
    ax.axhline(0.5, linestyle="--", linewidth=1.0, label=r"$\alpha\downarrow0$ limit")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("density")
    ax.set_title(r"The $q=1/2$ Bernoulli--Rvachev--Gaussian dimension bridge")
    ax.set_xlim(-1.0, 1.0)
    ax.set_ylim(bottom=0.0)
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "cascade_density_bridge_q_half")


def figure_bernoulli_desingularization(
    figure_dir: Path, rng: np.random.Generator, n_samples: int
) -> None:
    q = 0.4
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.018, 0.05, 0.15, 0.6]:
        samples = sample_cascade(alpha, q, n_samples, rng)
        x, y = smooth_histogram(samples, bins=720, sigma=1.1)
        ax.plot(x, y, label=rf"$\alpha={alpha:g}$")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel("density")
    ax.set_title(r"Smooth desingularization of the $q=0.4$ Bernoulli convolution")
    ax.set_xlim(-1.0, 1.0)
    ax.set_ylim(bottom=0.0, top=4.6)
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "bernoulli_desingularization_q_0p4")


def figure_characteristic_products(figure_dir: Path) -> None:
    q = 0.5
    t = np.linspace(0.0, 90.0, 3600)
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.08, 0.5, 1.0, 2.0]:
        log_abs = cascade_log_abs_cf(alpha, q, t)
        ax.plot(t, np.maximum(log_abs / math.log(10.0), -24.0), label=rf"$\alpha={alpha:g}$")
    ax.set_xlabel(r"$t$")
    ax.set_ylabel(r"$\log_{10}|\widehat f_{q,\alpha}(t)|$")
    ax.set_title(r"Geometric Bessel products at $q=1/2$")
    ax.set_ylim(-24.0, 0.5)
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "geometric_bessel_products")


def figure_beta2_flow(figure_dir: Path) -> None:
    q = np.linspace(0.0, 0.995, 500)
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.03, 0.07, 0.25, 1.0, 3.0]:
        ax.plot(q, beta2_over_variance(alpha, q), label=rf"$\alpha={alpha:g}$")
    ax.axhline(2.0, linestyle="--", linewidth=1.0, label="Hermite limit")
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"$\beta_2/\operatorname{Var}(X)$")
    ax.set_title("Second monic recurrence coefficient: exact monotone flow")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "orthogonal_beta2_flow")


def figure_beta3_flow(figure_dir: Path, alpha_star: float) -> None:
    q = np.linspace(0.002, 0.995, 700)
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.015, 0.04, alpha_star, 0.10, 1.0]:
        label = rf"$\alpha={alpha:.4g}$"
        ax.plot(q, beta3_over_variance(alpha, q), label=label)
    ax.axhline(3.0, linestyle="--", linewidth=1.0, label="Hermite limit")
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"$\beta_3/\operatorname{Var}(X)$")
    ax.set_title("Third recurrence coefficient and the small-alpha turning phase")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "orthogonal_beta3_flow")


def figure_beta3_phase(figure_dir: Path, phase: pd.DataFrame, alpha_star: float) -> None:
    # The transition is concentrated below alpha=0.1; restricting the plotted
    # window makes the sign change visible instead of letting the large-alpha
    # cubic growth dominate the vertical scale.
    window = phase[phase["alpha"] <= 0.5]
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ax.semilogx(window["alpha"], window["minimum_polynomial"])
    ax.axhline(0.0, linestyle="--", linewidth=1.0)
    ax.axvline(alpha_star, linestyle=":", linewidth=1.0, label=rf"$\alpha_3^*\approx{alpha_star:.8f}$")
    ax.set_xlabel(r"$\alpha$")
    ax.set_ylabel(r"$\min_{0\leq x\leq1}P_{2\alpha+3}(x)$")
    ax.set_title(r"Small-$\alpha$ phase test for monotonicity of $\beta_3$")
    ax.set_ylim(-0.36, 6.5)
    ax.legend()
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "beta3_monotonicity_phase")


def figure_resonance_cloud(figure_dir: Path, data_dir: Path) -> None:
    frame = pd.read_csv(data_dir / "resonance_cloud.csv")
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for d, group in frame.groupby("d"):
        ax.scatter(group["q_resonance"], group["ell"], s=7.0, alpha=0.45, label=rf"$d={d}$")
    ax.set_xlabel(r"resonant $q=(j_{\nu,k}/j_{\nu,\ell})^{1/d}$")
    ax.set_ylabel(r"upper zero index $\ell$")
    ax.set_title(r"Countable-dense Bessel-scale resonances ($\alpha=3/2$, $\nu=1$)")
    ax.set_xlim(0.0, 1.0)
    ax.legend(ncol=4)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "bessel_resonance_cloud")


def figure_laplace_periodicity(figure_dir: Path, data_dir: Path) -> pd.DataFrame:
    alpha = 1.3
    q = 0.1
    L = math.log(1.0 / q)
    log_c = special.gammaln(2.0 * alpha) - special.gammaln(alpha)
    quadratic = alpha / (2.0 * L)
    linear = log_c / L - alpha / 2.0
    theta_grid = np.linspace(0.0, 1.0, 240, endpoint=False)

    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    rows = []
    for N in [0, 1, 2, 5, 15]:
        residuals = []
        for theta in theta_grid:
            T = L * (N + theta)
            value = endpoint_log_laplace_from_log_z(alpha, q, T)
            residual = value + quadratic * T * T - linear * T
            residuals.append(residual)
            rows.append({"alpha": alpha, "q": q, "N": N, "theta": theta, "residual": residual})
        ax.plot(theta_grid, residuals, label=rf"$N={N}$")
    ax.set_xlabel(r"$\theta=\{\log_{1/q}z\}$")
    ax.set_ylabel("quadratic-subtracted residual")
    ax.set_title("Convergence to the one-periodic endpoint Laplace profile")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "endpoint_laplace_periodic_profile")

    frame = pd.DataFrame(rows)
    frame.to_csv(data_dir / "endpoint_laplace_periodic_profile.csv", index=False)
    return frame


def figure_gaussian_corner(figure_dir: Path) -> None:
    """Plot the exact standardized fourth cumulant across the two Gaussian routes."""
    q = np.linspace(0.02, 0.995, 600)
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    for alpha in [0.1, 0.5, 1.0, 3.0, 20.0]:
        lambda4 = -6.0 / (2.0 * alpha + 3.0) * (1.0 - q*q) / (1.0 + q*q)
        ax.plot(q, np.abs(lambda4), label=rf"$\alpha={alpha:g}$")
    ax.set_yscale("log")
    ax.set_xlabel(r"$q$")
    ax.set_ylabel(r"absolute excess cumulant $|\lambda_4|$")
    ax.set_title("Two-parameter Gaussian corner: either q approaches 1 or alpha grows")
    ax.legend(ncol=2)
    ax.grid(True, alpha=0.25)
    save_figure(fig, figure_dir, "two_parameter_gaussian_corner")


# ---------------------------------------------------------------------------
# Main driver
# ---------------------------------------------------------------------------


def run(root: Path, samples: int, validation_samples: int, seed: int) -> None:
    figure_dir, data_dir = ensure_directories(root)
    rng = np.random.default_rng(seed)

    cumulants = generate_cumulant_table(data_dir)
    orthogonal = generate_orthogonal_table(data_dir)
    phase, alpha_star, x_star = generate_beta3_phase_table(data_dir)
    rayleigh = generate_rayleigh_validation(data_dir)
    resonance = generate_resonance_table(data_dir)
    validation = generate_moment_validation(data_dir, rng, validation_samples)

    figure_digit_densities(figure_dir)
    figure_cascade_density_bridge(figure_dir, rng, samples)
    figure_bernoulli_desingularization(figure_dir, rng, samples)
    figure_characteristic_products(figure_dir)
    figure_beta2_flow(figure_dir)
    figure_beta3_flow(figure_dir, alpha_star)
    figure_beta3_phase(figure_dir, phase, alpha_star)
    figure_resonance_cloud(figure_dir, data_dir)
    periodic = figure_laplace_periodicity(figure_dir, data_dir)
    figure_gaussian_corner(figure_dir)

    # A small exact-symbolic supplement: first five digit cumulants as rational
    # functions of alpha, generated independently by moments and log-MGF series.
    alpha_symbol, t = sp.symbols("alpha t", positive=True)
    mgf = sp.hyper([], [alpha_symbol + sp.Rational(1, 2)], t**2 / 4)
    log_series = sp.series(sp.log(mgf), t, 0, 12).removeO().expand()
    exact_rows = []
    for m in range(1, 6):
        cumulant = sp.factor(sp.expand(log_series).coeff(t, 2*m) * sp.factorial(2*m))
        exact_rows.append({"order": 2*m, "digit_cumulant": str(cumulant)})
    pd.DataFrame(exact_rows).to_csv(data_dir / "exact_digit_cumulants.csv", index=False)

    # The W_1 coupling rate to the Bernoulli-convolution boundary.
    boundary_rows = []
    for alpha in [1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 0.1, 0.3, 1.0]:
        expected_abs = digit_abs_moment(alpha, 1.0)
        boundary_rows.append(
            {
                "alpha": alpha,
                "E_abs_U": expected_abs,
                "W1_coupling_bound": 1.0 - expected_abs,
                "bound_over_alpha": (1.0 - expected_abs) / alpha,
                "limit_2_log_2": 2.0 * math.log(2.0),
            }
        )
    pd.DataFrame(boundary_rows).to_csv(data_dir / "bernoulli_boundary_W1_rate.csv", index=False)

    max_rayleigh_error = float(rayleigh["relative_error"].max())
    max_moment_error = float(validation["relative_error"].max())
    periodic_last = periodic[periodic["N"] == periodic["N"].max()]
    periodic_amplitude = float(periodic_last["residual"].max() - periodic_last["residual"].min())
    summary = f"""Jacobi-digit Fabius--Rvachev numerical summary
================================================
seed = {seed}
density samples per curve = {samples}
moment-validation samples per parameter pair = {validation_samples}

Observed beta_3 monotonicity tangency
-------------------------------------
alpha_star = {alpha_star:.15f}
A_star = 2 alpha_star + 3 = {2*alpha_star+3:.15f}
x_star = q_star^2 = {x_star:.15f}
q_star = {math.sqrt(x_star):.15f}

Validation diagnostics
----------------------
maximum relative error in corrected Bessel-zero/Rayleigh-sum table = {max_rayleigh_error:.6e}
maximum relative Monte Carlo error through eighth moments = {max_moment_error:.6e}
limiting periodic-profile amplitude for alpha=1.3, q=0.1, N=15 = {periodic_amplitude:.6e}

Rows written
------------
standardized_cumulants.csv: {len(cumulants)}
orthogonal_recurrence_coefficients.csv: {len(orthogonal)}
beta3_monotonicity_phase.csv: {len(phase)}
rayleigh_sum_validation.csv: {len(rayleigh)}
resonance_density.csv: {len(resonance)}
moment_monte_carlo_validation.csv: {len(validation)}
endpoint_laplace_periodic_profile.csv: {len(periodic)}
"""
    (root / "numerical_summary.txt").write_text(summary, encoding="utf-8")
    print(summary)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-root",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory in which figures/, data/, and the summary are written",
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=320_000,
        help="Monte Carlo samples per density curve",
    )
    parser.add_argument(
        "--validation-samples",
        type=int,
        default=600_000,
        help="samples per independent moment-validation parameter pair",
    )
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    return parser.parse_args()


if __name__ == "__main__":
    arguments = parse_args()
    run(
        root=arguments.output_root.resolve(),
        samples=arguments.samples,
        validation_samples=arguments.validation_samples,
        seed=arguments.seed,
    )
