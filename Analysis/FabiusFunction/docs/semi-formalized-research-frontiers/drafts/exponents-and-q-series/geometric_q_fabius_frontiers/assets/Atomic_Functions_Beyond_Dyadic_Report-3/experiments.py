#!/usr/bin/env python3
"""Reproducible numerical experiments for Atomic Functions Beyond the Dyadic Case.

The script generates every figure and CSV table referenced by the LaTeX report.
It deliberately keeps the numerical layer separate from the proofs: all theorem
statements in the report are derived analytically, while the computations here
serve as audits, illustrations, and regression tests.

Dependencies
------------
* NumPy
* Matplotlib
* mpmath

Typical use
-----------
    python experiments.py --output .

The command creates ``figures/`` and ``data/`` below the requested output
directory.  Both PDF (vector) and PNG (raster) versions of each figure are saved.
The pseudorandom seed is fixed at 20260828.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib

# A noninteractive backend makes the script reproducible on headless systems.
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

SEED = 20260828
RNG = np.random.default_rng(SEED)


@dataclass(frozen=True)
class OutputTree:
    """Directories used by the script."""

    root: Path
    figures: Path
    data: Path

    @classmethod
    def create(cls, root: Path) -> "OutputTree":
        root = root.resolve()
        figures = root / "figures"
        data = root / "data"
        figures.mkdir(parents=True, exist_ok=True)
        data.mkdir(parents=True, exist_ok=True)
        return cls(root=root, figures=figures, data=data)


def write_csv(path: Path, fieldnames: Sequence[str], rows: Iterable[dict[str, object]]) -> None:
    """Write dictionaries to a UTF-8 CSV file with a stable column order."""

    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def save_figure(fig: plt.Figure, stem: Path) -> None:
    """Save one Matplotlib figure in vector and raster formats."""

    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".png"), dpi=220, bbox_inches="tight")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Elementary exact formulae for the separated regime a > 2
# ---------------------------------------------------------------------------


def support_radius(a: float) -> float:
    return 1.0 / (a - 1.0)


def central_gap_length(a: float) -> float:
    return 2.0 * (a - 2.0) / (a * (a - 1.0))


def fractal_dimension(a: float) -> float:
    return math.log(2.0) / math.log(a)


def gap_intervals(a: float, max_generation: int) -> list[tuple[int, str, float, float]]:
    """Return all complementary gaps through ``max_generation``.

    A word is recorded in the same order as the affine maps are applied.  The
    empty word denotes the central gap.  The generation is also the exact local
    polynomial degree of h_a on that gap.
    """

    b1 = (a - 2.0) / (a * (a - 1.0))
    current: list[tuple[str, float, float]] = [("", -b1, b1)]
    rows: list[tuple[int, str, float, float]] = []

    for generation in range(max_generation + 1):
        for word, left, right in current:
            rows.append((generation, word or "central", left, right))
        next_generation: list[tuple[str, float, float]] = []
        for word, left, right in current:
            next_generation.append((word + "-", (left - 1.0) / a, (right - 1.0) / a))
            next_generation.append((word + "+", (left + 1.0) / a, (right + 1.0) / a))
        current = sorted(next_generation, key=lambda item: item[1])
    return rows


def exact_tube_volume(a: float, eps: np.ndarray | float) -> np.ndarray:
    """Exact inner tube volume V_a(eps) for 0 < 2 eps < ell_0.

    The function is vectorized.  Values outside the small-tube range are clipped
    to the geometrically obvious interval [0, 2b]; the report only uses the exact
    displayed formula in its stated range.
    """

    eps_array = np.asarray(eps, dtype=float)
    ell0 = central_gap_length(a)
    b = support_radius(a)
    result = np.empty_like(eps_array)

    small = (eps_array > 0.0) & (2.0 * eps_array < ell0)
    if np.any(small):
        e = eps_array[small]
        n = np.floor(np.log(ell0 / (2.0 * e)) / math.log(a)).astype(int)
        result[small] = (
            2.0 * e * (2.0 ** (n + 1) - 1.0)
            + ell0 * (2.0 / a) ** (n + 1) / (1.0 - 2.0 / a)
        )

    nonpositive = eps_array <= 0.0
    large = 2.0 * eps_array >= ell0
    result[nonpositive] = 0.0
    if np.any(large):
        result[large] = np.minimum(
            2.0 * b, 2.0 * eps_array[large] + (2.0 * b - ell0)
        )
    return np.minimum(result, 2.0 * b)


def minkowski_profile(a: float, theta: np.ndarray | float) -> np.ndarray:
    """The one-periodic normalized tube profile M_a(theta)."""

    theta_array = np.asarray(theta, dtype=float)
    ell0 = central_gap_length(a)
    d = fractal_dimension(a)
    return ell0**d * (
        2.0 ** (2.0 - d - theta_array)
        + 2.0 ** (1.0 - d)
        * a ** ((d - 1.0) * (1.0 - theta_array))
        / (1.0 - 2.0 / a)
    )


def distance_moment(a: float, s: float) -> float:
    """Exact E[Delta_a^s] for a uniform point in the support.

    Delta_a is the distance from the point to the Cantor nonanalytic set K_a.
    The formula is valid for Re(s) > D_a - 1; only real s in that range are used
    numerically here.
    """

    p = (a - 2.0) / a
    ell0 = central_gap_length(a)
    return p * (ell0 / 2.0) ** s / ((s + 1.0) * (1.0 - 2.0 * a ** (-(s + 1.0))))


# ---------------------------------------------------------------------------
# Bernoulli cumulants and Bell-polynomial moments
# ---------------------------------------------------------------------------


def cumulants_h_a(a: float, max_order: int) -> list[float]:
    """Return cumulants kappa_0,...,kappa_max_order of X_a."""

    mp.mp.dps = 80
    cumulants = [0.0] * (max_order + 1)
    for order in range(2, max_order + 1, 2):
        m = order // 2
        value = mp.power(2, order) * mp.bernoulli(order) / (
            order * (mp.power(a, order) - 1)
        )
        cumulants[order] = float(value)
    return cumulants


def moments_from_cumulants(cumulants: Sequence[float]) -> list[float]:
    """Complete Bell-polynomial recurrence for ordinary moments."""

    max_order = len(cumulants) - 1
    moments = [0.0] * (max_order + 1)
    moments[0] = 1.0
    for n in range(1, max_order + 1):
        total = 0.0
        for j in range(1, n + 1):
            total += math.comb(n - 1, j - 1) * cumulants[j] * moments[n - j]
        moments[n] = total
    return moments


def truncation_terms(a: float, deterministic_tail_bound: float = 1e-12) -> int:
    """Choose N so sum_{j>N} a^{-j} is below the requested bound."""

    threshold = 1.0 / (deterministic_tail_bound * (a - 1.0))
    return max(1, math.ceil(math.log(threshold) / math.log(a)))


def sample_random_series(a: float, sample_size: int, terms: int) -> np.ndarray:
    """Sample sum_{j=1}^terms a^{-j} U_j with U_j uniform on [-1,1]."""

    weights = a ** (-np.arange(1, terms + 1, dtype=float))
    # Generate in moderate chunks so the routine remains usable with much larger
    # sample sizes than those required by the report.
    output = np.empty(sample_size, dtype=float)
    chunk_size = 50_000
    for start in range(0, sample_size, chunk_size):
        stop = min(sample_size, start + chunk_size)
        uniforms = RNG.uniform(-1.0, 1.0, size=(stop - start, terms))
        output[start:stop] = uniforms @ weights
    return output


# ---------------------------------------------------------------------------
# Stable computation of the periodic Laplace correction P_a
# ---------------------------------------------------------------------------


def kappa_numpy(u: np.ndarray) -> np.ndarray:
    """Stable double-precision kappa(u)=log((1-exp(-u))/u)."""

    u = np.asarray(u, dtype=float)
    out = np.empty_like(u)
    small = u < 1e-3
    if np.any(small):
        z = u[small]
        # log((1-e^{-z})/z) = -z/2 + z^2/24 - z^4/2880
        #                         + z^6/181440 - z^8/9676800 + O(z^10).
        out[small] = (
            -z / 2.0
            + z**2 / 24.0
            - z**4 / 2880.0
            + z**6 / 181440.0
            - z**8 / 9_676_800.0
        )
    if np.any(~small):
        z = u[~small]
        out[~small] = np.log(-np.expm1(-z) / z)
    return out


def periodic_correction_values(a: float, x: np.ndarray, tol: float = 2e-16) -> np.ndarray:
    """Compute the exact periodic correction P_a(x) from its convergent sums.

    The tail of Lambda is controlled by kappa(u) ~ -u/2, so stopping when the
    largest remaining u is below ``tol*(a-1)`` keeps the omitted geometric tail
    near machine precision.  The R_a sum is stopped after exp(-a^{x+n}) is tiny.
    """

    x = np.asarray(x, dtype=float)
    loga = math.log(a)
    u0 = np.exp(loga * x)

    lam = np.zeros_like(x)
    j = 1
    while True:
        u = u0 * a ** (-j)
        lam += kappa_numpy(u)
        if float(np.max(u)) / (2.0 * (a - 1.0)) < tol:
            break
        j += 1
        if j > 20_000:
            raise RuntimeError("Lambda_a sum did not converge; check the base and tolerance")

    rsum = np.zeros_like(x)
    n = 0
    while True:
        u = u0 * a**n
        term = np.log1p(-np.exp(-u))
        rsum += term
        if float(np.max(np.abs(term))) < tol:
            break
        n += 1
        if n > 20_000:
            raise RuntimeError("R_a sum did not converge; check the base and tolerance")

    return lam + 0.5 * loga * x**2 - 0.5 * loga * x + rsum


def gamma_zeta_mode(a: float, k: int) -> complex:
    """Closed Fourier coefficient -Gamma(-chi_k) zeta(1-chi_k)/log(a)."""

    mp.mp.dps = 80
    chi = 2j * mp.pi * k / mp.log(a)
    value = -mp.gamma(-chi) * mp.zeta(1 - chi) / mp.log(a)
    return complex(value)


# ---------------------------------------------------------------------------
# Figure and table generators
# ---------------------------------------------------------------------------


def experiment_gap_hierarchy(out: OutputTree) -> None:
    a = 2.6
    max_generation = 7
    gaps = gap_intervals(a, max_generation)

    fig, ax = plt.subplots(figsize=(10.0, 5.4))
    for generation, _word, left, right in gaps:
        ax.plot([left, right], [generation, generation], linewidth=2.0)
    b = support_radius(a)
    ax.set_xlim(-b * 1.03, b * 1.03)
    ax.set_ylim(max_generation + 0.6, -0.6)
    ax.set_xlabel("gap location")
    ax.set_ylabel("generation = exact polynomial degree")
    ax.set_title(r"Complementary gaps of $K_a$ for $a=2.6$")
    ax.grid(True, alpha=0.25)
    save_figure(fig, out.figures / "gap_hierarchy_a_2_6")

    rows = []
    for generation, word, left, right in gaps:
        rows.append(
            {
                "a": a,
                "generation": generation,
                "word": word,
                "left": f"{left:.17g}",
                "right": f"{right:.17g}",
                "length": f"{right-left:.17g}",
                "exact_polynomial_degree": generation,
            }
        )
    write_csv(
        out.data / "gap_geometry_a_2_6.csv",
        ["a", "generation", "word", "left", "right", "length", "exact_polynomial_degree"],
        rows,
    )

    norm_rows = []
    for base in (2.0, 2.6, 3.0, 5.0):
        for n in range(0, 11):
            norm_rows.append(
                {
                    "a": base,
                    "n": n,
                    "L_infinity_norm": f"{base ** ((n + 1) * (n + 2) / 2) / 2 ** (n + 1):.17g}",
                    "L1_norm": f"{base ** (n * (n + 1) / 2):.17g}",
                }
            )
    write_csv(out.data / "derivative_norms.csv", ["a", "n", "L_infinity_norm", "L1_norm"], norm_rows)


def experiment_tube_oscillation(out: OutputTree) -> None:
    a = 3.0
    ell0 = central_gap_length(a)
    d = fractal_dimension(a)
    x = np.linspace(0.025, 12.0, 2400)
    eps = 0.5 * ell0 * a ** (-x)
    volume = exact_tube_volume(a, eps)
    normalized = eps ** (d - 1.0) * volume
    profile = minkowski_profile(a, np.mod(x, 1.0))

    fig, ax = plt.subplots(figsize=(10.0, 4.8))
    ax.plot(x, normalized, label=r"exact $\varepsilon^{D_a-1}V_a(\varepsilon)$")
    ax.plot(x, profile, linestyle="--", label=r"periodic profile $\mathcal{M}_a(\{x\})$")
    ax.set_xlabel(r"$x=\log_a(\ell_0/(2\varepsilon))$")
    ax.set_ylabel("normalized tube volume")
    ax.set_title(r"Log-periodic tube oscillation for $a=3$")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, out.figures / "tube_oscillation_a_3")

    rows = [
        {
            "x": f"{xx:.17g}",
            "epsilon": f"{ee:.17g}",
            "tube_volume": f"{vv:.17g}",
            "normalized_tube_volume": f"{nn:.17g}",
            "periodic_profile": f"{pp:.17g}",
            "residual": f"{nn-pp:.17g}",
        }
        for xx, ee, vv, nn, pp in zip(x[::8], eps[::8], volume[::8], normalized[::8], profile[::8])
    ]
    write_csv(
        out.data / "tube_oscillation_a_3.csv",
        ["x", "epsilon", "tube_volume", "normalized_tube_volume", "periodic_profile", "residual"],
        rows,
    )


def experiment_degree_limit(out: OutputTree) -> None:
    bases = (2.5, 2.2, 2.1, 2.05, 2.02)
    x = np.linspace(0.0, 5.0, 2001)

    fig, ax = plt.subplots(figsize=(9.5, 5.2))
    table: dict[str, np.ndarray] = {"x": x}
    for a in bases:
        p = (a - 2.0) / a
        nmax = np.floor(x / p).astype(int)
        cdf = 1.0 - (1.0 - p) ** (nmax + 1)
        ax.step(x, cdf, where="post", linewidth=1.3, label=f"a={a:g}")
        table[f"cdf_a_{str(a).replace('.', '_')}"] = cdf
    exponential_cdf = 1.0 - np.exp(-x)
    table["exp1_cdf"] = exponential_cdf
    ax.plot(x, exponential_cdf, linestyle="--", linewidth=2.2, label="Exp(1)")
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$\mathbb{P}(p_aN_a\leq x)$")
    ax.set_title("Critical limit of the local polynomial degree")
    ax.set_xlim(0.0, 5.0)
    ax.set_ylim(0.0, 1.01)
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, out.figures / "degree_critical_limit")

    fieldnames = list(table)
    rows = []
    for index in range(0, len(x), 4):
        rows.append({name: f"{values[index]:.17g}" for name, values in table.items()})
    write_csv(out.data / "degree_critical_limit.csv", fieldnames, rows)


def experiment_distance_to_singular_set(out: OutputTree) -> None:
    a = 3.0
    p = (a - 2.0) / a
    ell0 = central_gap_length(a)
    b = support_radius(a)
    sample_size = 300_000

    generation = RNG.geometric(p, size=sample_size) - 1
    relative_position = RNG.random(sample_size)
    gap_length = ell0 * a ** (-generation)
    distance = 0.5 * gap_length * relative_position

    r = np.geomspace(ell0 * a ** (-12) / 2.0, ell0 / 2.0, 900)
    exact_survival = 1.0 - exact_tube_volume(a, r) / (2.0 * b)
    sorted_distance = np.sort(distance)
    empirical_survival = 1.0 - np.searchsorted(sorted_distance, r, side="right") / sample_size

    fig, ax = plt.subplots(figsize=(9.5, 5.0))
    ax.plot(r, exact_survival, linewidth=2.0, label="exact survival function")
    ax.plot(r, empirical_survival, linestyle="--", linewidth=1.2, label="Monte Carlo audit")
    ax.set_xscale("log")
    ax.set_xlabel(r"distance threshold $r$")
    ax.set_ylabel(r"$\mathbb{P}(\Delta_a>r)$")
    ax.set_title(r"Distance from a uniform point to $K_a$ for $a=3$")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, out.figures / "distance_to_singular_set_a_3")

    rows = []
    for s in (0.5, 1.0, 2.0, 3.0):
        powers = distance**s
        empirical = float(np.mean(powers))
        standard_error = float(np.std(powers, ddof=1) / math.sqrt(sample_size))
        exact = distance_moment(a, s)
        rows.append(
            {
                "a": a,
                "s": s,
                "sample_size": sample_size,
                "exact_moment": f"{exact:.17g}",
                "empirical_moment": f"{empirical:.17g}",
                "absolute_error": f"{abs(empirical-exact):.17g}",
                "standard_error": f"{standard_error:.17g}",
                "z_score": f"{(empirical-exact)/standard_error:.17g}",
            }
        )
    write_csv(
        out.data / "distance_validation_a_3.csv",
        ["a", "s", "sample_size", "exact_moment", "empirical_moment", "absolute_error", "standard_error", "z_score"],
        rows,
    )


def experiment_periodic_correction(out: OutputTree) -> None:
    plot_bases = (1.5, 2.0, 2.6, 3.0, 5.0)
    x_plot = np.linspace(0.0, 1.0, 1001)

    fig, ax = plt.subplots(figsize=(10.0, 5.2))
    for a in plot_bases:
        values = periodic_correction_values(a, x_plot)
        # The endpoint is a duplicate under periodic identification; integrate
        # only over [0,1) to avoid double weighting it.
        mean = float(np.mean(values[:-1]))
        ax.plot(x_plot, values - mean, label=f"a={a:g}")
    ax.set_xlabel(r"$x$ modulo $1$")
    ax.set_ylabel(r"$P_a(x)-\overline{P}_a$")
    ax.set_title("General-base periodic correction in the endpoint Laplace law")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, out.figures / "periodic_correction_bases")

    residual_rows = []
    x_test = np.linspace(-0.4, 1.4, 2001)
    for a in (1.2, 1.5, 2.0, 2.6, 3.0, 5.0):
        residual = periodic_correction_values(a, x_test + 1.0) - periodic_correction_values(a, x_test)
        residual_rows.append(
            {
                "a": a,
                "grid_points": len(x_test),
                "max_abs_periodicity_residual": f"{float(np.max(np.abs(residual))):.17g}",
                "rms_periodicity_residual": f"{float(np.sqrt(np.mean(residual**2))):.17g}",
            }
        )
    write_csv(
        out.data / "periodicity_residuals.csv",
        ["a", "grid_points", "max_abs_periodicity_residual", "rms_periodicity_residual"],
        residual_rows,
    )

    # A uniform periodic grid makes the trapezoidal rule equivalent to a DFT and
    # is spectrally accurate for the analytic function P_a.
    mode_rows = []
    grid_size = 16384
    x = np.arange(grid_size, dtype=float) / grid_size
    for a in plot_bases:
        values = periodic_correction_values(a, x)
        values -= np.mean(values)
        for k in range(1, 5):
            numerical = complex(np.mean(values * np.exp(-2j * np.pi * k * x)))
            exact = gamma_zeta_mode(a, k)
            mode_rows.append(
                {
                    "a": a,
                    "k": k,
                    "numerical_real": f"{numerical.real:.17g}",
                    "numerical_imag": f"{numerical.imag:.17g}",
                    "closed_form_real": f"{exact.real:.17g}",
                    "closed_form_imag": f"{exact.imag:.17g}",
                    "absolute_error": f"{abs(numerical-exact):.17g}",
                    "relative_error": f"{abs(numerical-exact)/max(abs(exact), 1e-300):.17g}",
                }
            )
    write_csv(
        out.data / "gamma_zeta_modes.csv",
        [
            "a",
            "k",
            "numerical_real",
            "numerical_imag",
            "closed_form_real",
            "closed_form_imag",
            "absolute_error",
            "relative_error",
        ],
        mode_rows,
    )


def experiment_gaussian_cumulants(out: OutputTree) -> None:
    epsilon = np.geomspace(1e-4, 1.0, 900)
    a = 1.0 + epsilon
    exact = -(6.0 / 5.0) * (a**2 - 1.0) / (a**2 + 1.0)
    first_term = -(6.0 / 5.0) * epsilon

    fig, ax = plt.subplots(figsize=(9.5, 5.0))
    ax.plot(epsilon, exact, label=r"exact standardized cumulant $\lambda_4(a)$")
    ax.plot(epsilon, first_term, linestyle="--", label=r"first term $-\frac{6}{5}(a-1)$")
    ax.set_xscale("log")
    ax.set_xlabel(r"$a-1$")
    ax.set_ylabel(r"fourth standardized cumulant")
    ax.set_title("Gaussian limit as the base decreases to one")
    ax.grid(True, alpha=0.25)
    ax.legend()
    save_figure(fig, out.figures / "gaussian_cumulant_limit")

    rows = [
        {
            "a_minus_1": f"{ee:.17g}",
            "a": f"{aa:.17g}",
            "lambda4_exact": f"{ex:.17g}",
            "first_asymptotic_term": f"{ft:.17g}",
            "difference": f"{ex-ft:.17g}",
        }
        for ee, aa, ex, ft in zip(epsilon[::6], a[::6], exact[::6], first_term[::6])
    ]
    write_csv(
        out.data / "gaussian_cumulant_limit.csv",
        ["a_minus_1", "a", "lambda4_exact", "first_asymptotic_term", "difference"],
        rows,
    )


def experiment_moments(out: OutputTree) -> None:
    a = 2.6
    max_order = 10
    sample_size = 250_000
    terms = truncation_terms(a, 1e-12)
    sample = sample_random_series(a, sample_size, terms)

    cumulants = cumulants_h_a(a, max_order)
    exact_moments = moments_from_cumulants(cumulants)
    rows = []
    for order in range(max_order + 1):
        powers = sample**order
        empirical = float(np.mean(powers))
        standard_error = 0.0 if order == 0 else float(np.std(powers, ddof=1) / math.sqrt(sample_size))
        exact = exact_moments[order]
        z_score = 0.0 if standard_error == 0.0 else (empirical - exact) / standard_error
        rows.append(
            {
                "a": a,
                "order": order,
                "sample_size": sample_size,
                "truncation_terms": terms,
                "deterministic_tail_bound": "1e-12",
                "exact_moment": f"{exact:.17g}",
                "empirical_moment": f"{empirical:.17g}",
                "absolute_error": f"{abs(empirical-exact):.17g}",
                "standard_error": f"{standard_error:.17g}",
                "z_score": f"{z_score:.17g}",
            }
        )
    write_csv(
        out.data / "moment_validation_a_2_6.csv",
        [
            "a",
            "order",
            "sample_size",
            "truncation_terms",
            "deterministic_tail_bound",
            "exact_moment",
            "empirical_moment",
            "absolute_error",
            "standard_error",
            "z_score",
        ],
        rows,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("."),
        help="report directory in which figures/ and data/ will be created",
    )
    args = parser.parse_args()
    out = OutputTree.create(args.output)

    experiment_gap_hierarchy(out)
    experiment_tube_oscillation(out)
    experiment_degree_limit(out)
    experiment_distance_to_singular_set(out)
    experiment_periodic_correction(out)
    experiment_gaussian_cumulants(out)
    experiment_moments(out)

    print(f"Generated figures in {out.figures}")
    print(f"Generated data tables in {out.data}")


if __name__ == "__main__":
    main()
