#!/usr/bin/env python3
"""Numerical and symbolic experiments for the Fabius--Rvachev information report.

The script is deliberately self contained.  It uses the fixed-point density equation

    X_q  =_d  q X_q' + (1-q) U,       U ~ Uniform[-1,1],

rather than an opaque special-function evaluator.  The CDF form of the transfer
operator makes each iteration linear-time in the grid size and remains stable for
q close to one.  All plots use Matplotlib's default colors and separate figures.

Outputs
-------
data/q_entropy_table.csv
    Differential entropy, variance, Gaussian entropy deficit, Fisher information,
    and varentropy for selected q.
data/dyadic_prefix_entropy.csv
    Entropy of the finite dyadic sinc/Thue--Morse prefixes and the normalized
    entropy gap predicted by the Fisher-information theorem.
data/information_spectrum_summary.csv
    Monte Carlo check of the centered information-density limit.
data/thue_morse_signs.csv
    Finite Thue--Morse signs used in the exact prefix spline formula.
data/symbolic_edgeworth.txt
    Exact symbolic derivation of the first entropic Edgeworth coefficients.
figures/*.pdf and figures/*.png
    Vector and raster versions of the three numerical figures.
numerical_summary.txt
    Human-readable summary of the principal numerical constants.

The density computations are deterministic.  Monte Carlo uses a fixed seed.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path
from typing import Iterable

import matplotlib.pyplot as plt
import numpy as np
import sympy as sp


def trapezoid(values: np.ndarray, grid: np.ndarray) -> float:
    """Compatibility wrapper for NumPy's trapezoidal rule."""
    return float(np.trapezoid(values, grid))


def cdf_from_density(grid: np.ndarray, density: np.ndarray) -> np.ndarray:
    """Return a normalized trapezoidal CDF on an increasing uniform grid."""
    dx = float(grid[1] - grid[0])
    cdf = np.empty_like(density)
    cdf[0] = 0.0
    cdf[1:] = np.cumsum((density[:-1] + density[1:]) * (0.5 * dx))
    total = float(cdf[-1])
    if not math.isfinite(total) or total <= 0.0:
        raise RuntimeError("density has nonpositive or nonfinite mass")
    cdf /= total
    return cdf


def fixed_point_density(
    q: float,
    grid_points: int,
    tolerance: float,
    max_iterations: int,
) -> tuple[np.ndarray, np.ndarray, int, float]:
    """Compute the stationary geometric-uniform density f_q on [-1,1].

    If F is the CDF of a trial density, the density of qX+(1-q)U is

        T_q f(x) = [F((x+1-q)/q)-F((x-1+q)/q)]/[2(1-q)].

    Iterating this contractive smoothing map from the uniform density converges
    rapidly.  Renormalization only compensates for quadrature/interpolation error.
    """
    if not (0.0 < q < 1.0):
        raise ValueError("q must lie in (0,1)")
    if grid_points < 1001 or grid_points % 2 == 0:
        raise ValueError("grid_points must be an odd integer at least 1001")

    grid = np.linspace(-1.0, 1.0, grid_points)
    density = np.full(grid_points, 0.5, dtype=float)
    innovation_halfwidth = 1.0 - q
    last_difference = math.inf

    for iteration in range(1, max_iterations + 1):
        cdf = cdf_from_density(grid, density)
        lower = (grid - innovation_halfwidth) / q
        upper = (grid + innovation_halfwidth) / q
        cdf_lower = np.interp(lower, grid, cdf, left=0.0, right=1.0)
        cdf_upper = np.interp(upper, grid, cdf, left=0.0, right=1.0)
        updated = (cdf_upper - cdf_lower) / (2.0 * innovation_halfwidth)
        updated = np.maximum(updated, 0.0)
        updated /= trapezoid(updated, grid)
        last_difference = float(np.max(np.abs(updated - density)))
        density = updated
        if last_difference < tolerance:
            return grid, density, iteration, last_difference

    raise RuntimeError(
        f"fixed-point iteration did not converge for q={q}; "
        f"last sup difference={last_difference:.3e}"
    )


def prefix_density(q: float, depth: int, grid_points: int) -> tuple[np.ndarray, np.ndarray]:
    """Density of S_{q,m}=(1-q) sum_{j=0}^{m-1} q^j U_j.

    Starting from the first uniform summand, each new summand is included through
    a moving-average CDF formula.  This computes the finite sinc-product spline
    without evaluating its cancellation-prone truncated-power formula.
    """
    if depth < 1:
        raise ValueError("depth must be at least one")
    grid = np.linspace(-1.0, 1.0, grid_points)
    first_halfwidth = 1.0 - q
    density = np.where(
        np.abs(grid) <= first_halfwidth,
        1.0 / (2.0 * first_halfwidth),
        0.0,
    )
    density /= trapezoid(density, grid)

    for j in range(1, depth):
        halfwidth = (1.0 - q) * q**j
        cdf = cdf_from_density(grid, density)
        cdf_lower = np.interp(grid - halfwidth, grid, cdf, left=0.0, right=1.0)
        cdf_upper = np.interp(grid + halfwidth, grid, cdf, left=0.0, right=1.0)
        density = (cdf_upper - cdf_lower) / (2.0 * halfwidth)
        density = np.maximum(density, 0.0)
        density /= trapezoid(density, grid)
    return grid, density


def density_functionals(
    grid: np.ndarray,
    density: np.ndarray,
    fisher_floor: float = 1e-14,
) -> dict[str, float]:
    """Compute entropy, Fisher information, and varentropy.

    The density is flat at the endpoints.  Values below fisher_floor are omitted
    only in the score quotient f'^2/f; their total probability is far below the
    discretization error.  Entropy and varentropy retain every positive grid value.
    """
    positive = density > 0.0
    safe = np.maximum(density, np.finfo(float).tiny)
    surprisal = np.zeros_like(density)
    surprisal[positive] = -np.log(safe[positive])
    entropy = trapezoid(density * surprisal, grid)
    varentropy = trapezoid(density * (surprisal - entropy) ** 2, grid)

    derivative = np.gradient(density, grid, edge_order=2)
    fisher_mask = density > fisher_floor
    fisher_integrand = np.zeros_like(density)
    fisher_integrand[fisher_mask] = (
        derivative[fisher_mask] ** 2 / density[fisher_mask]
    )
    fisher = trapezoid(fisher_integrand, grid)

    return {
        "entropy": entropy,
        "fisher_information": fisher,
        "varentropy": varentropy,
    }


def variance_q(q: float) -> float:
    """Exact variance of X_q for Uniform[-1,1] innovations."""
    return (1.0 - q) / (3.0 * (1.0 + q))


def gaussian_entropy_deficit(entropy: float, variance: float) -> float:
    """D(X || centered Gaussian with the same variance)."""
    return 0.5 * math.log(2.0 * math.pi * math.e * variance) - entropy


def sample_xq(
    rng: np.random.Generator,
    q: float,
    sample_size: int,
    terms: int,
) -> np.ndarray:
    """Sample X_q by a truncated geometric random series.

    The omitted tail is bounded by q**terms.  The defaults make that bound much
    smaller than the density-grid spacing in the dyadic information-spectrum test.
    """
    samples = np.zeros(sample_size, dtype=float)
    weight = 1.0 - q
    for _ in range(terms):
        samples += weight * rng.uniform(-1.0, 1.0, size=sample_size)
        weight *= q
    return samples


def sample_prefix(
    rng: np.random.Generator,
    q: float,
    depth: int,
    sample_size: int,
) -> np.ndarray:
    """Sample the finite prefix S_{q,m}."""
    samples = np.zeros(sample_size, dtype=float)
    weight = 1.0 - q
    for _ in range(depth):
        samples += weight * rng.uniform(-1.0, 1.0, size=sample_size)
        weight *= q
    return samples


def two_sample_ks(first: np.ndarray, second: np.ndarray) -> float:
    """Elementary two-sample Kolmogorov--Smirnov distance."""
    x = np.sort(first)
    y = np.sort(second)
    combined = np.sort(np.concatenate([x, y]))
    cdf_x = np.searchsorted(x, combined, side="right") / x.size
    cdf_y = np.searchsorted(y, combined, side="right") / y.size
    return float(np.max(np.abs(cdf_x - cdf_y)))


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, object]]) -> None:
    """Write a deterministic CSV with an explicit column order."""
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def symbolic_edgeworth(output_path: Path) -> dict[str, sp.Expr]:
    """Derive the first standardized cumulants and entropy-deficit coefficients.

    For epsilon=1-q, the standardized fourth cumulant is

        lambda_4 = -(6/5)(1-q^2)/(1+q^2).

    The Hermite expansion f/phi = 1 + lambda_4 H_4/24 + ... gives

        D(f||phi) = lambda_4^2/48 - lambda_4^3/48 + O(epsilon^4).

    The cubic coefficient uses E[H_4(Z)^3]=1728.  The function records the
    exact SymPy derivation rather than relying on floating-point fitting.
    """
    eps = sp.symbols("epsilon", positive=True)
    q = 1 - eps
    lambda4 = -sp.Rational(6, 5) * (1 - q**2) / (1 + q**2)
    lambda6 = sp.Rational(48, 7) * (1 - q**2) ** 2 / (1 + q**2 + q**4)
    lambda4_series = sp.series(lambda4, eps, 0, 5)
    lambda6_series = sp.series(lambda6, eps, 0, 5)

    z = sp.symbols("z", real=True)
    H4 = z**4 - 6 * z**2 + 3
    # Gaussian moments E[Z^(2k)]=(2k-1)!! evaluate E[H4^3] exactly.
    expanded = sp.expand(H4**3)
    h4_cube_moment = sp.Integer(0)
    for power, coefficient in sp.Poly(expanded, z).terms():
        exponent = power[0]
        if exponent % 2 == 0:
            gaussian_moment = sp.Integer(1) if exponent == 0 else sp.factorial2(exponent - 1)
            h4_cube_moment += coefficient * gaussian_moment
    h4_square_moment = sp.factorial(4)

    entropy_formal = lambda4**2 / 48 - lambda4**3 / 48
    entropy_series = sp.series(entropy_formal, eps, 0, 4)
    c2 = sp.expand(entropy_series.removeO()).coeff(eps, 2)
    c3 = sp.expand(entropy_series.removeO()).coeff(eps, 3)

    text = f"""Exact symbolic Edgeworth calculation
====================================

Let epsilon = 1-q.

lambda_4(q) = {sp.simplify(lambda4)}
lambda_4 series = {lambda4_series}

lambda_6(q) = {sp.simplify(lambda6)}
lambda_6 series = {lambda6_series}

E[H_4(Z)^2] = {h4_square_moment}
E[H_4(Z)^3] = {h4_cube_moment}

Formal entropy expansion through cubic order:
D(Z_q || Gaussian) = lambda_4^2/48 - lambda_4^3/48 + O(epsilon^4)
                    = {entropy_series}

Predicted coefficients:
c_2 = {c2}
c_3 = {c3}
"""
    output_path.write_text(text, encoding="utf-8")
    return {
        "lambda4": sp.simplify(lambda4),
        "lambda6": sp.simplify(lambda6),
        "c2": c2,
        "c3": c3,
        "h4_cube_moment": h4_cube_moment,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("."))
    parser.add_argument("--grid-points", type=int, default=200_001)
    parser.add_argument("--tolerance", type=float, default=2e-13)
    parser.add_argument("--max-iterations", type=int, default=5_000)
    parser.add_argument("--sample-size", type=int, default=250_000)
    parser.add_argument("--seed", type=int, default=20260830)
    args = parser.parse_args()

    root = args.output.resolve()
    data_dir = root / "data"
    figure_dir = root / "figures"
    data_dir.mkdir(parents=True, exist_ok=True)
    figure_dir.mkdir(parents=True, exist_ok=True)

    symbolic = symbolic_edgeworth(data_dir / "symbolic_edgeworth.txt")
    c2 = float(symbolic["c2"])
    c3 = float(symbolic["c3"])

    q_values = [0.50, 0.70, 0.80, 0.90, 0.95, 0.97]
    q_rows: list[dict[str, object]] = []
    density_cache: dict[float, tuple[np.ndarray, np.ndarray, dict[str, float]]] = {}

    for q in q_values:
        grid, density, iterations, residual = fixed_point_density(
            q,
            grid_points=args.grid_points,
            tolerance=args.tolerance,
            max_iterations=args.max_iterations,
        )
        functionals = density_functionals(grid, density)
        variance = variance_q(q)
        deficit = gaussian_entropy_deficit(functionals["entropy"], variance)
        epsilon = 1.0 - q
        formal_prediction = c2 * epsilon**2 + c3 * epsilon**3
        q_rows.append(
            {
                "q": f"{q:.8f}",
                "iterations": iterations,
                "fixed_point_sup_residual": f"{residual:.17g}",
                "variance_exact": f"{variance:.17g}",
                "differential_entropy": f"{functionals['entropy']:.17g}",
                "gaussian_entropy_deficit": f"{deficit:.17g}",
                "deficit_over_(1-q)^2": f"{deficit / epsilon**2:.17g}",
                "formal_cubic_prediction": f"{formal_prediction:.17g}",
                "fisher_information": f"{functionals['fisher_information']:.17g}",
                "varentropy": f"{functionals['varentropy']:.17g}",
            }
        )
        density_cache[q] = (grid, density, functionals)

    write_csv(
        data_dir / "q_entropy_table.csv",
        [
            "q",
            "iterations",
            "fixed_point_sup_residual",
            "variance_exact",
            "differential_entropy",
            "gaussian_entropy_deficit",
            "deficit_over_(1-q)^2",
            "formal_cubic_prediction",
            "fisher_information",
            "varentropy",
        ],
        q_rows,
    )

    # Dyadic finite-prefix entropy convergence.
    dyadic_grid, dyadic_density, dyadic_functionals = density_cache[0.50]
    h_limit = dyadic_functionals["entropy"]
    fisher_limit = dyadic_functionals["fisher_information"]
    variance_limit = variance_q(0.50)
    predicted_gap_coefficient = 0.5 * variance_limit * fisher_limit
    prefix_rows: list[dict[str, object]] = []

    for depth in range(1, 11):
        grid, density = prefix_density(0.50, depth, args.grid_points)
        entropy = density_functionals(grid, density)["entropy"]
        geometric_factor = 0.50 ** (2 * depth)
        entropy_gap = h_limit - entropy
        prefix_rows.append(
            {
                "depth_m": depth,
                "prefix_variance_exact": f"{variance_limit * (1.0 - geometric_factor):.17g}",
                "prefix_entropy": f"{entropy:.17g}",
                "limit_entropy_minus_prefix_entropy": f"{entropy_gap:.17g}",
                "gap_over_4^(-m)": f"{entropy_gap / geometric_factor:.17g}",
                "predicted_limit_coefficient": f"{predicted_gap_coefficient:.17g}",
                "mutual_information_bits_exact": depth,
                "mmse_exact": f"{variance_limit * geometric_factor:.17g}",
            }
        )

    write_csv(
        data_dir / "dyadic_prefix_entropy.csv",
        [
            "depth_m",
            "prefix_variance_exact",
            "prefix_entropy",
            "limit_entropy_minus_prefix_entropy",
            "gap_over_4^(-m)",
            "predicted_limit_coefficient",
            "mutual_information_bits_exact",
            "mmse_exact",
        ],
        prefix_rows,
    )

    # Thue--Morse signs for exact spline formulas.
    sign_rows = []
    for depth in range(1, 9):
        for index in range(2**depth):
            digit_sum = index.bit_count()
            sign_rows.append(
                {
                    "depth_m": depth,
                    "index_j": index,
                    "binary_digit_sum": digit_sum,
                    "thue_morse_sign": 1 if digit_sum % 2 == 0 else -1,
                }
            )
    write_csv(
        data_dir / "thue_morse_signs.csv",
        ["depth_m", "index_j", "binary_digit_sum", "thue_morse_sign"],
        sign_rows,
    )

    # Information-spectrum experiment in the dyadic case.
    rng = np.random.default_rng(args.seed)
    q = 0.50
    grid, density, functionals = density_cache[q]
    log_density_grid = np.log(np.maximum(density, np.finfo(float).tiny))
    tail = sample_xq(rng, q, args.sample_size, terms=60)
    independent_first = sample_xq(rng, q, args.sample_size, terms=60)
    independent_second = sample_xq(rng, q, args.sample_size, terms=60)
    log_first = np.interp(independent_first, grid, log_density_grid)
    log_second = np.interp(independent_second, grid, log_density_grid)
    limiting_centered_information = log_second - log_first

    spectrum_rows: list[dict[str, object]] = []
    centered_samples: dict[int, np.ndarray] = {}
    for depth in [2, 4, 8]:
        prefix = sample_prefix(rng, q, depth, args.sample_size)
        final = prefix + q**depth * tail
        log_tail = np.interp(tail, grid, log_density_grid)
        log_final = np.interp(final, grid, log_density_grid)
        centered = log_tail - log_final
        centered_samples[depth] = centered
        spectrum_rows.append(
            {
                "depth_m": depth,
                "exact_mean_before_centering_nats": f"{depth * math.log(2.0):.17g}",
                "empirical_centered_mean": f"{float(np.mean(centered)):.17g}",
                "empirical_centered_variance": f"{float(np.var(centered)):.17g}",
                "predicted_limiting_variance_2V": f"{2.0 * functionals['varentropy']:.17g}",
                "two_sample_KS_to_limiting_difference": f"{two_sample_ks(centered, limiting_centered_information):.17g}",
            }
        )

    write_csv(
        data_dir / "information_spectrum_summary.csv",
        [
            "depth_m",
            "exact_mean_before_centering_nats",
            "empirical_centered_mean",
            "empirical_centered_variance",
            "predicted_limiting_variance_2V",
            "two_sample_KS_to_limiting_difference",
        ],
        spectrum_rows,
    )

    # Figure 1: entropic Gaussian coefficient.
    epsilons = np.array([1.0 - float(row["q"]) for row in q_rows])
    scaled_deficits = np.array(
        [float(row["deficit_over_(1-q)^2"]) for row in q_rows]
    )
    # The displayed comparison is intentionally restricted to the asymptotic
    # window q >= 0.8.  The CSV retains the coarser q values as a useful warning
    # that a local Edgeworth series should not be extrapolated to q far from one.
    asymptotic_mask = epsilons <= 0.2000001
    plotted_epsilons = epsilons[asymptotic_mask]
    plotted_deficits = scaled_deficits[asymptotic_mask]
    order = np.argsort(plotted_epsilons)
    epsilon_curve = np.linspace(0.0, 0.21, 400)
    formal_scaled_curve = c2 + c3 * epsilon_curve
    plt.figure(figsize=(7.0, 4.5))
    plt.plot(
        plotted_epsilons[order],
        plotted_deficits[order],
        marker="o",
        label="numerical (q >= 0.8)",
    )
    plt.plot(epsilon_curve, formal_scaled_curve, label="formal cubic prediction")
    plt.axhline(c2, linestyle="--", label="limit 3/100")
    plt.xlabel(r"$\varepsilon=1-q$")
    plt.ylabel(r"$D(Z_q\Vert\gamma)/\varepsilon^2$")
    plt.title("Entropic Gaussian limit of the geometric-uniform law")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "entropy_deficit.pdf")
    plt.savefig(figure_dir / "entropy_deficit.png", dpi=180)
    plt.close()

    # Figure 2: Fisher-controlled finite-prefix entropy gap.
    depths = np.array([int(row["depth_m"]) for row in prefix_rows])
    normalized_gaps = np.array([float(row["gap_over_4^(-m)"]) for row in prefix_rows])
    # At depths 9 and 10 the entropy gap is smaller than one grid cell's
    # second-order quadrature error.  Keep those rows in the CSV, but display the
    # numerically resolved range m <= 8 in the figure.
    resolved = depths <= 8
    plt.figure(figsize=(7.0, 4.5))
    plt.plot(
        depths[resolved],
        normalized_gaps[resolved],
        marker="o",
        label="computed normalized gap",
    )
    plt.axhline(predicted_gap_coefficient, linestyle="--", label=r"$J(\mathrm{up})/18$")
    plt.xlabel("prefix depth m")
    plt.ylabel(r"$4^m\,[h(\mathrm{up})-h(S_m)]$")
    plt.title("Fisher-information coefficient for finite sinc prefixes")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "prefix_entropy_gap.pdf")
    plt.savefig(figure_dir / "prefix_entropy_gap.png", dpi=180)
    plt.close()

    # Figure 3: centered information-density convergence.
    plt.figure(figsize=(7.0, 4.5))
    bins = np.linspace(-4.5, 4.5, 150)
    for depth in [2, 4, 8]:
        plt.hist(
            centered_samples[depth],
            bins=bins,
            density=True,
            histtype="step",
            linewidth=1.2,
            label=f"m={depth}",
        )
    plt.hist(
        limiting_centered_information,
        bins=bins,
        density=True,
        histtype="step",
        linewidth=1.6,
        label="independent-surprisal limit",
    )
    plt.xlabel("centered information density (nats)")
    plt.ylabel("estimated density")
    plt.title("Information-spectrum limit for dyadic prefixes")
    plt.legend()
    plt.tight_layout()
    plt.savefig(figure_dir / "information_spectrum.pdf")
    plt.savefig(figure_dir / "information_spectrum.png", dpi=180)
    plt.close()

    dyadic_deficit = gaussian_entropy_deficit(h_limit, variance_limit)
    summary = f"""Fabius--Rvachev information experiments
=======================================

Grid points: {args.grid_points}
Fixed-point tolerance: {args.tolerance:.3e}
Monte Carlo sample size: {args.sample_size}
Random seed: {args.seed}

Dyadic centered Rvachev law (q=1/2)
-----------------------------------
h(up)                         = {h_limit:.15f} nats
Var(up)                       = {variance_limit:.15f}
D(up || matching Gaussian)    = {dyadic_deficit:.15f} nats
                               = {dyadic_deficit / math.log(2.0):.15f} bits
Fisher information J(up)      = {fisher_limit:.15f}
Varentropy V(up)              = {functionals['varentropy']:.15f}
Fisher prefix coefficient     = J(up)/18
                               = {predicted_gap_coefficient:.15f}
Limiting information variance = 2 V(up)
                               = {2.0 * functionals['varentropy']:.15f}

Formal q->1 entropic prediction
--------------------------------
D(Z_q || Gaussian)
  = (3/100)(1-q)^2 + (33/500)(1-q)^3 + O((1-q)^4).

Exact dyadic information law
----------------------------
I(X;S_m) = m log 2 nats = m bits,
MMSE(X|S_m) = 4^(-m)/9.
"""
    (root / "numerical_summary.txt").write_text(summary, encoding="utf-8")
    print(summary)


if __name__ == "__main__":
    main()
