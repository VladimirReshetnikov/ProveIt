#!/usr/bin/env python3
"""Numerical experiments for the Rvachev/atomic-function report.

The script is deliberately self-contained and deterministic.  It produces
three figures and five small CSV tables used by the LaTeX report:

    ha_a3_density.png
    local_degree_distribution.png
    fup_clt.png
    ha_a3_diagnostics.csv
    gap_length_check_a3.csv
    polynomial_gap_fit_a3.csv
    generalized_ha_parameters.csv
    fup_clt_cumulants.csv

Mathematical conventions
------------------------
For a>1, h_a is the probability density of

    X_a = sum_{j>=1} a^{-j} U_j,       U_j ~ Uniform[-1,1], independent.

It is the fixed point of

    (T_a f)(x) = a/2 * integral_{a x - 1}^{a x + 1} f(y) dy.

For a>2, the complement of the Bernoulli Cantor set consists of gaps.
A gap of generation n is a region on which h_a is a polynomial of exact
degree n.  The exact leading coefficient is

    (-1)^(number of right branches)
    * a^((n+1)(n+2)/2) / (2^(n+1) n!).

The last experiment samples the generalized Fup hierarchy

    Z_n = 2^{-n} X_2 + 2^{-n-1} sum_{r=1}^n U_r,

standardizes it, and compares its density with the standard Gaussian.

Requirements: Python 3.10+, NumPy, SciPy, and Matplotlib.
"""

from __future__ import annotations

import csv
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray
from scipy.integrate import cumulative_trapezoid
from scipy.special import bernoulli
from scipy.stats import norm

OUTPUT_DIR = Path(__file__).resolve().parent
RNG = np.random.default_rng(20260828)


@dataclass(frozen=True)
class DensityApproximation:
    """A uniform-grid approximation to h_a."""

    a: float
    x: NDArray[np.float64]
    density: NDArray[np.float64]
    iterations: int

    @property
    def b(self) -> float:
        return 1.0 / (self.a - 1.0)


def fixed_point_density(
    a: float,
    grid_size: int = 131_073,
    iterations: int = 38,
) -> DensityApproximation:
    """Approximate h_a by iterating its exact integral fixed-point operator.

    The grid includes both endpoints of [-b,b].  The integral in T_a is
    evaluated from a cumulative trapezoidal integral and linear interpolation.
    Starting from the uniform density is convenient; the affine random-series
    operator is contracting at the level of probability laws, and the result
    stabilizes rapidly for the present diagnostics.
    """

    if a <= 1.0:
        raise ValueError("a must be greater than 1")
    if grid_size < 1025 or grid_size % 2 == 0:
        raise ValueError("grid_size must be an odd integer >= 1025")

    b = 1.0 / (a - 1.0)
    x = np.linspace(-b, b, grid_size, dtype=np.float64)
    f = np.full_like(x, 1.0 / (2.0 * b))

    for _ in range(iterations):
        primitive = cumulative_trapezoid(f, x, initial=0.0)
        left = np.clip(a * x - 1.0, -b, b)
        right = np.clip(a * x + 1.0, -b, b)
        p_left = np.interp(left, x, primitive)
        p_right = np.interp(right, x, primitive)
        f = 0.5 * a * (p_right - p_left)

        # Correct only accumulated discretization error, not the shape.
        mass = np.trapezoid(f, x)
        if not np.isfinite(mass) or mass <= 0.0:
            raise RuntimeError("fixed-point iteration produced an invalid density")
        f /= mass

    return DensityApproximation(a=a, x=x, density=f, iterations=iterations)


def interp_density(approx: DensityApproximation, points: NDArray[np.float64]) -> NDArray[np.float64]:
    """Interpolate the computed density and return zero outside its support."""

    return np.interp(points, approx.x, approx.density, left=0.0, right=0.0)


def write_csv(path: Path, header: Sequence[str], rows: Iterable[Sequence[object]]) -> None:
    """Write a compact UTF-8 CSV file with stable newlines."""

    with path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


def central_gap_halfwidth(a: float) -> float:
    """Half-width b_1 of the central polynomial plateau for a>2."""

    b = 1.0 / (a - 1.0)
    return b * (1.0 - 2.0 / a)


def apply_word_interval(a: float, interval: tuple[float, float], word: str) -> tuple[float, float]:
    """Apply the IFS word to an interval.

    A '-' letter applies phi_-(x)=(x-1)/a and '+' applies
    phi_+(x)=(x+1)/a.  Letters are read from left to right as outer
    compositions, matching the report's convention

        phi_{w-}=phi_- o phi_w,  phi_{w+}=phi_+ o phi_w.
    """

    lo, hi = interval
    for letter in word:
        if letter == "-":
            lo, hi = (lo - 1.0) / a, (hi - 1.0) / a
        elif letter == "+":
            lo, hi = (lo + 1.0) / a, (hi + 1.0) / a
        else:
            raise ValueError(f"unexpected word letter: {letter!r}")
    return lo, hi


def all_words(n: int) -> list[str]:
    """Return all length-n words in lexicographic (- before +) order."""

    words = [""]
    for _ in range(n):
        words = [w + sign for w in words for sign in ("-", "+")]
    return words


def exact_gap_leading_coefficient(a: float, word: str) -> float:
    """Leading coefficient of h_a on the gap indexed by *word*."""

    n = len(word)
    magnitude = a ** ((n + 1) * (n + 2) / 2.0) / (2.0 ** (n + 1) * math.factorial(n))
    return (-1.0 if word.count("+") % 2 else 1.0) * magnitude


def classify_local_degree(a: float, points: NDArray[np.float64], max_depth: int = 80) -> NDArray[np.int64]:
    """Classify uniform support points by the generation of their gap.

    For a>2, points in the central gap have degree 0.  Points in a first
    child gap have degree 1, and so on.  The Cantor set itself has Lebesgue
    measure zero; an unresolved value after max_depth is marked -1.
    """

    if a <= 2.0:
        raise ValueError("the gap classifier requires a>2")

    b1 = central_gap_halfwidth(a)
    y = np.asarray(points, dtype=np.float64).copy()
    result = np.full(y.shape, -1, dtype=np.int64)
    active = np.ones(y.shape, dtype=bool)

    for depth in range(max_depth + 1):
        in_gap = active & (np.abs(y) < b1)
        result[in_gap] = depth
        active &= ~in_gap
        if not np.any(active):
            break

        left = active & (y <= -b1)
        right = active & (y >= b1)
        # Invert phi_-(z)=(z-1)/a and phi_+(z)=(z+1)/a.
        y[left] = a * y[left] + 1.0
        y[right] = a * y[right] - 1.0

    return result


def experiment_ha_a3() -> None:
    """Compute h_3, check plateaux/gaps, and save a density figure."""

    a = 3.0
    approx = fixed_point_density(a)
    b = approx.b
    b1 = central_gap_halfwidth(a)

    central_mask = np.abs(approx.x) <= 0.95 * b1
    central_values = approx.density[central_mask]
    central_mean = float(np.mean(central_values))
    central_max_deviation = float(np.max(np.abs(central_values - a / 2.0)))
    mass = float(np.trapezoid(approx.density, approx.x))
    symmetry_error = float(np.max(np.abs(approx.density - approx.density[::-1])))

    write_csv(
        OUTPUT_DIR / "ha_a3_diagnostics.csv",
        ["quantity", "computed", "exact_or_target", "absolute_error"],
        [
            ("total_mass", f"{mass:.16g}", "1", f"{abs(mass - 1.0):.6g}"),
            ("central_plateau_mean", f"{central_mean:.16g}", f"{a/2:.16g}", f"{abs(central_mean-a/2):.6g}"),
            ("central_plateau_max_deviation", f"{central_max_deviation:.16g}", "0", f"{central_max_deviation:.6g}"),
            ("reflection_symmetry_max_error", f"{symmetry_error:.16g}", "0", f"{symmetry_error:.6g}"),
            ("support_halfwidth", f"{b:.16g}", "1/2", f"{abs(b-0.5):.6g}"),
            ("central_gap_halfwidth", f"{b1:.16g}", "1/6", f"{abs(b1-1/6):.6g}"),
        ],
    )

    # Check exact total gap lengths by generation.
    ell0 = 2.0 * b1
    gap_rows: list[Sequence[object]] = []
    partial = 0.0
    for n in range(11):
        count = 2**n
        one_length = ell0 * a ** (-n)
        total = count * one_length
        partial += total
        exact_total = 2.0 * b * (1.0 - 2.0 / a) * (2.0 / a) ** n
        gap_rows.append(
            (
                n,
                count,
                f"{one_length:.16g}",
                f"{total:.16g}",
                f"{exact_total:.16g}",
                f"{abs(total-exact_total):.6g}",
                f"{partial:.16g}",
                f"{2*b-partial:.16g}",
            )
        )
    write_csv(
        OUTPUT_DIR / "gap_length_check_a3.csv",
        [
            "generation",
            "gap_count",
            "one_gap_length",
            "total_generation_length",
            "closed_form_total",
            "absolute_error",
            "cumulative_gap_length",
            "remaining_cantor_cover_length",
        ],
        gap_rows,
    )

    # Fit polynomials on the interiors of low-generation gaps.  We discard
    # 12% at each endpoint to avoid interpolation errors near the knots.
    fit_rows: list[Sequence[object]] = []
    central = (-b1, b1)
    for n in range(4):
        for word in all_words(n):
            lo, hi = apply_word_interval(a, central, word)
            margin = 0.12 * (hi - lo)
            xs = np.linspace(lo + margin, hi - margin, max(60, 20 * (n + 1)))
            ys = interp_density(approx, xs)
            coefficients = np.polyfit(xs, ys, deg=n)
            fitted = np.polyval(coefficients, xs)
            exact_lead = exact_gap_leading_coefficient(a, word)
            lead = float(coefficients[0])
            max_residual = float(np.max(np.abs(fitted - ys)))
            fit_rows.append(
                (
                    n,
                    word or "empty",
                    f"{lo:.16g}",
                    f"{hi:.16g}",
                    f"{lead:.16g}",
                    f"{exact_lead:.16g}",
                    f"{abs(lead-exact_lead):.6g}",
                    f"{max_residual:.6g}",
                )
            )
    write_csv(
        OUTPUT_DIR / "polynomial_gap_fit_a3.csv",
        [
            "generation_degree",
            "word",
            "gap_left",
            "gap_right",
            "fitted_leading_coefficient",
            "exact_leading_coefficient",
            "leading_coefficient_absolute_error",
            "max_fit_residual",
        ],
        fit_rows,
    )

    fig, ax = plt.subplots(figsize=(9.0, 4.8))
    ax.plot(approx.x, approx.density, linewidth=1.5, label=r"fixed-point approximation to $h_3$")
    ax.axhline(a / 2.0, linewidth=0.8, linestyle="--", label=r"exact plateau height $3/2$")
    ax.axvspan(-b1, b1, alpha=0.15, label="generation-0 gap")
    for word in all_words(1):
        lo, hi = apply_word_interval(a, central, word)
        ax.axvspan(lo, hi, alpha=0.08)
    ax.set_xlabel(r"$x$")
    ax.set_ylabel(r"$h_3(x)$")
    ax.set_title(r"The smooth Cantor spline $h_3$")
    ax.set_xlim(-b, b)
    ax.grid(True, linewidth=0.4, alpha=0.4)
    ax.legend(loc="best", fontsize=9)
    fig.tight_layout()
    fig.savefig(OUTPUT_DIR / "ha_a3_density.png", dpi=220)
    plt.close(fig)


def experiment_local_degree_distribution() -> None:
    """Compare the exact geometric local-degree law with Monte Carlo."""

    a = 3.0
    b = 1.0 / (a - 1.0)
    sample_size = 400_000
    points = RNG.uniform(-b, b, size=sample_size)
    degree = classify_local_degree(a, points)
    unresolved = int(np.count_nonzero(degree < 0))

    max_degree = 13
    empirical = np.array([np.mean(degree == n) for n in range(max_degree + 1)])
    exact = np.array([(1.0 - 2.0 / a) * (2.0 / a) ** n for n in range(max_degree + 1)])

    n_values = np.arange(max_degree + 1)
    width = 0.42
    fig, ax = plt.subplots(figsize=(9.0, 4.8))
    ax.bar(n_values - width / 2.0, exact, width=width, label="exact geometric law")
    ax.bar(n_values + width / 2.0, empirical, width=width, label="uniform-point Monte Carlo")
    ax.set_xlabel("local polynomial degree")
    ax.set_ylabel("probability")
    ax.set_title(r"Local degree of $h_3$: $\Pr(D=n)=\frac{1}{3}(\frac{2}{3})^n$")
    ax.set_xticks(n_values)
    ax.grid(True, axis="y", linewidth=0.4, alpha=0.4)
    ax.legend(loc="best")
    fig.tight_layout()
    fig.savefig(OUTPUT_DIR / "local_degree_distribution.png", dpi=220)
    plt.close(fig)

    # Include the Monte Carlo numbers in the gap-length table's companion
    # diagnostics via a small text sidecar for reproducibility.
    with (OUTPUT_DIR / "local_degree_monte_carlo.txt").open("w", encoding="utf-8") as stream:
        stream.write(f"sample_size={sample_size}\n")
        stream.write(f"unresolved_after_depth_80={unresolved}\n")
        stream.write(f"empirical_mean={np.mean(degree[degree >= 0]):.16g}\n")
        stream.write(f"exact_mean={2.0/(a-2.0):.16g}\n")
        stream.write(f"empirical_variance={np.var(degree[degree >= 0]):.16g}\n")
        stream.write(f"exact_variance={2.0*a/(a-2.0)**2:.16g}\n")


def bernoulli_number_even(two_m: int) -> float:
    """Return B_{two_m} as a float using SciPy's Bernoulli table."""

    values = bernoulli(two_m)
    return float(values[two_m])


def uniform_even_cumulant(m: int) -> float:
    """Return kappa_{2m} of Uniform[-1,1]."""

    b2m = bernoulli_number_even(2 * m)
    return (2.0 ** (2 * m - 1) * b2m) / m


def up_even_cumulant(m: int) -> float:
    """Return kappa_{2m} of the random variable with density Up."""

    return uniform_even_cumulant(m) / (2.0 ** (2 * m) - 1.0)


def fup_even_cumulant(n: int, m: int) -> float:
    """Return kappa_{2m}(Z_n) for the generalized Fup random variable."""

    scale_power = 2.0 ** (-2 * m * n)
    return scale_power * (
        up_even_cumulant(m) + n * 2.0 ** (-2 * m) * uniform_even_cumulant(m)
    )


def sample_up(size: int, digits: int = 28) -> NDArray[np.float64]:
    """Sample X_2=sum 2^{-j}U_j with a negligible truncated tail."""

    result = np.zeros(size, dtype=np.float64)
    # Generate in modest blocks so peak memory stays small.
    for j in range(1, digits + 1):
        result += (2.0 ** (-j)) * RNG.uniform(-1.0, 1.0, size=size)
    return result


def experiment_fup_clt() -> None:
    """Verify the Fup central-limit scaling and exact cumulants."""

    sample_size = 350_000
    x_up = sample_up(sample_size)
    n_values = [1, 4, 16, 64]
    bins = np.linspace(-4.5, 4.5, 181)
    centers = 0.5 * (bins[:-1] + bins[1:])

    fig, ax = plt.subplots(figsize=(9.0, 5.0))
    cumulant_rows: list[Sequence[object]] = []

    for n in n_values:
        uniform_sum = np.zeros(sample_size, dtype=np.float64)
        # Chunk the summands to keep the code transparent and memory bounded.
        for _ in range(n):
            uniform_sum += RNG.uniform(-1.0, 1.0, size=sample_size)

        z = (2.0 ** (-n)) * x_up + (2.0 ** (-n - 1)) * uniform_sum
        variance = fup_even_cumulant(n, 1)
        standardized = z / math.sqrt(variance)
        hist, _ = np.histogram(standardized, bins=bins, density=True)
        ax.plot(centers, hist, linewidth=1.1, label=fr"$n={n}$")

        kappa4 = fup_even_cumulant(n, 2)
        kappa6 = fup_even_cumulant(n, 3)
        standardized_kappa4 = kappa4 / variance**2
        standardized_kappa6 = kappa6 / variance**3
        empirical_variance = float(np.var(standardized))
        empirical_kurtosis_cumulant = float(np.mean(standardized**4) - 3.0 * empirical_variance**2)
        cumulant_rows.append(
            (
                n,
                f"{variance:.16g}",
                f"{standardized_kappa4:.16g}",
                f"{standardized_kappa6:.16g}",
                f"{empirical_variance:.16g}",
                f"{empirical_kurtosis_cumulant:.16g}",
            )
        )

    ax.plot(centers, norm.pdf(centers), linewidth=2.0, linestyle="--", label=r"$N(0,1)$")
    ax.set_xlabel("standardized coordinate")
    ax.set_ylabel("density")
    ax.set_title("Gaussian limit in the generalized Fup hierarchy")
    ax.set_xlim(-4.5, 4.5)
    ax.grid(True, linewidth=0.4, alpha=0.4)
    ax.legend(loc="best", ncol=2)
    fig.tight_layout()
    fig.savefig(OUTPUT_DIR / "fup_clt.png", dpi=220)
    plt.close(fig)

    write_csv(
        OUTPUT_DIR / "fup_clt_cumulants.csv",
        [
            "n",
            "exact_variance_of_Z_n",
            "exact_standardized_kappa_4",
            "exact_standardized_kappa_6",
            "empirical_standardized_variance",
            "empirical_standardized_kappa_4",
        ],
        cumulant_rows,
    )


def write_general_parameter_table() -> None:
    """Tabulate exact geometric and probabilistic parameters of h_a."""

    rows: list[Sequence[object]] = []
    for a in (2.05, 2.1, 2.25, 2.5, 3.0, 4.0, 8.0):
        b = 1.0 / (a - 1.0)
        b1 = central_gap_halfwidth(a)
        dimension = math.log(2.0) / math.log(a)
        mean_degree = 2.0 / (a - 2.0)
        variance_degree = 2.0 * a / (a - 2.0) ** 2
        variance_x = 1.0 / (3.0 * (a * a - 1.0))
        rows.append(
            (
                f"{a:.8g}",
                f"{b:.16g}",
                f"{b1:.16g}",
                f"{dimension:.16g}",
                f"{mean_degree:.16g}",
                f"{variance_degree:.16g}",
                f"{variance_x:.16g}",
            )
        )

    write_csv(
        OUTPUT_DIR / "generalized_ha_parameters.csv",
        [
            "a",
            "support_halfwidth_b",
            "central_gap_halfwidth_b1",
            "Cantor_dimension_log2_loga",
            "mean_local_degree",
            "variance_local_degree",
            "variance_of_X_a",
        ],
        rows,
    )


def main() -> None:
    """Run every experiment and print a short manifest."""

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    experiment_ha_a3()
    experiment_local_degree_distribution()
    experiment_fup_clt()
    write_general_parameter_table()

    outputs = sorted(
        p.name
        for p in OUTPUT_DIR.iterdir()
        if p.suffix.lower() in {".png", ".csv", ".txt"}
        and p.name != "README.txt"
    )
    print("Generated numerical artifacts:")
    for name in outputs:
        print(f"  {name}")


if __name__ == "__main__":
    main()
