#!/usr/bin/env python3
"""Numerical and exact-arithmetic experiments for Fabius monomial antiderivatives.

This script accompanies the report
    Dyadic Primitive Ladders and Mellin--Newton Antiderivatives
    for the Fabius--Rvachev System.

It deliberately uses two substantially different representations:

1. A dyadic-grid fixed-point iteration for the bounded Fabius function F.
2. The exact rational recurrence for the moment sequence d_n.

The grid is used to check pointwise antiderivative and inverse-quantile formulas.
The moment recurrence is used to check complete integrals and fractional/negative
Newton series without numerical differentiation near the infinitely flat endpoints.

No network access is required.  Dependencies: Python 3.10+, NumPy, SciPy,
Matplotlib.  All generated CSV/PNG files are placed next to this script unless
--output-dir is supplied.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import cumulative_trapezoid, trapezoid


# ---------------------------------------------------------------------------
# Exact moments and exact inverse-dyadic values
# ---------------------------------------------------------------------------


def exact_half_moments(count: int) -> list[Fraction]:
    """Return d_0,...,d_count exactly as Fractions.

    The recurrence is

        (n+1)(2^n-1)d_n = sum_{k=0}^{n-1} binom(n+1,k)d_k.

    In the probabilistic normalization of the report, d_n = E[X^n], where
    X has distribution function F.  The same sequence satisfies

        F(2^{-n}) = d_n / (n! 2^{n choose 2}).
    """

    if count < 0:
        raise ValueError("count must be nonnegative")
    d = [Fraction(0) for _ in range(count + 1)]
    d[0] = Fraction(1)
    for n in range(1, count + 1):
        numerator = sum(Fraction(math.comb(n + 1, k)) * d[k] for k in range(n))
        denominator = (n + 1) * (2**n - 1)
        d[n] = numerator / denominator
    return d


def float_half_moments(count: int) -> np.ndarray:
    """Return d_0,...,d_count in IEEE double precision.

    The binomial row is generated multiplicatively, avoiding repeated calls to
    math.comb.  count=900 is safe in double precision because 2^900 is finite.
    """

    if not (0 <= count <= 1000):
        raise ValueError("count must be in 0..1000 for this double-precision routine")
    d = np.zeros(count + 1, dtype=np.float64)
    d[0] = 1.0
    for n in range(1, count + 1):
        coefficient = 1.0  # C(n+1,0)
        total = d[0]
        for k in range(1, n):
            coefficient *= (n + 2 - k) / k  # C(n+1,k) from C(n+1,k-1)
            total += coefficient * d[k]
        d[n] = total / ((n + 1) * (2.0**n - 1.0))
    return d


def exact_fabius_inverse_power(n: int, d: Sequence[Fraction]) -> Fraction:
    """Return F(2^{-n}) exactly from d_n."""

    if n < 0 or n >= len(d):
        raise ValueError("n is outside the supplied moment table")
    return d[n] / (math.factorial(n) * 2 ** (n * (n - 1) // 2))


# ---------------------------------------------------------------------------
# Dyadic-grid approximation to F
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FabiusGrid:
    x: np.ndarray
    f: np.ndarray

    @property
    def step(self) -> float:
        return float(self.x[1] - self.x[0])

    def value(self, arg: float | np.ndarray) -> float | np.ndarray:
        """Linearly interpolate F, with exact constant extension outside [0,1]."""

        values = np.interp(arg, self.x, self.f, left=0.0, right=1.0)
        if np.isscalar(arg):
            return float(values)
        return values

    def up(self, arg: float | np.ndarray) -> float | np.ndarray:
        """Evaluate up(x)=F(1-|x|) by interpolation."""

        a = np.asarray(arg)
        values = self.value(1.0 - np.abs(a))
        if np.isscalar(arg):
            return float(values)
        return values


def build_fabius_grid(power: int = 18, iterations: int = 36) -> FabiusGrid:
    """Approximate F on a dyadic grid by iterating its integral equation.

    For 0 <= x <= 1/2,

        F(x) = integral_0^{2x} F(t) dt,

    and F(1-x)=1-F(x).  The grid size is 2**power+1, so the map x -> 2x
    lands exactly on grid nodes on the left half.  The initial function x is
    already symmetric and monotone.  Iteration rapidly stabilizes for the
    resolutions used here.
    """

    if power < 8:
        raise ValueError("power should be at least 8")
    if iterations < 1:
        raise ValueError("iterations must be positive")

    n = 2**power
    x = np.linspace(0.0, 1.0, n + 1)
    f = x.copy()
    half = n // 2
    h = 1.0 / n

    for _ in range(iterations):
        cumulative = np.empty(n + 1)
        cumulative[0] = 0.0
        cumulative[1:] = np.cumsum((f[:-1] + f[1:]) * (0.5 * h))

        next_f = np.empty_like(f)
        next_f[: half + 1] = cumulative[0 : n + 1 : 2]
        # Symmetry determines nodes strictly to the right of 1/2.
        next_f[half + 1 :] = 1.0 - next_f[half - 1 :: -1]
        next_f[0] = 0.0
        next_f[-1] = 1.0
        f = next_f

    # Suppress tiny monotonicity violations from roundoff; this is also useful
    # when inverting the sampled CDF by interpolation.
    f = np.maximum.accumulate(f)
    f[half] = 0.5
    return FabiusGrid(x=x, f=f)


# ---------------------------------------------------------------------------
# Closed forms and direct quadrature
# ---------------------------------------------------------------------------


def rising_integer(n: int, k: int) -> int:
    """Return the rising factorial (n)_k for positive integer n."""

    result = 1
    for j in range(k):
        result *= n + j
    return result


def falling_integer(p: int, k: int) -> int:
    """Return the falling factorial p^(underline k)."""

    if k > p:
        return 0
    result = 1
    for j in range(k):
        result *= p - j
    return result


def primitive_ladder(grid: FabiusGrid, order: int, x: float) -> float:
    """Evaluate J_order(x)=2^{order choose 2}F(x/2^order).

    J_0=F and J_{m+1}'=J_m.  For the modest orders used in pointwise
    tests, interpolation remains accurate after multiplication by the scale.
    """

    if order < 0:
        raise ValueError("order must be nonnegative")
    scale = 2.0 ** (order * (order - 1) // 2)
    return scale * grid.value(x / (2.0**order))


def monomial_nfold_formula(grid: FabiusGrid, p: int, n: int, x: float) -> float:
    """Closed form for the normalized n-fold primitive of x^p F(x)."""

    total = 0.0
    for k in range(p + 1):
        coefficient = ((-1) ** k) * math.comb(p, k) * rising_integer(n, k)
        total += coefficient * (x ** (p - k)) * primitive_ladder(grid, n + k, x)
    return total


def monomial_nfold_direct(grid: FabiusGrid, p: int, n: int, x: float) -> float:
    """Direct Cauchy-kernel quadrature for the normalized n-fold primitive."""

    mask = grid.x <= x
    t = grid.x[mask]
    f = grid.f[mask]
    if t[-1] < x:
        t = np.append(t, x)
        f = np.append(f, grid.value(x))
    integrand = ((x - t) ** (n - 1)) * (t**p) * f / math.factorial(n - 1)
    return float(trapezoid(integrand, t))


def up_monomial_nfold_formula(grid: FabiusGrid, p: int, n: int, x: float) -> float:
    """Normalized-from--1 n-fold primitive of x^p up(x), -1 <= x <= 1.

    It uses up(x)=mathcal F(x+1) and the shifted primitive ladder.  All sampled
    F arguments lie in [0,1].
    """

    if not (-1.0 <= x <= 1.0):
        raise ValueError("the displayed shifted formula is intended for -1 <= x <= 1")
    total = 0.0
    for k in range(p + 1):
        m = n + k
        coefficient = ((-1) ** k) * math.comb(p, k) * rising_integer(n, k)
        ladder = (2.0 ** (m * (m - 1) // 2)) * grid.value((x + 1.0) / (2.0**m))
        total += coefficient * (x ** (p - k)) * ladder
    return total


def up_monomial_nfold_direct(grid: FabiusGrid, p: int, n: int, x: float) -> float:
    """Direct Cauchy-kernel quadrature from -1 to x for t^p up(t)."""

    # Uniform grid on [-1,x], chosen fine enough to match the F grid scale.
    count = max(4001, int(round((x + 1.0) / grid.step)) + 1)
    t = np.linspace(-1.0, x, count)
    integrand = ((x - t) ** (n - 1)) * (t**p) * grid.up(t) / math.factorial(n - 1)
    return float(trapezoid(integrand, t))


def complete_newton_series(alpha: float, d: np.ndarray, terms: int) -> float:
    """Partial sum for integral_0^1 x^alpha F(x) dx.

        sum_{k>=0} (-1)^k binom(alpha,k) d_{k+1}/(k+1).
    """

    if terms < 1 or terms >= len(d):
        raise ValueError("terms must be positive and below the moment-table length")
    total = 0.0
    coefficient = 1.0  # binom(alpha,0)
    for k in range(terms):
        if k > 0:
            coefficient *= (alpha - (k - 1)) / k
        total += ((-1.0) ** k) * coefficient * d[k + 1] / (k + 1)
    return total


def complete_integral_from_distribution(alpha: float, grid: FabiusGrid) -> float:
    """Grid quadrature for integral_0^1 x^alpha F(x) dx.

    At x=0, set the product to zero.  Infinite flatness makes this correct for
    every real alpha, including negative alpha.
    """

    x = grid.x
    values = np.zeros_like(x)
    positive = x > 0.0
    values[positive] = (x[positive] ** alpha) * grid.f[positive]
    return float(trapezoid(values, x))


def inverse_quantile_integral(grid: FabiusGrid, y: float, p: int, samples: int = 200_001) -> float:
    """Numerically integrate Q(v)^p from 0 to y by inverting the sampled CDF."""

    v = np.linspace(0.0, y, samples)
    q = np.interp(v, grid.f, grid.x)
    return float(trapezoid(q**p, v))


# ---------------------------------------------------------------------------
# Experiment driver and output
# ---------------------------------------------------------------------------


def write_rows(path: Path, rows: Iterable[dict[str, object]], fieldnames: Sequence[str]) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def run(output_dir: Path, grid_power: int, iterations: int, moment_count: int) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Building F grid with 2^{grid_power}+1 nodes ...")
    grid = build_fabius_grid(grid_power, iterations)
    exact_d = exact_half_moments(20)
    float_d = float_half_moments(moment_count)

    # 1. Grid sanity checks at reciprocal powers of two.
    grid_rows: list[dict[str, object]] = []
    for n in range(1, 9):
        exact = exact_fabius_inverse_power(n, exact_d)
        approximate = grid.value(2.0 ** (-n))
        grid_rows.append(
            {
                "n": n,
                "x": f"2^-{n}",
                "exact": str(exact),
                "approximate": f"{approximate:.17g}",
                "absolute_error": f"{abs(approximate - float(exact)):.6e}",
            }
        )
    write_rows(
        output_dir / "grid_inverse_power_checks.csv",
        grid_rows,
        ["n", "x", "exact", "approximate", "absolute_error"],
    )

    # 2. Pointwise finite closed forms for F.
    finite_rows: list[dict[str, object]] = []
    test_x = [0.3125, 0.375, 0.625, 0.8125]
    for x in test_x:
        for n in (1, 2, 3):
            for p in range(0, 7):
                formula = monomial_nfold_formula(grid, p, n, x)
                direct = monomial_nfold_direct(grid, p, n, x)
                finite_rows.append(
                    {
                        "x": x,
                        "n": n,
                        "p": p,
                        "formula": f"{formula:.17g}",
                        "direct_quadrature": f"{direct:.17g}",
                        "absolute_error": f"{abs(formula - direct):.6e}",
                    }
                )
    write_rows(
        output_dir / "fabius_finite_primitive_checks.csv",
        finite_rows,
        ["x", "n", "p", "formula", "direct_quadrature", "absolute_error"],
    )

    # 3. Shifted Rvachev formulas on both halves of the support.
    up_rows: list[dict[str, object]] = []
    for x in (-0.75, -0.25, 0.25, 0.75):
        for n in (1, 2, 3):
            for p in range(0, 6):
                formula = up_monomial_nfold_formula(grid, p, n, x)
                direct = up_monomial_nfold_direct(grid, p, n, x)
                up_rows.append(
                    {
                        "x": x,
                        "n": n,
                        "p": p,
                        "formula": f"{formula:.17g}",
                        "direct_quadrature": f"{direct:.17g}",
                        "absolute_error": f"{abs(formula - direct):.6e}",
                    }
                )
    write_rows(
        output_dir / "rvachev_shifted_primitive_checks.csv",
        up_rows,
        ["x", "n", "p", "formula", "direct_quadrature", "absolute_error"],
    )

    # 4. Exact moment identity for complete integer-power integrals.
    exact_rows: list[dict[str, object]] = []
    for p in range(0, 13):
        finite_sum = sum(
            Fraction((-1) ** k * math.comb(p, k), k + 1) * exact_d[k + 1]
            for k in range(p + 1)
        )
        compact = (Fraction(1) - exact_d[p + 1]) / (p + 1)
        exact_rows.append(
            {
                "p": p,
                "finite_newton_sum": str(finite_sum),
                "compact_moment_form": str(compact),
                "equal": finite_sum == compact,
            }
        )
    write_rows(
        output_dir / "complete_integer_exact_checks.csv",
        exact_rows,
        ["p", "finite_newton_sum", "compact_moment_form", "equal"],
    )

    # 5. Fractional and negative complete integrals.
    fractional_rows: list[dict[str, object]] = []
    alphas = (-2.0, -1.0, -0.5, 0.5, 1.5, math.sqrt(2.0))
    term_counts = (8, 16, 32, 64, 128, 256, 512, min(900, moment_count))
    term_counts = tuple(sorted(set(t for t in term_counts if t < len(float_d))))
    for alpha in alphas:
        grid_value = complete_integral_from_distribution(alpha, grid)
        reference = complete_newton_series(alpha, float_d, term_counts[-1])
        for terms in term_counts:
            partial = complete_newton_series(alpha, float_d, terms)
            fractional_rows.append(
                {
                    "alpha": f"{alpha:.15g}",
                    "terms": terms,
                    "partial_sum": f"{partial:.17g}",
                    "reference_series": f"{reference:.17g}",
                    "series_tail_proxy": f"{abs(partial-reference):.6e}",
                    "grid_quadrature": f"{grid_value:.17g}",
                    "grid_difference": f"{abs(partial-grid_value):.6e}",
                }
            )
    write_rows(
        output_dir / "fractional_complete_series_checks.csv",
        fractional_rows,
        [
            "alpha",
            "terms",
            "partial_sum",
            "reference_series",
            "series_tail_proxy",
            "grid_quadrature",
            "grid_difference",
        ],
    )

    # 6. Negative-power tail diagnostics.
    #
    # For alpha=-a<0 all Newton terms are positive:
    #
    #   t_k(a) = C(a+k-1,k) d_{k+1}/(k+1).
    #
    # The known log-normal-scale envelope for d_n implies that the term
    # envelope has a local logarithmic slope containing (a-3/2).  When the
    # tail is estimated after the endpoint-Laplace substitution x=exp(u), the
    # Jacobian contributes one further unit; hence the first tail model is
    #
    #   R_N(a) ~ N t_N(a) / (log(N)/log(2) - (a-1/2)).
    #
    # This omits the bounded log-periodic derivative from the refined endpoint
    # asymptotic, so the CSV is diagnostic evidence rather than a proof.  Since
    # all terms are positive, the reference tail is summed directly instead of
    # subtracting two nearly equal partial sums.
    negative_tail_rows: list[dict[str, object]] = []
    reference_terms = min(900, moment_count)
    for a in (0.5, 1.0, 2.0, 3.0):
        generalized_coefficient = 1.0
        positive_terms: list[float] = []
        for k in range(reference_terms):
            if k > 0:
                generalized_coefficient *= (a + k - 1.0) / k
            positive_terms.append(generalized_coefficient * float_d[k + 1] / (k + 1))

        reference = math.fsum(positive_terms)
        for terms in (25, 50, 100, 200, 400):
            if terms >= reference_terms:
                continue
            partial = math.fsum(positive_terms[:terms])
            actual_tail = math.fsum(positive_terms[terms:])
            first_omitted_term = positive_terms[terms]
            denominator = math.log(terms) / math.log(2.0) - (a - 0.5)
            hazard_tail = terms * first_omitted_term / denominator
            negative_tail_rows.append(
                {
                    "a=-alpha": f"{a:.15g}",
                    "terms_N": terms,
                    "partial_sum": f"{partial:.17g}",
                    "actual_tail_to_reference": f"{actual_tail:.17g}",
                    "first_omitted_term": f"{first_omitted_term:.17g}",
                    "hazard_tail_approximation": f"{hazard_tail:.17g}",
                    "approximation_over_actual": f"{hazard_tail/actual_tail:.12g}",
                    "reference_terms": reference_terms,
                }
            )
    write_rows(
        output_dir / "negative_power_tail_checks.csv",
        negative_tail_rows,
        [
            "a=-alpha",
            "terms_N",
            "partial_sum",
            "actual_tail_to_reference",
            "first_omitted_term",
            "hazard_tail_approximation",
            "approximation_over_actual",
            "reference_terms",
        ],
    )

    # 7. Inverse-quantile area formulas at q=1/4, y=F(q)=5/72.
    q = Fraction(1, 4)
    y = Fraction(5, 72)
    inverse_rows: list[dict[str, object]] = []
    # Exact formula y q^p - p A_{p-1}(q), with A evaluated by the finite ladder.
    for p in range(1, 7):
        a = Fraction(0)
        for k in range(p):
            m = k + 1
            fabius_value = exact_fabius_inverse_power(m + 2, exact_d)  # q/2^m=2^{-(m+2)}
            ladder = Fraction(2 ** (m * (m - 1) // 2)) * fabius_value
            a += Fraction((-1) ** k * falling_integer(p - 1, k)) * (q ** (p - 1 - k)) * ladder
        exact_value = y * (q**p) - p * a
        numerical = inverse_quantile_integral(grid, float(y), p)
        inverse_rows.append(
            {
                "p": p,
                "q": str(q),
                "y=F(q)": str(y),
                "exact_integral": str(exact_value),
                "decimal_exact": f"{float(exact_value):.17g}",
                "quantile_quadrature": f"{numerical:.17g}",
                "absolute_error": f"{abs(numerical-float(exact_value)):.6e}",
            }
        )
    write_rows(
        output_dir / "inverse_quantile_exact_checks.csv",
        inverse_rows,
        ["p", "q", "y=F(q)", "exact_integral", "decimal_exact", "quantile_quadrature", "absolute_error"],
    )

    # 8. A convergence plot for three representative exponents.
    plt.figure(figsize=(7.2, 4.6))
    plot_counts = np.array([4, 8, 16, 32, 64, 128, 256, 512, min(900, moment_count)])
    plot_counts = np.unique(plot_counts[plot_counts < len(float_d)])
    for alpha in (-2.0, -0.5, 0.5):
        reference = complete_newton_series(alpha, float_d, int(plot_counts[-1]))
        errors = [
            max(abs(complete_newton_series(alpha, float_d, int(t)) - reference), 1e-18)
            for t in plot_counts
        ]
        plt.loglog(plot_counts, errors, marker="o", label=rf"$\alpha={alpha:g}$")
    plt.xlabel("number of Newton terms")
    plt.ylabel("absolute difference from longest sum")
    plt.title("Convergence of complete Mellin--Newton series")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "newton_series_convergence.png", dpi=180)
    plt.close()

    # Human-readable summary used when auditing the report tables.
    max_finite_error = max(float(row["absolute_error"]) for row in finite_rows)
    max_up_error = max(float(row["absolute_error"]) for row in up_rows)
    max_inverse_error = max(float(row["absolute_error"]) for row in inverse_rows)
    summary = output_dir / "run_summary.txt"
    summary.write_text(
        "\n".join(
            [
                "Fabius integral experiment summary",
                f"grid nodes: {len(grid.x)}",
                f"fixed-point iterations: {iterations}",
                f"moment count: {moment_count}",
                f"max finite F primitive error: {max_finite_error:.6e}",
                f"max shifted up primitive error: {max_up_error:.6e}",
                f"max inverse-quantile error: {max_inverse_error:.6e}",
                f"F(1/4) grid: {grid.value(0.25):.17g}",
                f"F(1/4) exact: {float(Fraction(5,72)):.17g}",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    print(summary.read_text(encoding="utf-8"), end="")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for CSV, PNG, and summary outputs",
    )
    parser.add_argument("--grid-power", type=int, default=18, help="grid has 2^power+1 nodes")
    parser.add_argument("--iterations", type=int, default=36, help="fixed-point iteration count")
    parser.add_argument("--moment-count", type=int, default=900, help="largest floating moment index")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    run(args.output_dir, args.grid_power, args.iterations, args.moment_count)


if __name__ == "__main__":
    main()
