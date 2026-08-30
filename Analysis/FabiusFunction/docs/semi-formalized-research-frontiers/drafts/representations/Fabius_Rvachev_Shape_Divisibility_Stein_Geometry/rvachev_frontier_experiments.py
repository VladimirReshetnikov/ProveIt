#!/usr/bin/env python3
"""Numerical experiments for the Fabius/Rvachev frontier report.

The Rvachev up-function ``up`` is the probability density of

    Z = sum_{n >= 0} V_n / 2^(n+1),     V_n ~ Uniform[-1, 1],

and is the unique compactly supported continuous fixed point of

    p(x) = integral_{2x-1}^{2x+1} p(u) du,     p(u)=0 outside [-1,1].

This script approximates that fixed point on a uniform grid.  It then
computes:

* the score -p'(x)/p(x), whose strict increase is predicted by the
  strict-log-concavity theorem proved in the accompanying report;
* the canonical one-dimensional Stein kernel

      tau(x) = (1/p(x)) integral_x^1 t p(t) dt;

* the endpoint scale parameter rho(delta)=delta F'(delta)/F(delta),
  using F(delta)=up(1-delta), and the conjectural asymptotic diagnostic

      tau(1-delta) (rho(delta)+1) / delta -> 1.

The fixed-point discretization is deliberately elementary: NumPy's
trapezoidal cumulative integration and linear interpolation are enough
for all figures and tables in the report.  No external data are used.

Usage
-----
    python rvachev_frontier_experiments.py --output-dir numerical_output

The script writes PDF figures and CSV tables.  The defaults (200001 grid
points, 24 fixed-point iterations) reproduce the numerical values quoted
in the report on an ordinary desktop computer.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import matplotlib as mpl

mpl.rcParams["pdf.fonttype"] = 42
mpl.rcParams["ps.fonttype"] = 42

import matplotlib.pyplot as plt
import numpy as np
from numpy.typing import NDArray

FloatArray = NDArray[np.float64]


@dataclass(frozen=True)
class Approximation:
    """Container for the grid, up-density, derivatives, and Stein kernel."""

    x: FloatArray
    p: FloatArray
    p_prime: FloatArray
    p_second: FloatArray
    tau: FloatArray


def cumulative_trapezoid(values: FloatArray, dx: float) -> FloatArray:
    """Return C[i] = integral from the left endpoint through grid point i."""

    result = np.empty_like(values)
    result[0] = 0.0
    result[1:] = np.cumsum((values[:-1] + values[1:]) * (0.5 * dx))
    return result


def interpolate_with_zero_outside(
    points: FloatArray, grid: FloatArray, values: FloatArray
) -> FloatArray:
    """Linearly interpolate on [-1,1] and return zero outside the support."""

    clipped = np.clip(points, grid[0], grid[-1])
    result = np.interp(clipped, grid, values)
    outside = (points < grid[0]) | (points > grid[-1])
    result[outside] = 0.0
    return result


def fixed_point_density(grid_size: int, iterations: int) -> tuple[FloatArray, FloatArray]:
    """Approximate the Rvachev up-density by iterating its integral equation.

    We start from the uniform density on [-1,1].  If p is any density on
    this interval, the update

        (T p)(x) = integral_{max(-1,2x-1)}^{min(1,2x+1)} p(u) du

    is again a symmetric probability density.  The fixed point is ``up``.
    Symmetrization and renormalization remove only roundoff-level drift.
    """

    if grid_size < 1001 or grid_size % 2 == 0:
        raise ValueError("grid_size must be an odd integer at least 1001")
    if iterations < 1:
        raise ValueError("iterations must be positive")

    x = np.linspace(-1.0, 1.0, grid_size, dtype=np.float64)
    dx = float(x[1] - x[0])
    p = np.full_like(x, 0.5)  # Uniform[-1,1].

    for _ in range(iterations):
        primitive = cumulative_trapezoid(p, dx)
        lower = np.clip(2.0 * x - 1.0, -1.0, 1.0)
        upper = np.clip(2.0 * x + 1.0, -1.0, 1.0)
        p = np.interp(upper, x, primitive) - np.interp(lower, x, primitive)
        p = 0.5 * (p + p[::-1])
        p /= np.trapezoid(p, x)

    return x, p


def differentiate_by_refinement(x: FloatArray, p: FloatArray) -> tuple[FloatArray, FloatArray]:
    """Evaluate the first two derivatives from exact refinement identities.

    Differentiating

        p(x) = integral_{2x-1}^{2x+1} p(u) du

    gives

        p'(x)  = 2[p(2x+1)-p(2x-1)],
        p''(x) = 4[p'(2x+1)-p'(2x-1)].

    These formulas are much more stable than finite differences in the
    very flat central region and near the rapidly decaying endpoints.
    """

    p_left = interpolate_with_zero_outside(2.0 * x - 1.0, x, p)
    p_right = interpolate_with_zero_outside(2.0 * x + 1.0, x, p)
    p_prime = 2.0 * (p_right - p_left)

    dp_left = interpolate_with_zero_outside(2.0 * x - 1.0, x, p_prime)
    dp_right = interpolate_with_zero_outside(2.0 * x + 1.0, x, p_prime)
    p_second = 4.0 * (dp_right - dp_left)
    return p_prime, p_second


def stein_kernel(x: FloatArray, p: FloatArray) -> FloatArray:
    """Compute the even Stein kernel by stable one-sided quadrature.

    For x >= 0 we evaluate

        tau(x) = p(x)^(-1) integral_x^1 t p(t) dt,

    whose integrand is nonnegative and therefore does not suffer
    cancellation.  The Rvachev density is even, so its canonical Stein
    kernel is even as well; values for x < 0 are obtained by reflection.
    This is materially more stable than directly integrating from a
    negative x, where an almost exact cancellation of the positive and
    negative first moments is divided by an extremely small endpoint
    density.  Points where the density underflows are stored as NaN.
    """

    if x.size % 2 == 0 or not np.isclose(x[x.size // 2], 0.0):
        raise ValueError("the Stein-kernel grid must be odd and centered at zero")

    dx = float(x[1] - x[0])
    center = x.size // 2
    x_positive = x[center:]
    p_positive = p[center:]
    integrand = x_positive * p_positive
    interval_areas = (integrand[:-1] + integrand[1:]) * (0.5 * dx)

    tail_positive = np.empty_like(x_positive)
    tail_positive[-1] = 0.0
    tail_positive[:-1] = np.cumsum(interval_areas[::-1])[::-1]

    threshold = 1.0e-25
    tau_positive = np.full_like(p_positive, np.nan)
    np.divide(
        tail_positive,
        p_positive,
        out=tau_positive,
        where=p_positive > threshold,
    )

    tau = np.empty_like(p)
    tau[center:] = tau_positive
    tau[:center] = tau_positive[1:][::-1]
    return tau


def build_approximation(grid_size: int, iterations: int) -> Approximation:
    """Construct all numerical fields used by the report."""

    x, p = fixed_point_density(grid_size, iterations)
    p_prime, p_second = differentiate_by_refinement(x, p)
    tau = stein_kernel(x, p)
    return Approximation(x=x, p=p, p_prime=p_prime, p_second=p_second, tau=tau)


def at(value: float, x: FloatArray, y: FloatArray) -> float:
    """Interpolate a scalar field at one point."""

    return float(np.interp(value, x, y))


def endpoint_diagnostics(
    approximation: Approximation, deltas: Iterable[float]
) -> list[dict[str, float]]:
    """Compute endpoint quantities appearing in the asymptotic conjecture.

    For 0 < delta < 1/2, the Fabius/Rvachev relation gives

        F(delta)  = p(1-delta),
        F'(delta) = 2 F(2 delta) = 2 p(1-2 delta).

    Hence rho(delta)=delta F'(delta)/F(delta) is obtained without numerical
    differentiation.
    """

    rows: list[dict[str, float]] = []
    x, p, tau = approximation.x, approximation.p, approximation.tau
    for delta in deltas:
        p_endpoint = at(1.0 - delta, x, p)
        f_prime = 2.0 * at(1.0 - 2.0 * delta, x, p)
        rho = delta * f_prime / p_endpoint
        tau_endpoint = at(1.0 - delta, x, tau)
        rows.append(
            {
                "delta": delta,
                "tau_1_minus_delta": tau_endpoint,
                "rho": rho,
                "tau_times_rho_over_delta": tau_endpoint * rho / delta,
                "tau_times_rho_plus_one_over_delta": tau_endpoint * (rho + 1.0) / delta,
            }
        )
    return rows


def write_csv(path: Path, rows: list[dict[str, object]]) -> None:
    """Write a homogeneous list of dictionaries as a CSV file."""

    if not rows:
        raise ValueError("cannot write an empty CSV table")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=list(rows[0].keys()), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def save_density_figure(approximation: Approximation, output_dir: Path) -> None:
    """Plot the Rvachev up-density."""

    fig, ax = plt.subplots(figsize=(7.0, 4.4))
    ax.plot(approximation.x, approximation.p)
    ax.set_xlabel("x")
    ax.set_ylabel("up(x)")
    ax.set_title("Rvachev up-density from the refinement fixed point")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "up_density.pdf")
    plt.close(fig)


def save_score_figure(approximation: Approximation, output_dir: Path) -> None:
    """Plot the positive-half score -p'/p and its dyadic ratio form."""

    x, p, p_prime = approximation.x, approximation.p, approximation.p_prime
    mask = (x >= 0.0) & (x <= 0.99) & (p > 1.0e-14)
    score = -p_prime[mask] / p[mask]

    fig, ax = plt.subplots(figsize=(7.0, 4.4))
    ax.plot(x[mask], score)
    ax.set_xlabel("x")
    ax.set_ylabel("-up'(x) / up(x)")
    ax.set_title("Increasing score predicted by strict log-concavity")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "score_monotonicity.pdf")
    plt.close(fig)


def save_stein_figure(approximation: Approximation, output_dir: Path) -> None:
    """Plot the even canonical Stein kernel."""

    mask = np.isfinite(approximation.tau)
    fig, ax = plt.subplots(figsize=(7.0, 4.4))
    ax.plot(approximation.x[mask], approximation.tau[mask])
    ax.set_xlabel("x")
    ax.set_ylabel("tau(x)")
    ax.set_title("Canonical Stein kernel of the Rvachev distribution")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "stein_kernel.pdf")
    plt.close(fig)


def save_endpoint_figure(rows: list[dict[str, float]], output_dir: Path) -> None:
    """Plot the normalized endpoint ratio used to test the conjecture."""

    delta = np.array([row["delta"] for row in rows], dtype=np.float64)
    ratio = np.array(
        [row["tau_times_rho_plus_one_over_delta"] for row in rows],
        dtype=np.float64,
    )
    order = np.argsort(delta)

    fig, ax = plt.subplots(figsize=(7.0, 4.4))
    ax.plot(delta[order], ratio[order], marker="o")
    ax.axhline(1.0, linewidth=1.0)
    ax.set_xscale("log")
    ax.set_xlabel("delta")
    ax.set_ylabel("tau(1-delta) [rho(delta)+1] / delta")
    ax.set_title("Endpoint Stein-kernel asymptotic diagnostic")
    ax.grid(True, alpha=0.25)
    fig.tight_layout()
    fig.savefig(output_dir / "endpoint_stein_ratio.pdf")
    plt.close(fig)


def validate(approximation: Approximation) -> dict[str, float]:
    """Run consistency checks and return aggregate numerical diagnostics."""

    x, p, p_prime, p_second, tau = (
        approximation.x,
        approximation.p,
        approximation.p_prime,
        approximation.p_second,
        approximation.tau,
    )

    mass = float(np.trapezoid(p, x))
    symmetry_error = float(np.max(np.abs(p - p[::-1])))
    mean_tau = float(np.trapezoid(np.nan_to_num(tau) * p, x))
    second_tau = float(np.trapezoid(np.nan_to_num(tau) ** 2 * p, x))
    normalized_stein_discrepancy = 81.0 * (second_tau - (1.0 / 9.0) ** 2)

    # Pointwise log-concavity diagnostic p p'' - (p')^2 <= 0, excluding
    # the under-resolved extreme endpoint tail.
    safe = (np.abs(x) < 0.995) & (p > 1.0e-10)
    log_concavity_defect_max = float(np.max(p[safe] * p_second[safe] - p_prime[safe] ** 2))

    # The Stein ODE tau' + (p'/p) tau = -x gives a stable monotonicity check.
    positive = (x >= 0.0) & (x <= 0.99) & (p > 1.0e-14) & np.isfinite(tau)
    tau_prime = -x[positive] - tau[positive] * p_prime[positive] / p[positive]
    tau_prime_max = float(np.max(tau_prime))

    checks = {
        "probability_mass": mass,
        "symmetry_error": symmetry_error,
        "up_at_zero": at(0.0, x, p),
        "up_at_one_half": at(0.5, x, p),
        "score_at_one_half": -at(0.5, x, p_prime) / at(0.5, x, p),
        "tau_at_zero": at(0.0, x, tau),
        "tau_at_one_half": at(0.5, x, tau),
        "mean_tau": mean_tau,
        "second_moment_tau": second_tau,
        "normalized_stein_discrepancy": normalized_stein_discrepancy,
        "max_log_concavity_defect": log_concavity_defect_max,
        "max_sampled_tau_derivative_on_0_to_0_99": tau_prime_max,
    }

    # Exact identities used in the report.  Tolerances are deliberately much
    # looser than the observed errors, so the script remains portable.
    if abs(mass - 1.0) > 2.0e-9:
        raise RuntimeError(f"density normalization failed: mass={mass}")
    if symmetry_error > 2.0e-12:
        raise RuntimeError(f"density symmetry failed: error={symmetry_error}")
    if abs(checks["up_at_zero"] - 1.0) > 2.0e-7:
        raise RuntimeError("up(0)=1 consistency check failed")
    if abs(checks["up_at_one_half"] - 0.5) > 2.0e-7:
        raise RuntimeError("up(1/2)=1/2 consistency check failed")
    if abs(checks["tau_at_zero"] - 5.0 / 36.0) > 2.0e-7:
        raise RuntimeError("tau(0)=5/36 consistency check failed")
    if abs(checks["tau_at_one_half"] - 1.0 / 12.0) > 2.0e-7:
        raise RuntimeError("tau(1/2)=1/12 consistency check failed")
    if abs(mean_tau - 1.0 / 9.0) > 2.0e-7:
        raise RuntimeError("E[tau(Z)]=Var(Z)=1/9 consistency check failed")

    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("numerical_output"),
        help="directory for PDF figures and CSV tables",
    )
    parser.add_argument(
        "--grid-size",
        type=int,
        default=200_001,
        help="odd number of uniform grid points on [-1,1]",
    )
    parser.add_argument(
        "--iterations",
        type=int,
        default=24,
        help="number of fixed-point refinement iterations",
    )
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    approximation = build_approximation(args.grid_size, args.iterations)
    checks = validate(approximation)

    sample_points = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99]
    sample_rows: list[dict[str, float]] = []
    for point in sample_points:
        density = at(point, approximation.x, approximation.p)
        derivative = at(point, approximation.x, approximation.p_prime)
        sample_rows.append(
            {
                "x": point,
                "up_x": density,
                "stein_tau_x": at(point, approximation.x, approximation.tau),
                "score_minus_up_prime_over_up": -derivative / density,
            }
        )

    deltas = [0.25, 0.125, 0.1, 0.05, 0.025, 0.02, 0.01]
    endpoint_rows = endpoint_diagnostics(approximation, deltas)

    write_csv(args.output_dir / "pointwise_values.csv", sample_rows)
    write_csv(args.output_dir / "endpoint_diagnostics.csv", endpoint_rows)
    write_csv(
        args.output_dir / "global_diagnostics.csv",
        [{"quantity": name, "value": value} for name, value in checks.items()],
    )
    with (args.output_dir / "global_diagnostics_readable.txt").open(
        "w", encoding="utf-8"
    ) as handle:
        for name, value in checks.items():
            handle.write(f"{name}: {value:.16g}\n")

    save_density_figure(approximation, args.output_dir)
    save_score_figure(approximation, args.output_dir)
    save_stein_figure(approximation, args.output_dir)
    save_endpoint_figure(endpoint_rows, args.output_dir)

    print(f"Wrote numerical output to {args.output_dir.resolve()}")
    for name, value in checks.items():
        print(f"{name}: {value:.16g}")


if __name__ == "__main__":
    main()
