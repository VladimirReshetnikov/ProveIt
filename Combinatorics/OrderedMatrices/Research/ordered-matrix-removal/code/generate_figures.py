#!/usr/bin/env python3
"""Reproduce the sampling figures for the five-by-five obstruction.

Dependencies: Python 3, NumPy, SciPy, Matplotlib.
Run: python3 generate_figures.py

Outputs are vector PDFs, PNG previews, and a numerical JSON receipt in
../figures/. No matrix is constructed. All large-depth probabilities use
log1p/expm1; the Bernoulli probabilities are exact analytic formulas evaluated
in floating-point arithmetic. Optimizer locations are numerical approximations,
not interval-certified enclosures, and no uniqueness claim is made.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
import numpy as np
from scipy.optimize import brentq, minimize_scalar


ANCHOR_SIZE = 3
DEPTHS = (12, 24, 48)
COLORS = ("#225EA8", "#087F8C", "#C27720")
INK = "#243247"
GRID = "#E1E6EB"


def at_least_one(probability: float, trials: int | float) -> float:
    """1-(1-probability)**trials without catastrophic cancellation."""
    if probability <= 0.0:
        return 0.0
    if probability >= 1.0:
        return 1.0
    return -math.expm1(trials * math.log1p(-probability))


def bernoulli_detection(depth: int, p: float, s: int = ANCHOR_SIZE) -> float:
    """Exact balanced Bernoulli detection law, including anchors and dummy."""
    m = 1 << depth
    group_ready = at_least_one(p, m)
    anchors_ready = group_ready ** (2 * s)
    parent_ready = p * (2.0 - p)
    one_parity = at_least_one(parent_ready * p * p, m // 2)
    both_parities = at_least_one(
        parent_ready * p * p * (2.0 - p * p), m // 2
    )
    return group_ready * (
        2.0 * anchors_ready * (1.0 - anchors_ready) * one_parity
        + anchors_ready * anchors_ready * both_parities
    )


def poisson_transition(c: float) -> float:
    return -math.expm1(-2.0 * c**3)


def rectangular_phi(z: float, theta: float, s: int = ANCHOR_SIZE) -> float:
    """F_s(z/theta, theta), with its continuous value zero at theta=0."""
    if z <= 0.0 or theta <= 0.0:
        return 0.0
    if theta > 1.0:
        raise ValueError("The column sampling fraction must be at most one.")
    C = z / theta
    row_group_ready = -math.expm1(-C)
    parity_witness = -math.expm1(-0.5 * z * theta * (2.0 - theta))
    parity_success = row_group_ready**s * parity_witness
    return row_group_ready * parity_success * (2.0 - parity_success)


def numerical_maximum(z: float, s: int = ANCHOR_SIZE) -> tuple[float, float]:
    """Grid-bracket and refine every observed local maximum, then compare."""
    grid = np.linspace(0.0, 1.0, 2001)
    values = np.array([rectangular_phi(z, float(x), s) for x in grid])
    candidates = [(float(values[-1]), 1.0)]
    for j in range(1, len(grid) - 1):
        if values[j] >= values[j - 1] and values[j] >= values[j + 1]:
            result = minimize_scalar(
                lambda theta: -rectangular_phi(z, float(theta), s),
                bounds=(float(grid[j - 1]), float(grid[j + 1])),
                method="bounded",
                options={"xatol": 1e-13},
            )
            if not result.success:
                raise RuntimeError("Numerical maximization did not converge.")
            candidates.append((-float(result.fun), float(result.x)))
    return max(candidates)


def quantile_constants(rho: float, s: int = ANCHOR_SIZE) -> dict[str, float]:
    upper = 1.0
    while numerical_maximum(upper, s)[0] < rho:
        upper *= 2.0
    z = brentq(
        lambda value: numerical_maximum(float(value), s)[0] - rho,
        1e-10,
        upper,
        xtol=1e-12,
        rtol=1e-13,
    )
    probability, theta = numerical_maximum(z, s)
    upper_all_columns = max(1.0, z)
    while rectangular_phi(upper_all_columns, 1.0, s) < rho:
        upper_all_columns *= 2.0
    all_columns = brentq(
        lambda value: rectangular_phi(float(value), 1.0, s) - rho,
        1e-10,
        upper_all_columns,
        xtol=1e-12,
        rtol=1e-13,
    )
    return {
        "target_rejection": rho,
        "optimal_normalized_budget_z": z,
        "column_fraction_theta": theta,
        "row_coefficient_C": z / theta,
        "achieved_probability": probability,
        "all_columns_normalized_budget": all_columns,
        "relative_budget_reduction": 1.0 - z / all_columns,
    }


def style_axes(ax: plt.Axes) -> None:
    for side in ("top", "right"):
        ax.spines[side].set_visible(False)
    for side in ("bottom", "left"):
        ax.spines[side].set_color("#9CA7B3")
        ax.spines[side].set_linewidth(0.7)
    ax.tick_params(colors=INK, width=0.7, length=3.0)
    ax.grid(True, color=GRID, linewidth=0.6, zorder=0)
    ax.set_axisbelow(True)


def save_figure(fig: plt.Figure, directory: Path, stem: str) -> None:
    fig.savefig(directory / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(directory / f"{stem}.png", dpi=240, bbox_inches="tight")
    plt.close(fig)


def balanced_figure(directory: Path) -> dict[str, object]:
    c_grid = np.linspace(0.0, 1.5, 751)
    residual_grid = np.linspace(0.1, 1.5, 701)
    fig, axes = plt.subplots(1, 2, figsize=(7.15, 3.05), layout="constrained")
    ax, residual_ax = axes
    receipt = []
    for depth, color in zip(DEPTHS, COLORS):
        cube_root_m = 2.0 ** (depth / 3.0)
        probabilities = np.array(
            [bernoulli_detection(depth, float(c) / cube_root_m) for c in c_grid]
        )
        differences = np.array(
            [
                poisson_transition(float(c))
                - bernoulli_detection(depth, float(c) / cube_root_m)
                for c in residual_grid
            ]
        )
        if not np.all(differences > 0.0):
            raise RuntimeError("The plotted finite-depth deficit is not positive.")
        ax.plot(c_grid, probabilities, color=color, linewidth=1.6,
                label=rf"$h={depth}$")
        residual_ax.plot(residual_grid, differences, color=color, linewidth=1.6)
        receipt.append({
            "depth_h": depth,
            "leaves_m": 1 << depth,
            "probability_at_c_1": bernoulli_detection(depth, 1.0 / cube_root_m),
            "maximum_deficit_on_plotted_grid": float(np.max(differences)),
            "minimum_deficit_on_plotted_grid": float(np.min(differences)),
        })
    ax.plot(c_grid, [poisson_transition(float(c)) for c in c_grid],
            color=INK, linestyle=(0, (4.0, 2.0)), linewidth=1.3,
            label=r"$1-e^{-2c^3}$", zorder=4)
    ax.set_title("(a) Exact Bernoulli detection", loc="left", pad=9)
    ax.set_xlabel(r"Scaled retention $c=p\,m^{1/3}$")
    ax.set_ylabel("Detection probability")
    ax.set_xlim(0.0, 1.5)
    ax.set_ylim(0.0, 1.015)
    ax.set_yticks(np.linspace(0, 1, 6))
    ax.legend(loc="upper left", frameon=False, handlelength=2.6,
              borderaxespad=0.3, labelspacing=0.4)
    residual_ax.set_title("(b) Difference from the limit", loc="left", pad=9)
    residual_ax.set_xlabel(r"Scaled retention $c=p\,m^{1/3}$")
    residual_ax.set_ylabel("Limit minus exact probability")
    residual_ax.set_yscale("log")
    residual_ax.set_xlim(0.1, 1.5)
    residual_ax.set_ylim(8e-10, 2e-2)
    for item in axes:
        style_axes(item)
    save_figure(fig, directory, "balanced_sampling")
    return {
        "anchor_size_s": ANCHOR_SIZE,
        "sampling_model": "Independent Bernoulli retention on each axis",
        "horizontal_coordinate": "c=p*m^(1/3), with m=2^h",
        "limiting_probability_at_c_1": poisson_transition(1.0),
        "depth_receipts": receipt,
    }


def rectangular_figure(directory: Path, records: list[dict[str, float]]) -> None:
    fig, axes = plt.subplots(
        1, 2, figsize=(7.15, 3.22), width_ratios=(1.25, 1.0),
        layout="constrained"
    )
    ax, bars = axes
    theta_grid = np.linspace(0.0, 1.0, 801)
    labels = (r"$\rho=1/2$", r"$\rho=2/3$", r"$\rho=0.9$")
    for record, color, label in zip(records, COLORS, labels):
        z = record["optimal_normalized_budget_z"]
        theta = record["column_fraction_theta"]
        rho = record["target_rejection"]
        ax.plot(theta_grid,
                [rectangular_phi(z, float(x)) for x in theta_grid],
                color=color, linewidth=1.65, label=label)
        ax.scatter([theta], [rho], s=24, color=color, edgecolor="white",
                   linewidth=0.7, zorder=5)
        ax.plot([theta, theta], [0, rho], color=color,
                linewidth=0.75, linestyle=(0, (2, 3)), alpha=0.55)
        ax.annotate(rf"$\theta\approx{theta:.3f}$", (theta, rho),
                    xytext=(7, 9), textcoords="offset points",
                    color=color, fontsize=8.1)
        ax.scatter([1.0], [rectangular_phi(z, 1.0)], s=19,
                   facecolor="white", edgecolor=color, linewidth=1.0,
                   zorder=5, clip_on=False)
    ax.set_title("(a) Column fraction at fixed budget", loc="left", pad=9)
    ax.set_xlabel(r"Column fraction $\theta=q_C/n$")
    ax.set_ylabel(r"Limiting probability $\Phi_3(z,\theta)$")
    ax.set_xlim(0.0, 1.025)
    ax.set_ylim(0.0, 1.035)
    ax.legend(loc="upper left", frameon=False, handlelength=2.3,
              borderaxespad=0.1)
    ax.set_yticks(np.linspace(0, 1, 6))
    positions = np.array([2.0, 1.0, 0.0])
    for y, record, color in zip(positions, records, COLORS):
        z = record["optimal_normalized_budget_z"]
        all_columns = record["all_columns_normalized_budget"]
        bars.barh(y + 0.16, z, height=0.26, color=color,
                  edgecolor=color, linewidth=0.8, zorder=3)
        bars.barh(y - 0.16, all_columns, height=0.26, facecolor="white",
                  edgecolor=color, linewidth=1.0, zorder=3)
        bars.text(z + 0.055, y + 0.16, f"{z:.3f}", va="center",
                  ha="left", fontsize=8.0, color=INK)
        bars.text(all_columns + 0.055, y - 0.16, f"{all_columns:.3f}",
                  va="center", ha="left", fontsize=8.0, color=INK)
    bars.set_title("(b) Budget for the same target", loc="left", pad=9)
    bars.set_xlabel(r"Normalized budget $q_Rq_C/(d_h^2m)$")
    bars.set_yticks(positions, labels)
    bars.set_xlim(0.0, 3.88)
    bars.set_ylim(-0.95, 2.7)
    bars.set_xticks((0, 1, 2, 3))
    bars.legend(handles=[
        Patch(facecolor=INK, edgecolor=INK, label="Optimized rectangle"),
        Patch(facecolor="white", edgecolor=INK, label="All columns")
    ], loc="lower center", bbox_to_anchor=(0.5, -0.015),
        frameon=False, fontsize=7.8, handlelength=1.5, labelspacing=0.25)
    for item in axes:
        style_axes(item)
    bars.grid(axis="y", visible=False)
    save_figure(fig, directory, "rectangular_sampling")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "figures")
    args = parser.parse_args()
    directory = args.output_dir.resolve()
    directory.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["DejaVu Serif"],
        "mathtext.fontset": "dejavuserif",
        "font.size": 9.2,
        "axes.titlesize": 9.4,
        "axes.labelsize": 9.0,
        "xtick.labelsize": 8.2,
        "ytick.labelsize": 8.2,
        "legend.fontsize": 8.0,
        "text.color": INK,
        "axes.labelcolor": INK,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
    })
    balanced_receipt = balanced_figure(directory)
    records = [quantile_constants(rho) for rho in (0.5, 2.0 / 3.0, 0.9)]
    rectangular_figure(directory, records)
    receipt = {
        "anchor_size_s": ANCHOR_SIZE,
        "matrix_pattern_size": 5,
        "host_size_factor": "d_h=20h+2",
        "balanced": balanced_receipt,
        "rectangular": {
            "model": "Uniform independent row and column subsets",
            "asymptotic_regime": "q_R/d_h -> C; q_C/n -> theta",
            "numerical_method": (
                "2001-point grid; bounded refinement of every observed local "
                "maximum; scalar bracketing for target probability"
            ),
            "qualification": (
                "Floating-point illustrations of the proved variational formula; "
                "not interval-certified constants; no optimizer uniqueness claim."
            ),
            "quantiles": records,
        },
    }
    receipt_path = directory / "sampling_figure_data.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output_directory": str(directory), "quantiles": records},
                     indent=2))


if __name__ == "__main__":
    main()
