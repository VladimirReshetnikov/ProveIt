#!/usr/bin/env python3
"""Rebuild the article's scientific figures from formulas and recorded data.

No root finding or asymptotic fitting is used here.  PDF figures are vector
graphics; matching PNGs are provided for convenient previews.
"""
import argparse
import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--data-dir", type=Path, default=ROOT / "data")
parser.add_argument("--output-dir", type=Path, default=ROOT / "figures")
args = parser.parse_args()
args.output_dir.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "DejaVu Serif", "font.size": 9.0,
    "mathtext.fontset": "dejavuserif", "axes.spines.top": False,
    "axes.spines.right": False, "axes.labelsize": 9.2,
    "axes.titlesize": 9.0, "legend.fontsize": 8.3,
    "axes.linewidth": 0.7, "lines.linewidth": 1.6,
    "xtick.labelsize": 8.3, "ytick.labelsize": 8.3,
    "savefig.dpi": 220, "pdf.fonttype": 42,
})
NAVY, TEAL, ORANGE = "#183653", "#247D86", "#BE6931"


def records(name):
    with (args.data_dir / name).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def save(fig, stem):
    for extension in ("pdf", "png"):
        fig.savefig(args.output_dir / f"{stem}.{extension}", bbox_inches="tight")
    plt.close(fig)


# Exact leading joint profile.  expm1 prevents cancellation near lambda=0.
lam = np.linspace(-4, 4, 401)
phi = np.ones_like(lam)
nonzero = lam != 0
phi[nonzero] = -np.expm1(-lam[nonzero]) / lam[nonzero]
A0 = np.pi ** 2 / 6
profiles = {}
fig, ax = plt.subplots(figsize=(5.45, 3.15), layout="constrained")
for eta, color in [(-1, NAVY), (0, TEAL), (1, ORANGE)]:
    val = 2 * A0 / (np.sqrt(eta * eta + 2 * A0 * phi) + eta)
    profiles[eta] = val
    ax.plot(lam, val, color=color, label=rf"$\eta={eta}$")
ax.set(xlabel=r"Scaled order displacement $\lambda$",
       ylabel=r"Inverse amplitude $V_0(\lambda,\eta)$", xlim=(-4, 4))
ax.grid(axis="y", alpha=0.18)
ax.legend(loc="upper left", frameon=False)
save(fig, "joint_profile")
with (args.data_dir / "joint_profile.csv").open("w", newline="", encoding="utf-8") as f:
    writer = csv.writer(f)
    writer.writerow(["lambda", "eta_minus_1", "eta_0", "eta_plus_1"])
    writer.writerows(zip(lam, profiles[-1], profiles[0], profiles[1]))

# Finite marginal coefficients, compared with three analytically proved laws.
rows = [r for r in records("coefficient_phases.csv") if r["case"] == "critical_s_3"]
rows.sort(key=lambda r: int(r["n"]))
fig, ax = plt.subplots(figsize=(5.45, 3.05), layout="constrained")
for key, label, color, marker in [
    ("ratio_to_leading", "Leading equivalent", NAVY, "o"),
    ("ratio_to_log_refinement", "Through first log correction", ORANGE, "s"),
    ("ratio_to_second_log_refinement", "Through second log correction", TEAL, "D"),
]:
    ax.plot([int(r["n"]) for r in rows], [float(r[key]) for r in rows],
            marker=marker, markersize=4.5, label=label, color=color)
ax.axhline(1, color="#555555", lw=0.8, linestyle="--", zorder=0)
ax.set(xscale="log", xlabel=r"Coefficient index $n$",
       ylabel="Computed coefficient / approximation")
ax.set_xticks([128, 512, 2048], ["128", "512", "2048"])
ax.minorticks_off()
ax.grid(axis="y", alpha=0.18)
ax.legend(loc="best", frameon=False)
save(fig, "marginal_refinement")

# Actual coefficient ordinates in the exact probability normalization.
density = records("density_profiles.csv")
grid = np.array([float(r["xi"]) for r in density])
sample = records("coefficient_crossover.csv")
fig, axes = plt.subplots(1, 3, figsize=(6.3, 2.62), sharey=True)
for ax, s, key, title in zip(
    axes, [2.5, 3, 4],
    ["stable_alpha_1_5", "standard_normal", "standard_normal"],
    [r"Fractional: $s=2.5$", r"Marginal: $s=3$", r"Finite curvature: $s=4$"],
):
    ax.plot(grid, [float(r[key]) for r in density], color=NAVY, label="Limit density")
    points = sorted([r for r in sample if float(r["s"]) == s and int(r["n"]) == 2048],
                    key=lambda r: float(r["xi"]))
    ax.scatter([float(r["xi"]) for r in points],
               [float(r["normalized_profile_n_Bn_Rb_power_n"]) for r in points],
               color=ORANGE, s=23, edgecolor="white", linewidth=0.4,
               zorder=3, label=r"Finite coefficients, $n=2048$")
    ax.set(title=title, xlabel=r"$\xi$", xlim=(-3, 3), ylim=(0, 0.445))
    ax.set_xticks([-2, 0, 2])
    ax.grid(axis="y", alpha=0.18)
axes[0].set_ylabel(r"$nB_n R_b^n a_n$")
handles, labels = axes[0].get_legend_handles_labels()
fig.legend(handles, labels, loc="lower center", ncol=2, frameon=False,
           bbox_to_anchor=(0.53, -0.02))
fig.tight_layout(rect=(0, 0.08, 1, 1), w_pad=0.8)
save(fig, "coefficient_crossover")
print(f"Rebuilt three figures in {args.output_dir}")
