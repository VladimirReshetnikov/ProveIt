#!/usr/bin/env python3
"""Regenerate the article's scientific figure from recorded exact-model data."""
from decimal import Decimal
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
data = json.loads((ROOT / "verification_results.json").read_text())["asymptotic_values"][1:]
x = np.array([float(v["u"]) for v in data])
y = np.array([float(v["normalized_secondary_correction"]) for v in data])
limit = float(data[0]["limiting_constant"])
gap = np.array([float(Decimal(v["normalized_secondary_correction"])
                      - Decimal(v["limiting_constant"])) for v in data])

plt.rcParams.update({
    "font.family": "DejaVu Serif", "font.size": 9,
    "axes.titlesize": 10.5, "axes.labelsize": 9.5,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.edgecolor": "#94a3b8", "axes.labelcolor": "#17233a",
    "text.color": "#17233a", "xtick.color": "#334155",
    "ytick.color": "#334155", "grid.color": "#e2e8f0",
    "pdf.fonttype": 42, "ps.fonttype": 42,
})
fig, axes = plt.subplots(1, 2, figsize=(7.35, 3.0), constrained_layout=True)
navy, teal = "#173b6c", "#087f8c"
axes[0].semilogx(x, y, marker="o", color=navy, markersize=4,
                linewidth=1.7, label="Exact model")
axes[0].axhline(limit, color=teal, linestyle="--", linewidth=1.25,
               label=r"$C_*=(9/4)^{1/3}$")
axes[0].set_title("Normalized secondary coefficient", loc="left", pad=11)
axes[0].set_ylabel(r"$\mathcal{R}_{1/4}(u)$")
axes[0].set_ylim(limit-.004, y[0]+.004)
axes[0].ticklabel_format(axis="y", style="plain", useOffset=False)
axes[0].legend(frameon=False, fontsize=8, loc="upper right")

ref = gap[-1]*(x/x[-1])**(4/3)
axes[1].loglog(x, ref, color="#a0abb8", linestyle="--", linewidth=2,
               label=r"$u^{4/3}$ reference")
axes[1].loglog(x, gap, color=teal, marker="o", markersize=4, linewidth=1.4,
               label="Exact residual")
axes[1].set_title("Decay of the remaining model error", loc="left", pad=11)
axes[1].set_ylabel(r"$\mathcal{R}_{1/4}(u)-C_*$")
axes[1].legend(frameon=False, fontsize=8, loc="upper right")
for ax in axes:
    ax.set_xlim(1e-2, 1e-9)
    ax.set_xticks([1e-2, 1e-4, 1e-6, 1e-8])
    ax.set_xlabel(r"Centered norm $u$ (decreasing to the right)")
    ax.grid(axis="y", alpha=.85, linewidth=.6)
fig.savefig(OUT / "cube_convergence.pdf", bbox_inches="tight")
fig.savefig(OUT / "cube_convergence.png", dpi=200, bbox_inches="tight")
plt.close(fig)
print("Created figures/cube_convergence.pdf and .png")
