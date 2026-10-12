#!/usr/bin/env python3
"""Render the recorded coefficient errors and the proved transition profile."""
from pathlib import Path
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
FIGURES = ROOT / "figures"
FIGURES.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Serif",
    "font.size": 10,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.labelsize": 10,
    "legend.frameon": False,
    "pdf.fonttype": 42,
    "savefig.bbox": "tight",
})
colors = ["#1e3d59", "#347c87", "#bf8230", "#983d4e"]
record = json.loads((DATA / "coefficient_validation.json").read_text())
summary = record["max_absolute_relative_error_by_n_and_order"]
ns = sorted(int(n) for n in summary)
fig, ax = plt.subplots(figsize=(6.6, 3.65))
for order, color in enumerate(colors):
    values = [100 * float(summary[str(n)][order]) for n in ns]
    ax.plot(ns, values, marker="o", color=color, linewidth=1.6,
            label="Gaussian term" if order == 0 else f"Through order {order}")
ax.set_xscale("log", base=2)
ax.set_yscale("log")
ax.set_xticks(ns, [str(n) for n in ns])
ax.set_yticks([1, 2, 5, 10, 20, 50, 100], ["1", "2", "5", "10", "20", "50", "100"])
ax.set_xlabel("Coefficient index n")
ax.set_ylabel("Maximum absolute relative error (%)")
ax.grid(alpha=.18, which="both")
ax.legend(ncol=2, loc="lower center", bbox_to_anchor=(0.5, 1.01), fontsize=9)
fig.tight_layout()
fig.savefig(FIGURES / "coefficient_refinement.pdf")
fig.savefig(FIGURES / "coefficient_refinement.png", dpi=160)
plt.close(fig)

mp.mp.dps = 40
tau = np.linspace(-3, 3, 241)
fig, ax = plt.subplots(figsize=(6.6, 3.65))
transition_rows = []
for q_string, color in zip(["0.001", "0.000001", "0.000000000001"], colors):
    q = mp.mpf(q_string)
    center2 = -3 * mp.lambertw(-(2*mp.pi)**(mp.mpf(1)/3)*q**(mp.mpf(2)/3)/3, -1)
    values = np.exp(-tau) + (1+2*tau/float(center2))**(-1.5)
    exponent = round(-float(mp.log10(q)))
    ax.plot(tau, values, color=color, lw=1.5, label=rf"$q=10^{{-{exponent}}}$")
    transition_rows.append({"q": q_string, "center_squared": mp.nstr(center2, 35)})
ax.plot(tau, 1+np.exp(-tau), "--", color="#111111", lw=1.4,
        label=r"Limit $1+e^{-\tau}$")
ax.set_yscale("log")
ax.set_xlabel(r"Transition coordinate $\tau=(\xi^2-x_*^2)/2$")
ax.set_ylabel("Normalized Gaussian plus power term")
ax.grid(alpha=.18, which="both")
ax.legend(loc="upper right", fontsize=9)
fig.tight_layout()
fig.savefig(FIGURES / "lambert_transition.pdf")
fig.savefig(FIGURES / "lambert_transition.png", dpi=160)
plt.close(fig)
(DATA / "figure_metadata.json").write_text(json.dumps({
    "matplotlib_version": matplotlib.__version__,
    "coefficient_figure": "Recorded finite recurrence diagnostics, not fitted errors.",
    "transition_figure": "Exact normalized two-term expressions, not sampled probabilities.",
    "transition_centers": transition_rows,
}, indent=2)+"\n")
print("Rendered coefficient_refinement.pdf and lambert_transition.pdf")
