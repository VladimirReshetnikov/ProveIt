#!/usr/bin/env python3
"""Generate the publication figure from the proved bound formulas."""
from pathlib import Path
from math import comb
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.labelcolor": "#18344D", "text.color": "#18344D",
                     "axes.titleweight": "bold", "pdf.fonttype": 42})
fig, axes = plt.subplots(1, 2, figsize=(8.2, 3.6), constrained_layout=True)
delta, degree, m = 0.5, 3, 8
eta = np.geomspace(1e-4, 0.1, 350)
old = ((delta + eta) ** m - delta ** m) / delta ** m
centered = sum(comb(m, j) * delta ** (m - j) * eta ** j
               for j in range(4, m + 1)) / delta ** m
refined = (12 * delta ** 4 * eta ** 4 +
           sum(comb(m, j) * delta ** (m - j) * eta ** j
               for j in range(5, m + 1))) / delta ** m
ax = axes[0]
ax.loglog(eta, old, color="#AD6830", lw=2, label="Triangle inequality")
ax.loglog(eta, centered, color="#7C8B98", lw=1.8, ls="--", label="Cancel degrees 1–3")
ax.loglog(eta, refined, color="#007E80", lw=2.2, label="Exact quartic types; odd order")
ax.set(title=r"Cube-count error: $d=3$, $\delta=1/2$",
       xlabel=r"Centered norm $\eta=\|f\|_{U^3}$",
       ylabel=r"Upper bound for $(Q_3-\delta^8)/\delta^8$")
ax.legend(loc="upper left", frameon=False, fontsize=8.5)
ax.grid(which="major", alpha=0.16)

x = np.geomspace(0.01, 1, 350)
ax = axes[1]
ax.loglog(x, x ** 5 / np.sqrt(2), color="#AD6830", lw=2,
          label=r"Gowers: $\delta^5/\sqrt{2}$")
ax.loglog(x, 7 * x ** 3 / (3 * np.sqrt(6)), color="#007E80", lw=2.2,
          label=r"Cubic certificate: $7\delta^3/(3\sqrt{6})$")
ax.set(title="Common-neighborhood core size", xlabel=r"Density parameter $\delta$",
       ylabel=r"Guaranteed fraction $|K|/n$")
ax.legend(loc="lower right", frameon=False, fontsize=8.5)
ax.grid(which="major", alpha=0.16)
out = Path(__file__).resolve().parent / "figures"
out.mkdir(exist_ok=True)
fig.savefig(out / "local_bound_comparisons.pdf")
fig.savefig(out / "local_bound_comparisons.png", dpi=180)
print("Created figures/local_bound_comparisons.pdf and .png")
print("Curves are evaluations of proved bounds, not observed extremizers.")
