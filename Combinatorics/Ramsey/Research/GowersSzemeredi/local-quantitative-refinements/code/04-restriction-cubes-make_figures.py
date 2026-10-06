#!/usr/bin/env python3
"""Reproduce the article figure; requires numpy and matplotlib."""
from pathlib import Path
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path(__file__).resolve().parent / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Serif", "font.size": 10,
    "mathtext.fontset": "dejavuserif", "axes.spines.top": False,
    "axes.spines.right": False, "axes.labelsize": 11,
    "legend.fontsize": 8.5, "pdf.fonttype": 42,
})
delta = 0.25
u = np.logspace(-5, -1, 250)
old = sum(math.comb(8, r) * delta ** (8-r) * u ** r for r in range(1, 9))
sharp = (6 * np.sqrt(2) * delta ** 4 * u ** 4
         + 2 ** (17/8) * delta ** 3 * u ** 5
         + 28 * delta ** 2 * u ** 6 + 8 * delta * u ** 7 + u ** 8)
fractional = (6 * np.sqrt(2) * delta ** 4 * u ** 4
              + 6 * delta ** (8/3) * u ** (16/3)
              + 28 * delta ** 2 * u ** 6 + 8 * delta * u ** 7 + u ** 8)
fig, axes = plt.subplots(1, 2, figsize=(11.3, 4.1))
ax = axes[0]
ax.loglog(u, old, color="#8c5a39", lw=2, label="Source: Minkowski bound")
ax.loglog(u, sharp, color="#16697a", lw=2, label="Sharp real leading term")
ax.loglog(u, fractional, color="#233b6e", lw=1.8, ls="--",
          label="Order coprime to 6")
ax.set(xlabel=r"$u=\|f\|_{U^3}$",
       ylabel=r"Upper bound for $Q_3(\delta+f)-\delta^8$",
       title=r"(a) Cube bounds at $\delta=1/4$")
ax.grid(True, which="major", alpha=.18)
ax.legend(loc="upper left", frameon=False)

x = np.logspace(-5, -1.7, 200)
c = (np.sqrt(2) / 6) ** (1/3)
b = c * delta ** (-1/3) * x ** (4/3)
a4 = -3 * b ** 4 + np.sqrt(32 * x ** 8 + 8 * b ** 8)
excess = (1.5 * delta ** 4 * (a4 + b ** 4)
          + .5 * delta ** 3 * a4 * b
          + 1.5 * delta ** 2 * a4 * b ** 2 + x ** 8)
scaled = ((excess - 6 * np.sqrt(2) * delta ** 4 * x ** 4)
          / (delta ** (8/3) * x ** (16/3)))
ax = axes[1]
ax.semilogx(x, scaled, color="#16697a", lw=2.2,
            label="Exact two-frequency family")
ax.axhline((9/4) ** (1/3), color="#233b6e", lw=1.6, ls="--",
           label=r"Limit $(9/4)^{1/3}$")
ax.set(xlabel=r"$u$",
       ylabel=r"Correction divided by $\delta^{8/3}u^{16/3}$",
       title="(b) The fractional correction is necessary")
ax.grid(True, alpha=.18)
ax.legend(loc="upper left", frameon=False)
fig.tight_layout(pad=1.3, w_pad=2.0)
fig.savefig(OUT / "cube_refinements.pdf", bbox_inches="tight")
fig.savefig(OUT / "cube_refinements.png", dpi=180, bbox_inches="tight")
print("Created figures/cube_refinements.pdf and .png")
