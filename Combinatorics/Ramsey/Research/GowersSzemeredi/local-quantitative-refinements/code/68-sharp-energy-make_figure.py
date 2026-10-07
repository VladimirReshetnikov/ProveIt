#!/usr/bin/env python3
"""Draw the article's two proved limiting profiles.

Requires matplotlib and numpy only for optional figure regeneration.
These plots illustrate proved formulas; they are not numerical certificates.
"""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

BASE = Path(__file__).resolve().parents[1]
OUT = BASE / "figs"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Serif",
    "font.size": 9,
    "axes.titlesize": 10,
    "axes.labelsize": 9,
    "legend.fontsize": 7.5,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.edgecolor": "#525b65",
    "text.color": "#172333",
    "axes.labelcolor": "#172333",
    "xtick.color": "#525b65",
    "ytick.color": "#525b65",
})
fig, axes = plt.subplots(1, 2, figsize=(6.25, 3.0))
blue = "#1f5c8f"
amber = "#b77b25"

ax = axes[0]
ep = np.linspace(0.0, 0.25, 701)
tau = (1.0 - np.sqrt(np.maximum(0.0, 1.0 - 4.0 * ep))) / 2.0
ax.axvspan(0.0, 2/9, facecolor="#edf4fa", zorder=0)
ax.axvspan(2/9, 0.25, facecolor="#fbf1de", zorder=0)
ax.plot(ep, tau, color=blue, lw=1.8, label=r"Bound $\tau(\varepsilon)$")
indices = np.arange(4, 16)
ep_pts = (indices - 2) / (indices - 1)**2
delta_pts = 1 / (indices - 1)
ax.scatter(ep_pts, delta_pts, s=12, color=blue, zorder=4,
           label="Punctured-coset equalities")
ax.scatter([0.25], [0.5], s=20, color=amber, zorder=5)
ax.axvline(2/9, color=amber, lw=0.8, ls="--")
ax.annotate(r"$2/9$", (2/9, 0.03), xytext=(-15, 7),
            textcoords="offset points", fontsize=8, color=amber)
ax.text(0.014, 0.42, "Unique closest coset\nwhen " + r"$\varepsilon<2/9$",
        color=blue, fontsize=8)
ax.set_title("A. Sharp coset envelope", loc="left", pad=9)
ax.set_xlabel(r"Energy defect $\varepsilon$")
ax.set_ylabel(r"Canonical distance $\delta_C$")
ax.set_xlim(0, 0.258)
ax.set_ylim(0, 0.55)
ax.set_xticks([0, .05, .10, .15, .20, .25])
ax.set_yticks([0, .1, .2, .3, .4, .5])
ax.tick_params(labelsize=7.5)
ax.legend(loc="upper left", bbox_to_anchor=(0.0, 0.70),
          frameon=False, handlelength=1.6)

ax = axes[1]
c = np.linspace(.25, 4.0, 500)
ax.plot(c, 1 + 1/(2*c), color=blue, lw=1.8)
cp = np.array([.5, 1.0, 2.0, 4.0])
yp = 1 + 1/(2*cp)
ax.scatter(cp, yp, s=17, color=blue, zorder=4)
for xx, yy, lab in zip(cp[:3], yp[:3], ["2", "1.5", "1.25"]):
    ax.annotate(lab, (xx, yy), xytext=(5, 6),
                textcoords="offset points", fontsize=8, color=blue)
ax.axhline(1, color=amber, lw=0.9, ls="--")
ax.text(1.8, 1.05, r"Baseline limit $1$", color=amber, fontsize=8)
ax.text(1.4, 2.45, r"$1+\frac{1}{2c}$", color=blue, fontsize=14)
ax.set_title("B. Joint arity-order limit", loc="left", pad=9)
ax.set_xlabel(r"$c$, where $a=m^{c+o(1)}$")
ax.set_ylabel(r"$\lim_{m\to\infty}\,\mathcal{I}_{m,a}/m$")
ax.set_xlim(.2, 4.1)
ax.set_ylim(.9, 3.15)
ax.set_xticks([.5, 1, 2, 3, 4])
ax.set_yticks([1, 1.5, 2, 2.5, 3])
ax.tick_params(labelsize=7.5)
fig.subplots_adjust(left=.085, right=.985, bottom=.20, top=.88, wspace=.42)
fig.savefig(OUT / "overview.pdf", bbox_inches="tight",
            metadata={"Title": "Sharp coset and principal-filter profiles",
                      "Author": "ProveIt research contribution"})
fig.savefig(OUT / "overview.png", dpi=220, bbox_inches="tight")
print(OUT / "overview.pdf")
