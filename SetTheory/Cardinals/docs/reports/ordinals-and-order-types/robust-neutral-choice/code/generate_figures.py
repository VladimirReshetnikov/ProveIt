#!/usr/bin/env python3
"""Render publication figures from the proved exact binomial formula.

Requires matplotlib and numpy; no random sampling is used.
Run from any directory: python3 code/generate_figures.py
"""
from fractions import Fraction
from math import comb, erfc, sqrt
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)


def profile(n: int):
    """All exact optimal robust fractions at integer budgets."""
    d = n if n % 2 else n - 1
    m = (d - 1) // 2
    cumulative = []
    total = 0
    for j in range(m + 1):
        total += comb(d, j)
        cumulative.append(total)
    return [Fraction(2 * cumulative[m - r], 1 << d)
            for r in range(m + 1)]


plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9,
    "axes.titlesize": 10, "axes.labelsize": 9,
    "axes.spines.top": False, "axes.spines.right": False,
    "pdf.fonttype": 42, "ps.fonttype": 42,
    "legend.frameon": False,
})

fig, axes = plt.subplots(1, 2, figsize=(10.4, 3.65))
colors = ["#17627a", "#ba5b34", "#5b6d31"]
for n, color in zip([25, 101, 1001], colors):
    p = profile(n)
    r = np.arange(len(p))
    mask = r / sqrt(n) <= 1.6
    axes[0].plot(r[mask] / sqrt(n), [float(p[i]) for i in r[mask]],
                 color=color, marker="o" if n == 25 else None,
                 markersize=3, linewidth=1.6, label=f"n = {n}")
x = np.linspace(0, 1.6, 250)
axes[0].plot(x, [erfc(sqrt(2) * t) for t in x], color="#333333",
             linestyle="--", linewidth=1.4, label=r"limit $2\Phi(-2c)$")
axes[0].set(xlim=(0, 1.6), ylim=(0, 1.02),
            xlabel=r"Adversarial budget $r/\sqrt{n}$",
            ylabel="Optimal robust fraction",
            title="A. The square-root scale")
axes[0].legend(loc="upper right", fontsize=8)

ns = list(range(1, 1002, 2))
ps = {n: profile(n) for n in ns}
for r, color in zip([1, 3, 10], colors):
    y = [float(ps[n][r]) if r < len(ps[n]) else 0 for n in ns]
    axes[1].plot(ns, y, color=color, linewidth=1.7, label=f"r = {r}")
axes[1].set(xscale="log", xlim=(1, 1001), ylim=(0, 1.02),
            xlabel="Odd committee size n",
            ylabel="Optimal robust fraction",
            title="B. A fixed budget becomes harmless")
axes[1].legend(loc="upper left", fontsize=8)
for ax in axes:
    ax.grid(alpha=0.16, linewidth=0.6)
    ax.set_axisbelow(True)
fig.tight_layout(pad=1.3, w_pad=2.2)
fig.savefig(OUT / "robustness_profile.pdf", bbox_inches="tight")
fig.savefig(OUT / "robustness_profile.png", dpi=220, bbox_inches="tight")
plt.close(fig)
print("Created figures/robustness_profile.pdf and .png from exact fractions.")
