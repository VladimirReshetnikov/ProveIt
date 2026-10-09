#!/usr/bin/env python3
"""Reproduce the explanatory kernel/bounds figure; requires NumPy/matplotlib."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 10,
    "axes.spines.top": False, "axes.spines.right": False,
})
blue, teal, orange = "#153149", "#137F86", "#BE7534"
fig, axes = plt.subplots(1, 2, figsize=(8.4, 3.7), layout="constrained")
x = np.linspace(0, 1, 2001)
nodes = np.array([0, .3791, .6209, 1])
weights = np.array([.3183, .1817, .1817, .3183])
potential = np.exp(-10*(x[:, None]-nodes[None, :])**2) @ weights
u = 36532567/10**8
axes[0].plot(x, potential, color=teal, lw=2.2, label=r"$U_\nu(x)$")
axes[0].axhline(u, color=orange, ls="--", lw=1.5, label="Certified lower bound")
for node in nodes:
    axes[0].axvline(node, color=blue, alpha=.15, lw=.8)
axes[0].set(xlabel="$x$", ylabel="Gaussian potential",
            title="Four rational support points")
axes[0].set_xlim(-.02, 1.02)
axes[0].legend(frameon=False, fontsize=9, loc="upper center")
axes[0].grid(axis="y", alpha=.15)

rows = json.loads((ROOT/"data/large_n_upper_bounds.json").read_text())
rows = [r for r in rows if r["n"] >= 50]
n = np.array([r["n"] for r in rows])
axes[1].plot(n, np.array([r["palette_upper"] for r in rows])/n,
             "o-", color=blue, label="Palette bound divided by n")
axes[1].plot(n, np.array([r["gaussian_upper"] for r in rows])/n,
             "s-", color=teal, label="Gaussian bound divided by n")
axes[1].axhline(1.848895345708975, color=orange, ls="--", lw=1.5,
               label=r"Certified limiting coefficient")
axes[1].axhline(np.sqrt(5), color=blue, ls=":", alpha=.55, lw=1.3)
axes[1].text(920, np.sqrt(5)+.01, r"$\sqrt{5}$", color=blue, ha="right", fontsize=9)
axes[1].set(xscale="log", xlabel="Cube side length n (log scale)",
            ylabel="Upper bound / n", title="Rigorous finite upper bounds")
axes[1].set_xticks(n, [str(v) for v in n])
axes[1].set_ylim(1.79, 2.29)
axes[1].legend(frameon=True, facecolor="white", edgecolor="#d5dce0",
               framealpha=1, fontsize=7.5, loc="upper left")
axes[1].grid(axis="y", alpha=.15)
for suffix in ("pdf", "png"):
    fig.savefig(ROOT/f"figures/kernel_bounds.{suffix}", dpi=180)
