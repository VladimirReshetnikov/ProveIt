#!/usr/bin/env python3
"""Render the exact valuation grid already computed by verify.py."""

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import BoundaryNorm, ListedColormap

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "data/valuation_grid.json").read_text())
matrix = np.array(data["valuation_matrix"])
bound = np.array(data["bound"])[None, :]
colors = ["#f2f4f5", "#d7e8eb", "#a8cfd3", "#72b1ba", "#398e9e",
          "#246878", "#234b63", "#182e46"]
cmap = ListedColormap(colors)
norm = BoundaryNorm(np.arange(-0.5, 8.5), cmap.N)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42, "ps.fonttype": 42})
fig = plt.figure(figsize=(7.0, 4.25), constrained_layout=True)
gs = fig.add_gridspec(2, 2, height_ratios=[0.48, 3.0], width_ratios=[30, 1.0])
ax0 = fig.add_subplot(gs[0, 0])
ax1 = fig.add_subplot(gs[1, 0], sharex=ax0)
cax = fig.add_subplot(gs[:, 1])
ax0.imshow(bound, aspect="auto", cmap=cmap, norm=norm, interpolation="nearest",
           extent=(0.5, 127.5, 0.5, 1.5))
ax0.set_yticks([])
ax0.set_title("Forced divisibility: binary digit sum minus one", loc="left", pad=7,
              fontsize=10, color="#18374f")
ax0.tick_params(axis="x", bottom=False, labelbottom=False)
im = ax1.imshow(matrix, aspect="auto", cmap=cmap, norm=norm, interpolation="nearest",
                origin="lower", extent=(0.5, 127.5, 0.5, 48.5))
ax1.set_title("Actual divisibility from direct composition modulo 128", loc="left",
              pad=7, fontsize=10, color="#18374f")
ax1.set_xlabel("Exponent N")
ax1.set_ylabel("Iteration number m")
ax1.set_xticks([1, 16, 32, 48, 64, 80, 96, 112, 127])
ax1.set_yticks([1, 8, 16, 24, 32, 40, 48])
bar = fig.colorbar(im, cax=cax, ticks=range(8))
bar.ax.set_yticklabels([str(i) for i in range(7)] + ["7+"])
bar.set_label("Exponent of 2 dividing the coefficient", labelpad=9)
out = ROOT / "figures"
out.mkdir(exist_ok=True)
fig.savefig(out / "valuation_grid.pdf", bbox_inches="tight")
fig.savefig(out / "valuation_grid.png", dpi=180, bbox_inches="tight")
print("Created valuation_grid.pdf and valuation_grid.png from exact data.")
