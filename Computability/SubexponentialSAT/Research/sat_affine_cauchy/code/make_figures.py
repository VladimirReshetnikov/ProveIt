#!/usr/bin/env python3
"""Draw the exact four parallel classes used in the nine-group certificate."""
from pathlib import Path
import os
import tempfile

os.environ.setdefault("MPLCONFIGDIR", str(Path(tempfile.gettempdir()) / "sat-mpl-cache"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
colors = ["#165D91", "#D66B22", "#33836C"]
directions = [(1, 0), (0, 1), (1, 1), (1, 2)]
titles = [r"$x$", r"$y$", r"$x+y$", r"$x+2y$"]
fig, axes = plt.subplots(1, 4, figsize=(10.4, 3.1), constrained_layout=True)
for ax, (a, b), title in zip(axes, directions, titles):
    for j in range(9):
        x, y = j % 3, j // 3
        fiber = (a*x + b*y) % 3
        ax.scatter([x], [y], s=590, color=colors[fiber], zorder=3,
                   edgecolors="white", linewidths=1.5)
        ax.text(x, y, str(j), ha="center", va="center", color="white",
                fontsize=13, fontweight="bold", zorder=4)
    ax.set(xlim=(-.5, 2.5), ylim=(-.5, 2.5), xticks=[0, 1, 2], yticks=[0, 1, 2])
    ax.set_aspect("equal")
    ax.set_xlabel(r"$x$", fontsize=11)
    ax.set_ylabel(r"$y$", fontsize=11)
    ax.set_title(title + "  (mod 3)", fontsize=13, pad=12)
    ax.grid(color="#D4DAE1", linewidth=.7)
    ax.tick_params(length=0, labelsize=9)
    for spine in ax.spines.values():
        spine.set_visible(False)
handles = [plt.Line2D([], [], marker="o", linestyle="", color=c,
                     label=f"Fiber {i}", markersize=8) for i, c in enumerate(colors)]
fig.legend(handles=handles, loc="outside lower center", ncols=3, frameon=False)
out = ROOT / "figures" / "affine_classes.png"
out.parent.mkdir(parents=True, exist_ok=True)
fig.savefig(out, dpi=220, facecolor="white")
print(out)
