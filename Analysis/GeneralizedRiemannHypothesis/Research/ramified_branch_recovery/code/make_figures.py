#!/usr/bin/env python3
"""Regenerate the vector figures. Requires matplotlib; verification does not."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42})
blue = "#176D9C"
orange = "#C66B32"
grey = "#D4DBE1"

with (ROOT / "results/phase_diagram.csv").open() as f:
    rows = list(csv.DictReader(f))
x = [int(r["precision"]) for r in rows]
y = [int(r["relative_distance"]) for r in rows]
fig, ax = plt.subplots(figsize=(7.0, 3.4), layout="constrained")
ax.step(x, y, where="post", color=blue, linewidth=2.5)
ax.scatter([10, 11, 15, 18, 19, 21], [4, 6, 7, 8, 10, 11], color=blue, s=28, zorder=3)
ax.axhline(7, color=orange, linestyle="--", linewidth=1.1)
ax.annotate("Three errors become correctable", xy=(15, 7), xytext=(10.1, 9.2),
            arrowprops={"arrowstyle": "->", "color": orange}, color=orange, fontsize=9)
ax.annotate("Maximum distance 11", xy=(21, 11), xytext=(19.2, 11.6), fontsize=9)
ax.set(xlim=(0, 27), ylim=(-.4, 12.3), xlabel="Coefficients retained per branch, n",
       ylabel="Exact relative block distance")
ax.set_xticks([0, 5, 10, 15, 20, 25])
ax.set_yticks(range(0, 12, 2))
ax.grid(axis="y", alpha=.18)
fig.savefig(OUT / "precision_distance.pdf")
fig.savefig(OUT / "precision_distance.png", dpi=180)
plt.close(fig)

packed = {0, 2, 4, 6, 8, 10, 12, 14, 1, 9}
worst = {0, 1, 2, 4, 5, 8, 9, 10, 12, 13}
leaf_order = sorted(range(16), key=lambda a: tuple((a >> k) & 1 for k in range(4)))
positions = {a: i for i, a in enumerate(leaf_order)}
fig, axes = plt.subplots(2, 1, figsize=(7.0, 4.8), layout="constrained")
for ax, retained, title in zip(axes, (packed, worst),
        ("Packed survivors: cutoff 13", "Worse survivors for this jet: cutoff 15")):
    def draw(group, depth):
        xpos = sum(positions[a] for a in group) / len(group)
        ypos = 4 - depth
        if depth < 4:
            for digit in (0, 1):
                child = [a for a in group if ((a >> depth) & 1) == digit]
                cx, cy = draw(child, depth + 1)
                active = any(a in retained for a in child)
                ax.plot([xpos, cx], [ypos, cy], color=blue if active else grey,
                        linewidth=1.2, zorder=1)
        else:
            active = group[0] in retained
            ax.scatter([xpos], [ypos], s=40, facecolors=blue if active else "white",
                       edgecolors=blue if active else grey, linewidths=1.2, zorder=2)
            ax.text(xpos, -.42, str(group[0]), ha="center", va="top", fontsize=9)
        return xpos, ypos
    draw(list(range(16)), 0)
    ax.set_title(title, loc="left", fontsize=11, fontweight="bold", pad=3)
    ax.text(-.65, 3.9, "1", fontsize=8, color="#687582")
    ax.text(-.65, 2.9, "2", fontsize=8, color="#687582")
    ax.text(-.65, 1.9, "4", fontsize=8, color="#687582")
    ax.text(-.65, .9, "8", fontsize=8, color="#687582")
    ax.set(xlim=(-1.1, 15.5), ylim=(-.9, 4.5))
    ax.axis("off")
fig.savefig(OUT / "survivor_trees.pdf")
fig.savefig(OUT / "survivor_trees.png", dpi=180)
plt.close(fig)
print("Wrote precision_distance and survivor_trees in PDF and PNG formats.")
