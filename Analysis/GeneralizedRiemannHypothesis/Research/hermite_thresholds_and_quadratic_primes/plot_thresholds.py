"""Draw the exponent in the fixed-threshold cube theorem (Matplotlib 3.x)."""
from math import sqrt
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ink = "#19364a"
teal = "#12665e"
roots = [0, 1, sqrt(3), sqrt(3 + sqrt(6))]
limits = [-0.5, *roots, 2.67]
fig, ax = plt.subplots(figsize=(6.4, 1.73))
for j, (left, right) in enumerate(zip(limits, limits[1:])):
    level = j + 0.5
    ax.hlines(level, left, right, linewidth=2.1, color=ink)
    interior_ends = [x for x in (left, right) if x in roots]
    ax.scatter(interior_ends, [level] * len(interior_ends), zorder=3,
               facecolors="white", edgecolors=ink, s=20, linewidths=1.25)
for j, root in enumerate(roots, start=1):
    ax.vlines(root, j - 0.5, j + 0.5, colors="#9caeb1", linestyles=":", linewidth=0.8)
    ax.scatter(root, j, s=22, color=teal, zorder=4)
ax.set_xlim(limits[0], limits[-1])
ax.set_ylim(0.15, 4.85)
ax.set_xticks(roots, ["0", "1", r"$\sqrt{3}$", r"$\sqrt{3+\sqrt{6}}$"])
ax.set_yticks([0.5, 1.5, 2.5, 3.5, 4.5])
ax.tick_params(axis="both", labelsize=8, colors=ink, length=2.5)
ax.set_ylabel(r"Exponent $\alpha$", fontsize=9, color=ink)
ax.set_xlabel(r"Threshold $a$", fontsize=9, color=ink)
ax.spines[["top", "right"]].set_visible(False)
for spine in ax.spines.values():
    spine.set_color("#b6c0c2")
fig.subplots_adjust(left=0.095, right=0.97, bottom=0.29, top=0.94)
fig.savefig(Path(__file__).with_name("thresholds.pdf"), metadata={"Title": "Parity-bias exponents at Hermite thresholds"})
