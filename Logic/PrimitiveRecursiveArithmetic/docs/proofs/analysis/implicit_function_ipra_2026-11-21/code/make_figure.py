#!/usr/bin/env python3
"""Draw the example; floating point is used only for visualization."""
from pathlib import Path
from fractions import Fraction
import math

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

from implicit_solver import CIRCLE, solve, sup

OUT = Path(__file__).resolve().parents[1] / "paper" / "figures"
OUT.mkdir(parents=True, exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 10,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.labelcolor": "#17344a",
    "text.color": "#17344a",
    "axes.titleweight": "bold",
    "pdf.fonttype": 42,
})

fig, (left, right) = plt.subplots(1, 2, figsize=(10.0, 3.65),
                                 constrained_layout=True)
xs = [-0.25 + 0.5 * i / 300 for i in range(301)]
ys = [math.sqrt(1 - x * x) for x in xs]
left.add_patch(Rectangle((-0.25, 0.75), 0.5, 0.5,
                        facecolor="#eff6f8", edgecolor="#94aeb8",
                        linewidth=1.3, linestyle="--"))
left.plot(xs, ys, color="#087f8c", linewidth=2.8, label="Implicit branch")
left.scatter([0], [1], color="#17344a", s=23, zorder=5)
left.annotate("Base zero (0, 1)", (0, 1), (0.01, 1.095),
              arrowprops={"arrowstyle": "-", "color": "#718792"},
              fontsize=9)
left.set(xlim=(-0.3, 0.3), ylim=(0.71, 1.29),
         xlabel="Parameter x", ylabel="Implicit value y",
         title="A certified local graph")
left.set_xticks([-0.25, 0, 0.25])
left.set_yticks([0.75, 1, 1.25])
left.grid(color="#dbe5e9", linewidth=0.6, alpha=0.7)

ks = list(range(0, 49, 2))
residuals = []
for k in ks:
    trace = solve(CIRCLE, (Fraction(1, 4),), k, "plus")
    residuals.append(float(sup(CIRCLE.exact(trace.parameter, trace.result))))
right.plot(ks, [2.0 ** (-k - 2) for k in ks], color="#b56b3b",
           linestyle="--", linewidth=1.8, label="Proved residual bound")
right.plot(ks, residuals, color="#087f8c", marker="o", markersize=3,
           linewidth=1.5, label="Computed residual")
right.set_yscale("log", base=2)
right.set(xlabel="Requested precision k", ylabel="Normalized residual",
          title="A fixed clock with an error guarantee")
right.grid(color="#dbe5e9", linewidth=0.6, alpha=0.7)
right.legend(frameon=False, fontsize=8.5, loc="upper right")
fig.savefig(OUT / "implicit_graph.pdf")
fig.savefig(OUT / "implicit_graph.png", dpi=180)
print(f"Created {OUT / 'implicit_graph.pdf'}")
