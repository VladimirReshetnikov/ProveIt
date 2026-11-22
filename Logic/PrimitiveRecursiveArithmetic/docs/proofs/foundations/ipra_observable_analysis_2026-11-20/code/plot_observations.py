#!/usr/bin/env python3
"""Optional scientific illustration generator (requires Matplotlib)."""
from pathlib import Path
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "axes.spines.top": False, "axes.spines.right": False})
fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.0), constrained_layout=True)
ax = axes[0]
x = [j / 400 for j in range(401)]
ax.fill_between(x, [t*t for t in x], x, color="#d9ebe9", label="Feasible moments")
ax.plot(x, x, color="#287d78", linewidth=1.6)
ax.plot(x, [t*t for t in x], color="#287d78", linewidth=1.2)
ax.add_patch(Rectangle((3/8, 5/8), 1/4, 1/4, fill=False,
                       edgecolor="#be6736", linewidth=1.4, linestyle="--"))
ax.scatter([1/2], [3/4], c="#be6736", s=27, zorder=5)
ax.scatter([5/8], [5/8], c="#152f49", s=27, zorder=5)
ax.annotate("Target (1/2, 3/4)", (1/2, 3/4), xytext=(0.08, 0.98),
            arrowprops={"arrowstyle": "-", "color": "#be6736"}, fontsize=8)
ax.annotate("Attainer (5/8, 5/8)", (5/8, 5/8), xytext=(0.1, 0.2),
            arrowprops={"arrowstyle": "-", "color": "#152f49"}, fontsize=8)
ax.set(xlim=(0,1.02), ylim=(0,1.04), xlabel="First moment", ylabel="Second moment",
       title="A quantified truth value: 1/8")
ax.set_aspect("equal")
ax = axes[1]
precision = list(range(65))
terms = [4 * (k + 3) for k in precision]
sequential = [n - 1 for n in terms]
doubling = [2 * (n - 1).bit_length() for n in terms]
ax.plot(precision, sequential, color="#be6736", label="Sequential geometric sum")
ax.step(precision, doubling, color="#287d78", where="mid", label="Shared doubling graph")
ax.set(xlabel="Requested error exponent k", ylabel="Algebra multiplications",
       title="Certified geometric-sum operation counts", xlim=(0,64), ylim=(0,280))
ax.legend(frameon=False, fontsize=7, loc="upper left")
ax.grid(alpha=0.18)
dest = ROOT / "paper/figures"
dest.mkdir(parents=True, exist_ok=True)
fig.savefig(dest / "observations.pdf")
fig.savefig(dest / "observations.png", dpi=180)
print("Generated moment geometry and geometric-sum operation-count figures.")
