#!/usr/bin/env python3
"""Render the article's analytic comparison figures. Requires numpy, matplotlib."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
DEST = ROOT / "figures"
DEST.mkdir(exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Serif", "font.size": 11,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.labelcolor": "#19314d", "text.color": "#19314d",
    "xtick.color": "#19314d", "ytick.color": "#19314d",
    "pdf.fonttype": 42, "figure.constrained_layout.use": True})
TEAL, NAVY, ORANGE = "#006f77", "#19314d", "#bb602d"


def save(fig, name):
    fig.savefig(DEST / (name + ".pdf"), bbox_inches="tight")
    fig.savefig(DEST / (name + ".png"), dpi=170, bbox_inches="tight")
    plt.close(fig)


a = np.linspace(0, 1 / 3, 400)
frontier = (1 - 3 * a) / 2
fig, ax = plt.subplots(figsize=(7.2, 4.9))
ax.fill_between(a, 0, frontier, color=TEAL, alpha=.09)
ax.plot(a, frontier, color=TEAL, lw=2.5, label=r"Optimal flexible frontier: $3a+2b=1$")
ac = np.linspace(0, .25, 300)
ax.plot(ac, (1 - 4 * ac) / 2, color=ORANGE, lw=2,
        label=r"Sufficient prescribed-length boundary: $4a+2b=1$")
ax.plot(a, 2 * a, color="#777777", ls=":", lw=1.5, label=r"Comparison constraint $b=2a$")
ax.scatter([1/7], [2/7], s=45, color=TEAL, zorder=4)
ax.annotate(r"Flexible: $a=1/7$", (1/7, 2/7), (.185, .325), fontsize=10,
            arrowprops={"arrowstyle": "-", "color": TEAL})
ax.scatter([1/8], [1/4], s=40, color=ORANGE, zorder=4)
ax.annotate(r"Prescribed: $a=1/8$", (1/8, 1/4), (.175, .195), fontsize=10,
            arrowprops={"arrowstyle": "-", "color": ORANGE})
ax.scatter([1/512], [1/256], s=30, color=NAVY, zorder=5)
ax.annotate(r"Lemma 5.9, linear case: $a=1/512$", (1/512, 1/256), (.035, .055),
            fontsize=9.5, arrowprops={"arrowstyle": "-", "color": NAVY})
ax.set(xlim=(0, .35), ylim=(0, .52), xlabel=r"Length exponent $a$",
       ylabel=r"Diameter exponent $b$", title=r"Two simultaneous phases ($q=2$)")
ax.legend(loc="upper right", fontsize=8.8, frameon=False, bbox_to_anchor=(1.01, 1.00))
ax.grid(alpha=.16)
save(fig, "partition_frontier")

t = np.linspace(0, .0103, 650)
a0, b0, alpha, s = .2, .8, .04, .1
v = (2 * a0 * b0 + (b0 - a0) * t) / (a0 + b0)
h = np.sqrt((1 - s * s) * t * t + s * s * v * v)
H = a0 * (t + h) / (a0 + t)
K = (a0 + b0) * (v - h) / (a0 + t)
joint = np.maximum(0, (alpha - H) / K)
p = (alpha - s * 2 * a0 * b0) / (2 * (1 - s))
composed = np.maximum(0, (p * (1 + t / a0) - t) / (b0 - t))
fig, ax = plt.subplots(figsize=(7.2, 4.6))
ax.plot(t, joint, color=TEAL, lw=2.5, label="Sharp joint frontier")
ax.plot(t, composed, color=ORANGE, lw=2, ls="--", label="Separate affine phase and selection bounds")
ax.fill_between(t, composed, joint, color=TEAL, alpha=.09)
ax.axvline(.005, color="#888888", lw=1.2, ls=":")
ax.scatter([.005], [.0022865312855382966], color=TEAL, s=40, zorder=4)
ax.annotate("0.00228653", (.005, .0022865312855382966), (.0061, .0032), fontsize=10,
            arrowprops={"arrowstyle": "-", "color": TEAL})
ax.set(xlabel=r"Density-increment threshold $t$", ylabel="Guaranteed high-average mass",
       xlim=(0, .0103), ylim=(-.00012, .0062))
ax.ticklabel_format(axis="y", style="plain", useOffset=False)
ax.legend(frameon=False, fontsize=9.5, loc="upper right")
ax.grid(alpha=.16)
save(fig, "density_frontier")
print("Rendered partition_frontier and density_frontier as PDF and PNG.")
