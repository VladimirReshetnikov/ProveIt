#!/usr/bin/env python3
"""Regenerate exact publication figures; no data are estimated or fitted."""
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.ticker import NullLocator
import numpy as np

BASE = Path(__file__).resolve().parent.parent
OUT = BASE / "figures"
OUT.mkdir(exist_ok=True)
TEAL = "#165C67"
INK = "#19303D"
PALE = "#E6ECEE"
GRAY = "#75858B"
GOLD = "#AA7744"
plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 10,
    "axes.labelcolor": INK,
    "text.color": INK,
    "axes.edgecolor": GRAY,
    "xtick.color": INK,
    "ytick.color": INK,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "savefig.facecolor": "white",
})


def delta(r, k):
    a = 0
    while 3 ** (a + 1) <= k:
        a += 1
    if k >= 3 ** (r - 1):
        return Fraction(2, 3 ** r)
    return (Fraction(2, 3 ** (a + 1)) if k < 2 * 3 ** a
            else Fraction(4, 3 ** (a + 2)))


def save(fig, name):
    fig.savefig(OUT / (name + ".pdf"), bbox_inches="tight")
    fig.savefig(OUT / (name + ".png"), dpi=190, bbox_inches="tight")
    plt.close(fig)


fig, (ax, bx) = plt.subplots(1, 2, figsize=(8.8, 3.25),
                            gridspec_kw={"width_ratios": [1, 1.5]})
grid = np.array([[(x == 0) != (y == 0) for y in range(3)] for x in range(3)])
ax.imshow(grid, cmap=ListedColormap([PALE, TEAL]), vmin=0, vmax=1)
for x in range(3):
    for y in range(3):
        ax.text(y, x, "different" if grid[x, y] else "equal",
                ha="center", va="center", fontsize=9,
                color="white" if grid[x, y] else INK)
ax.set_xticks([0, 1, 2], ["1", r"$\zeta$", r"$\zeta^2$"])
ax.set_yticks([0, 1, 2], ["1", r"$\zeta$", r"$\zeta^2$"])
ax.set_xlabel(r"Value of $\beta$")
ax.set_ylabel(r"Value of $\alpha$")
ax.set_title("Opposite-pair construction", fontweight="bold", pad=10)
for side in ax.spines.values():
    side.set_visible(False)
ax.set_xticks(np.arange(-0.5, 3, 1), minor=True)
ax.set_yticks(np.arange(-0.5, 3, 1), minor=True)
ax.grid(which="minor", color="white", linewidth=2)
ax.tick_params(which="both", length=0)

ks = np.arange(1, 82)
bx.step(ks, [float(delta(5, int(k))) for k in ks], where="post", color=TEAL, lw=2.3)
breaks = [1, 2, 3, 6, 9, 18, 27, 54, 81]
bx.scatter(breaks, [float(delta(5, k)) for k in breaks], color=TEAL, s=19, zorder=3)
bx.set_xscale("log", base=3)
bx.set_yscale("log", base=3)
bx.set_xlim(0.9, 90)
bx.set_ylim(0.0065, 0.8)
bx.set_xticks(breaks, [str(k) for k in breaks])
yt = [Fraction(2, 3), Fraction(2, 9), Fraction(2, 27), Fraction(2, 81), Fraction(2, 243)]
bx.set_yticks([float(v) for v in yt], [f"{v.numerator}/{v.denominator}" for v in yt])
bx.xaxis.set_minor_locator(NullLocator())
bx.yaxis.set_minor_locator(NullLocator())
bx.grid(axis="y", color=PALE, lw=0.8)
bx.set_xlabel("Packet size k")
bx.set_ylabel("Least disagreement density")
bx.set_title("Exact minimum at rank five", fontweight="bold", pad=10)
fig.tight_layout(w_pad=2.4)
save(fig, "cubic_staircase")

fig, ax = plt.subplots(figsize=(7.8, 3.1))
branches = [r"$0$", r"$X^5$", r"$X$", r"$2X$", r"$3X$"]
x = np.arange(5)
uniform = np.array([7] * 5)
optimal = np.array([7, 7, 3, 3, 3])
ax.bar(x - 0.19, uniform, width=0.36, color=GRAY, label="Uniform: total 35")
ax.bar(x + 0.19, optimal, width=0.36, color=TEAL, label="Optimal unequal: total 23")
for at, vals in ((x - 0.19, uniform), (x + 0.19, optimal)):
    for i, v in zip(at, vals):
        ax.text(i, v + 0.12, str(v), ha="center", va="bottom", fontsize=10)
ax.set_xticks(x, branches)
ax.set_ylim(0, 8.7)
ax.set_yticks(range(0, 9, 2))
ax.set_ylabel("Recorded coefficients per branch")
ax.set_xlabel(r"Branches over $\mathbb{F}_5$")
ax.legend(loc="upper center", ncol=2, frameon=False, bbox_to_anchor=(0.5, 1.13))
ax.grid(axis="y", color=PALE)
ax.set_axisbelow(True)
fig.tight_layout()
save(fig, "precision_budget")
print("Created figures/cubic_staircase.{pdf,png} and figures/precision_budget.{pdf,png}")
