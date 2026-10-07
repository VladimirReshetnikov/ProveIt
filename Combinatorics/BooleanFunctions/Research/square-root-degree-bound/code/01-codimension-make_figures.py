#!/usr/bin/env python3
"""Regenerate the two exact-data scientific figures used by the article."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "serif",
    "font.size": 11,
    "mathtext.fontset": "cm",
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.labelsize": 12,
    "legend.frameon": False,
    "savefig.bbox": "tight",
    "pdf.fonttype": 42,
})
navy, teal, gray = "#203954", "#087F8C", "#586574"

values = np.array([-2, 0, 2, 4, 6, 10])
counts = np.array([77, 296, 417, 248, 47, 3])
fig, ax = plt.subplots(figsize=(7.1, 3.6))
ax.bar(values, counts / 1088, width=1.05, color=navy)
for x, n in zip(values, counts):
    ax.text(x, n / 1088 + .009, str(n) + "/1088",
            ha="center", va="bottom", fontsize=9)
ax.axvline(31 / 17, color=teal, linewidth=1.3, linestyle="--",
           label=r"Mean $31/17$")
ax.set_xticks(values)
ax.set_ylim(0, .445)
ax.set_xlabel(r"Conditional coordinate sum $H_{20}$")
ax.set_ylabel("Probability")
ax.legend(loc="upper right")
ax.grid(axis="y", alpha=.13)
ax.set_axisbelow(True)
fig.tight_layout()
fig.savefig(OUT / "exceptional_cell.pdf")
fig.savefig(OUT / "exceptional_cell.png", dpi=180)
plt.close(fig)

u = np.linspace(0, 1, 801)
fig, axes = plt.subplots(1, 2, figsize=(7.3, 3.15), sharex=True)
for ax, k, bound in zip(
        axes, (2, 3),
        (2 + 4*u*(1-u), 4*np.maximum(2*u-u*u, 1-u*u))):
    ax.plot(u, bound, color=navy, linewidth=2)
    ax.axhline(k, color=teal, linestyle="--", linewidth=1.2)
    ax.set_title(r"Codimension $" + str(k) + "$", fontsize=12)
    ax.set_xlabel(r"Fractional parity mean $u$")
    ax.set_xticks([0, .5, 1], ["0", "1/2", "1"])
    ax.set_yticks([k, k+.5, k+1])
    ax.set_ylim(k-.08, k+1.15)
    ax.grid(alpha=.13)
axes[0].set_ylabel(r"Lower bound for $\operatorname{Var}(H_N\mid C)$")
fig.tight_layout(w_pad=2.3)
fig.savefig(OUT / "parity_bounds.pdf")
fig.savefig(OUT / "parity_bounds.png", dpi=180)
plt.close(fig)
print("Wrote exceptional_cell and parity_bounds in PDF and PNG formats.")
