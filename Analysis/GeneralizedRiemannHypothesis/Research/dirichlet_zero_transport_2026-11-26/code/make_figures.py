#!/usr/bin/env python3
"""Generate publication figures from the recorded verification output.

The plotted Dirichlet quantities are floating-point diagnostics of exact
transform formulas. They are not finite-height certificates for the
unsmoothed asymptotic theorems.
"""
from pathlib import Path
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
data = json.loads((ROOT / "data/verification.json").read_text())
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9,
    "axes.labelsize": 9, "axes.titlesize": 10,
    "axes.spines.top": False, "axes.spines.right": False,
    "pdf.fonttype": 42, "ps.fonttype": 42,
})
navy, teal, orange = "#18314b", "#007073", "#bd5b28"

rows = data["Dirichlet_imaginary_axis_checks"]["rows"]
square = data["squared_graph_checks"]["floating_checks"]
x = [r["log_y"] for r in rows]
ordinary = [float(r["normalized_y_im_f"]) for r in rows]
three = [float(r["normalized_three_term_expansion"]) for r in rows]
sq = [float(r["ratio_to_predicted_limit"]) for r in square]
fig, axs = plt.subplots(1, 2, figsize=(7.2, 2.65), constrained_layout=True)
axs[0].plot(x, ordinary, "o-", color=navy, label="Exact transform (numerical)", ms=4)
axs[0].plot(x, three, "s--", color=orange, label="Three-term expansion", ms=3)
axs[1].plot(x, sq, "o-", color=teal, ms=4)
for ax in axs:
    ax.axhline(1, color="#8a949e", lw=1, ls=":")
    ax.set_xscale("log")
    ax.set_xticks([5, 10, 20, 50, 100, 200], labels=["5", "10", "20", "50", "100", "200"])
    ax.set_xlabel(r"$\log y$")
    ax.set_ylim(.57, 1.065)
    ax.grid(axis="y", alpha=.14)
axs[0].set_title("Ordinary ordinate coupling")
axs[0].set_ylabel("Ratio to leading asymptotic")
axs[0].legend(fontsize=7, loc="lower right", frameon=False)
axs[1].set_title(r"Squared ordinate coupling ($R=y^2$)")
axs[1].set_ylabel("Ratio to electrical coefficient")
fig.savefig(OUT / "transform_convergence.pdf", bbox_inches="tight")
fig.savefig(OUT / "transform_convergence.png", dpi=190, bbox_inches="tight")
plt.close(fig)

old = [-2-math.sqrt(5), -2+math.sqrt(5)]
new = [(-2-math.sqrt(13))/3, (-2+math.sqrt(13))/3]
fig, ax = plt.subplots(figsize=(7.2, 1.8), constrained_layout=True)
ax.axhline(0, color="#aab2ba", lw=1)
for k, (a, b) in enumerate(zip(old, new)):
    ax.fill_between([a,b], 0, .75, color=teal, alpha=.17)
    ax.plot([a,b], [.75,.75], color=teal, lw=2)
    ax.annotate("", xy=(b,.35), xytext=(a,.35), arrowprops={"arrowstyle":"->","color":teal,"lw":1.5})
    ax.plot(a, 0, "o", color=navy, ms=6, label="Old net zero" if k==0 else None)
    ax.plot(b, 0, "D", color=orange, ms=5, label="New net zero" if k==0 else None)
ax.set_yticks([0,.75], labels=["0","1"])
ax.set_ylabel(r"$\sigma(x)$")
ax.set_xlim(-4.65, 1.2)
ax.set_ylim(-.2, 1.3)
ax.set_xlabel("Real zero coordinate")
ax.legend(fontsize=8, loc="upper right", frameon=False)
ax.set_title("Exact repeated-root example: the transport density is the swept length")
fig.savefig(OUT / "finite_transport.pdf", bbox_inches="tight")
fig.savefig(OUT / "finite_transport.png", dpi=190, bbox_inches="tight")
plt.close(fig)
print("Created two PDF figures and their PNG previews.")
