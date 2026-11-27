#!/usr/bin/env python3
"""Plot exact sharpness families; numerical points are illustrations only."""
from pathlib import Path
from fractions import Fraction
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader((ROOT / "data/scaling_eigenvalues.csv").open()))
b = np.array([float(Fraction(row["b_exact"])) for row in rows])
d = np.array([float(row["D"]) for row in rows])
t = 2*b
ratio = np.array([float(row["D_over_t4"]) for row in rows])
grid = np.geomspace(b.min(), b.max(), 200)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False})
fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.75), constrained_layout=True)
ax = axes[0]
ax.loglog(grid, 2*grid**2, color="#007F86", lw=2.4,
          label=r"$\{0,ib,-ib\}:\ D=2b^2$")
ax.loglog(b, d, "o-", color="#D65A31", ms=4.5, lw=2.1,
          label=r"$\{2b,ib,-ib\}$: computed $D$")
ax.loglog(grid, 50*grid**4, "--", color="#D65A31", alpha=.7, lw=1.4,
          label=r"cubic asymptote $50b^4$")
ax.set(xlabel=r"Largest imaginary part $b$", ylabel=r"PSD defect $D$",
       title="Two necessary powers (n = 3)")
ax.grid(True, which="major", color="#E3E7EB", lw=.7)
ax.legend(frameon=False, fontsize=8.2, loc="lower right")
ax = axes[1]
ax.semilogx(t[::-1], ratio[::-1], "o-", color="#D65A31", ms=4.5, lw=2)
ax.axhline(25/8, color="#263E56", ls="--", lw=1.5,
           label=r"Proved limit $25/8$")
lower = (25/8)/(1+25*t**2+9*t**4/4)
ax.fill_between(t[::-1], lower[::-1], 25/8, color="#B8C8D8", alpha=.35,
                label="Exact algebraic enclosure")
ax.set(xlabel=r"Scale $t$ (approaches zero to the left)", ylabel=r"$D/t^4$",
       title="Cubic sharpness with an exact enclosure", ylim=(0, 3.4))
ax.grid(True, which="major", color="#E3E7EB", lw=.7)
ax.legend(frameon=False, fontsize=8.2, loc="lower left")
folder = ROOT / "figures"
folder.mkdir(exist_ok=True)
fig.savefig(folder / "sharp_exponents.pdf", bbox_inches="tight")
fig.savefig(folder / "sharp_exponents.png", dpi=180, bbox_inches="tight")
plt.close(fig)
print("Created figures/sharp_exponents.pdf and figures/sharp_exponents.png")
