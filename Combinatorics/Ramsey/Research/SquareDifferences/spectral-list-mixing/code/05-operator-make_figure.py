#!/usr/bin/env python3
"""Regenerate the report's analytic comparison figure (not experimental data)."""
from pathlib import Path
import math

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "figures"
DEST.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.labelcolor": "#183A54",
    "text.color": "#183A54",
    "axes.titleweight": "bold",
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})
fig, (ax, bx) = plt.subplots(1, 2, figsize=(8.1, 3.3))
x = np.linspace(4, 24, 401)
p = 10.0**x
m = 16
old = (32*m)**0.25*p**(-0.125)
new = (1-2.0**(-m))*(np.sqrt(p)+1)/p
ax.plot(x, np.log10(old), color="#A65B35", lw=2, label="Source bound")
ax.plot(x, np.log10(new), color="#146B69", lw=2, label="Operator bound")
ax.set_title("List error, 16 edges", loc="left", fontsize=10)
ax.set_xlabel(r"$\log_{10} p$")
ax.set_ylabel(r"$\log_{10}$ upper bound")
ax.set_xlim(4, 24)
ax.set_ylim(-12.5, 0.6)
ax.set_xticks([4, 8, 12, 16, 20, 24])
ax.grid(axis="y", color="#D9E1E7", lw=0.6)
ax.legend(frameon=False, loc="lower left", fontsize=8)
blocks = [161, 17, 5]
log_factorial = math.lgamma(25)/math.log(10)
sizes = [b*log_factorial for b in blocks]
labels = ["Source\n161 blocks", "Same mass target\n17 blocks", "Fractional moment\n5 blocks"]
bars = bx.barh(range(3), sizes, color=["#A65B35", "#718D9C", "#146B69"], height=0.52)
bx.set_yticks(range(3), labels, fontsize=8)
bx.invert_yaxis()
bx.set_title("Tuple size at h = 24", loc="left", fontsize=10)
bx.set_xlabel(r"$\log_{10} d$, where $d=(24!)^{\ell}$")
bx.set_xlim(0, 4250)
bx.set_xticks([0, 1000, 2000, 3000, 4000])
bx.grid(axis="x", color="#D9E1E7", lw=0.6)
bx.set_axisbelow(True)
for bar, val in zip(bars, sizes):
    bx.text(val+55, bar.get_y()+bar.get_height()/2, f"{val:,.1f}", va="center", fontsize=8)
fig.subplots_adjust(left=0.085, right=0.97, bottom=0.18, top=0.88, wspace=0.75)
fig.savefig(DEST / "quantitative_comparison.pdf", metadata={
    "Title": "Analytic operator bounds and tuple-size comparison",
    "Author": "Research report prepared for Vladimir Reshetnikov",
    "CreationDate": None,
    "ModDate": None,
})
plt.close(fig)
print("Created figures/quantitative_comparison.pdf")
