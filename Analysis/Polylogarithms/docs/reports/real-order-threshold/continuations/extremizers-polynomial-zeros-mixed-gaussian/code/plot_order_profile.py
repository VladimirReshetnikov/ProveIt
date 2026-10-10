#!/usr/bin/env python3
"""Plot the exact limiting order-plane profile from the article's theorem."""
from pathlib import Path
import math

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

root = Path(__file__).resolve().parents[1]
(root / "figures").mkdir(exist_ok=True)
h = math.log(1.5)
p = math.log(2) / h
q = math.log(3) / math.log(2)
c = (1 - 1 / q) * q ** (-p)
d = np.linspace(-1.25, 2.5, 600)
base = q ** (-p) * (2.0 ** (-d) - 3.0 ** (-d) / q)
fig, ax = plt.subplots(figsize=(7.3, 3.9), layout="constrained")
for u, color in [(0.0, "#163c66"), (0.04, "#277c8e"), (0.08, "#ad6942")]:
    ax.plot(d, base - math.sqrt(math.pi) * u, lw=2.0,
            color=color, label=rf"$u={u:.2f}$")
ax.axhline(0, color="#777777", lw=0.8)
ax.axvline(0, color="#b0b0b0", lw=0.8, ls="--")
ax.scatter([0], [c], s=28, color="#163c66", zorder=5)
ax.annotate(r"$c$", (0, c), xytext=(7, 5), textcoords="offset points")
ax.set_xlabel(r"Inner-order displacement $d=b-\widehat b_N$")
ax.set_ylabel(r"Limit of $N^p(R_N-1)$")
ax.set_title("The outer order resolves on a much smaller scale")
ax.set_xlim(d[0], d[-1])
ax.set_ylim(-0.27, 0.2)
ax.grid(alpha=0.17)
ax.legend(loc="lower right", frameon=False,
          title=r"$a/[(\log N)N^{-(p-1/2)}]\to u$")
ax.spines[["top", "right"]].set_visible(False)
fig.savefig(root / "figures" / "order_plane_profile.pdf")
fig.savefig(root / "figures" / "order_plane_profile.png", dpi=180)
plt.close(fig)
print("Wrote exact limiting-profile figure in PDF and PNG formats.")
