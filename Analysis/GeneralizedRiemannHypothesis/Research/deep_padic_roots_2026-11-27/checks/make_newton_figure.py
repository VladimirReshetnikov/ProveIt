#!/usr/bin/env python3
"""Render the exact Newton polygon; no numerical root finding is used."""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / "data/lattice_certificates.json").read_text())
witness = data["nine_root_witness"]

def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k

points = [(k, v2(abs(n))) for k, n in
          enumerate(witness["translated_coefficients_low_to_high"]) if n]
vertices = witness["newton_vertices"]
fig, ax = plt.subplots(figsize=(7.5, 3.7), layout="constrained")
fig.patch.set_facecolor("white")
ax.set_facecolor("#fafbfd")
ax.scatter(*zip(*points), s=38, color="#425569", zorder=3,
           label="Exact coefficient valuations")
ax.plot(*zip(*vertices[:2]), linewidth=2.6, color="#125b8f",
        label="Nine roots at depth 10/9")
ax.plot(*zip(*vertices[1:]), linewidth=2.6, color="#bb663c",
        label="One root at depth 1")
for k, v in vertices:
    ax.annotate(f"({k}, {v})", (k, v), xytext=(7, 7),
                textcoords="offset points", fontsize=9, color="#243548")
ax.set(xlim=(-0.4, 11.1), ylim=(-0.5, 12.1),
       xlabel="Taylor coefficient index k", ylabel="2-adic valuation")
ax.set_xticks(range(11))
ax.set_yticks(range(0, 13, 2))
ax.grid(axis="y", color="#dbe2e8", linewidth=0.7)
ax.spines[["top", "right"]].set_visible(False)
ax.legend(loc="upper right", frameon=True, facecolor="white", fontsize=9)
(ROOT / "figures").mkdir(exist_ok=True)
fig.savefig(ROOT / "figures/nine_roots_newton.pdf")
fig.savefig(ROOT / "figures/nine_roots_newton.png", dpi=180)
plt.close(fig)

