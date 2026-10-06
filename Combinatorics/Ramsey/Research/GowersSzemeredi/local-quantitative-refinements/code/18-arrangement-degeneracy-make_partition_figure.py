#!/usr/bin/env python3
"""Regenerate the article's comparison of quadratic partition exponents."""
from pathlib import Path
import matplotlib.pyplot as plt

out = Path(__file__).resolve().parent
q = list(range(1, 9))
old = [2.0 ** (-11 * x - 1) for x in q]
general = [1 / (126 * x * x + 129 * x + 2) for x in q]
shared = [1 / (99 * x + 98) for x in q]
obstruction = [1 / (7 * x + 1) for x in q]

plt.rcParams.update({"font.size": 10, "font.family": "DejaVu Sans"})
fig, ax = plt.subplots(figsize=(7.5, 4.5), constrained_layout=True)
ax.semilogy(q, old, "o-", color="#ad4b2c", linewidth=1.6,
            label=r"Gowers Lemma 5.9: $1/(2\cdot2048^q)$")
ax.semilogy(q, general, "o-", color="#17688b", linewidth=1.6,
            label=r"General quadratics: strict $a<1/(126q^2+129q+2)$")
ax.semilogy(q, shared, "s-", color="#2e8979", linewidth=1.6,
            label=r"Shared leading coefficient: strict $a<1/(99q+98)$")
ax.semilogy(q, obstruction, "--", color="#626278", linewidth=1.6,
            label=r"Universal obstruction: $a\leq1/(7q+1)$")
ax.set_xticks(q)
ax.set_xlabel(r"Number of polynomial phases $q$")
ax.set_ylabel(r"Exponent $a$ (length $r^a$, oscillation $r^{-2a}$)")
ax.grid(True, which="major", alpha=.22)
ax.spines[["top", "right"]].set_visible(False)
ax.legend(loc="lower left", fontsize=8, framealpha=.96)
fig.savefig(out / "partition_exponents.pdf", metadata={"Title": "Quadratic partition exponents"})
fig.savefig(out / "partition_exponents.png", dpi=180)
plt.close(fig)
