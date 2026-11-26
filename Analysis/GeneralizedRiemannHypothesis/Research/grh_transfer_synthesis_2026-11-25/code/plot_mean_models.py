#!/usr/bin/env python3
"""Publication plot of the proved positive-ramp mean/pointwise sharpness models."""
from pathlib import Path
from fractions import Fraction
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
FIGURES.mkdir(parents=True, exist_ok=True)
VALIDATION = ROOT / "validation"
VALIDATION.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "DejaVu Serif",
    "font.size": 9,
    "mathtext.fontset": "dejavuserif",
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.labelsize": 9,
    "axes.titlesize": 10,
    "legend.fontsize": 8,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "savefig.bbox": "tight",
})

k = np.arange(13, 27)
X = np.power(4.0, k)
models = [
    (1, Fraction(1, 3), Fraction(32, 35), "#185c8d"),
    (2, Fraction(2, 5), Fraction(2048, 3003), "#b24e28"),
]
fig, axes = plt.subplots(1, 2, figsize=(7.1, 3.0), constrained_layout=True)
rows = []
for p, alpha_q, integral_psi_q, color in models:
    alpha = float(alpha_q)
    h = X ** (-alpha)
    L = 10 * X * np.sqrt(h)
    assert np.all(L <= X / 2)
    peak = np.sqrt(X) * h
    # Exact integral = h**p * L * integral(psi**p); the normalization is X**(p/2-1).
    moment = (X ** (p / 2 - 1)) * h ** p * L * float(integral_psi_q)
    budget_q = 10 * integral_psi_q
    exact_budget = float(budget_q)
    assert np.allclose(moment, exact_budget, rtol=1e-13, atol=1e-13)
    axes[0].plot(X, peak, "o-", color=color, lw=1.7, ms=3,
                 label=fr"$p={p}$: $X^{{{1}/{6 if p == 1 else 10}}}$")
    axes[1].plot(X, moment, "o-", color=color, lw=1.7, ms=3,
                 label=fr"$p={p}$: ${budget_q.numerator}/{budget_q.denominator}$")
    for kk, xx, hh, ll, pp, mm in zip(k, X, h, L, peak, moment):
        rows.append({"p": p, "k": int(kk), "X": float(xx), "height": float(hh),
                     "half_width": float(ll), "normalized_peak": float(pp),
                     "normalized_moment": float(mm)})

axes[0].set(xscale="log", yscale="log", xlabel=r"Bump center $X=4^k$",
            ylabel=r"$\sqrt{X}\,R_c(X)$", title="Pointwise peaks exceed the square-root scale")
axes[1].set(xscale="log", xlabel=r"Bump center $X=4^k$",
            ylabel=r"$X^{p/2-1}\int_{\mathrm{bump}} R_c(x)^p\,dx$",
            title="The normalized mean budgets stay constant", ylim=(0, 11))
for ax in axes:
    ax.grid(which="major", color="#d7dce0", lw=0.55)
    ax.legend(loc="upper left" if ax is axes[0] else "lower left", frameon=False)

fig.savefig(FIGURES / "mean_sharpness.pdf")
fig.savefig(FIGURES / "mean_sharpness.png", dpi=180)
plt.close(fig)
with (VALIDATION / "mean_sharpness_values.csv").open("w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
print(f"Created {FIGURES / 'mean_sharpness.pdf'}")
