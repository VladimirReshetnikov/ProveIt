#!/usr/bin/env python3
"""Numerical illustrations; exact finite values come from verify_sampling.py."""
from pathlib import Path
import json
import math
from decimal import Decimal, getcontext
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from verify_sampling import minimax

ROOT = Path(__file__).resolve().parents[1]
(ROOT / "figures").mkdir(exist_ok=True)
getcontext().prec = 60
constants = []
for d in range(1, 9):
    def total(x):
        return sum(x**j / Decimal(math.factorial(j)) for j in range(d))
    lo, hi = Decimal(0), Decimal(2*d+2)
    for _ in range(220):
        mid = (lo+hi)/2
        if total(mid) > mid**d / Decimal(math.factorial(d-1)):
            lo = mid
        else:
            hi = mid
    lam = (lo+hi)/2
    c = lam * (-lam).exp() * total(lam)
    constants.append({"d": d, "lambda": str(lam),
                      "C_d": str(c)})
phi = (1+Decimal(5).sqrt())/2
assert abs(Decimal(constants[1]["C_d"]) - phi**3 * (-phi).exp()) < Decimal("1e-38")
Path(__file__).with_name("poisson_constants.json").write_text(json.dumps(constants, indent=2)+"\n")

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42})
colors = ["#215A85", "#008480", "#BD6236"]
fig, axes = plt.subplots(1, 2, figsize=(11.3, 4.05), constrained_layout=True)
xs = [8*i/600 for i in range(601)]
for d, color in zip((1, 2, 3), colors):
    ys = [x*math.exp(-x)*sum(x**j/math.factorial(j) for j in range(d)) for x in xs]
    axes[0].plot(xs, ys, color=color, lw=2, label=f"{d} interpolation points")
    lam, c = float(constants[d-1]["lambda"]), float(constants[d-1]["C_d"])
    axes[0].scatter([lam], [c], color=color, s=26, zorder=4)
axes[0].set(xlabel=r"Mean sample count $\lambda$ in one class",
            ylabel=r"$\lambda\,\Pr(\mathrm{Poisson}(\lambda)<d)$",
            title="Sharp asymptotic loss per class", xlim=(0, 8), ylim=(0, 1.5))
axes[0].legend(frameon=False, fontsize=9)
axes[0].grid(alpha=.16)
rs = list(range(33))
values = [float(minimax(32, 3, r, 2)[0]) for r in rs]
axes[1].plot(rs, [min(1, 6/(r+1)) for r in rs], color="#85939F", lw=1.9,
             ls="--", label=r"Universal bound $\min(1,6/(r+1))$")
axes[1].plot(rs, values, color=colors[1], lw=2, marker="o", markersize=3,
             label="Exact finite minimax loss")
axes[1].set(xlabel="Number of distinct sampled columns", ylabel="Fraction of lost points",
            title=r"Finite example: $n=32$, $q=3$, $d=2$", xlim=(0, 32), ylim=(0, 1.06))
axes[1].legend(frameon=False, fontsize=9)
axes[1].grid(alpha=.16)
fig.savefig(ROOT / "figures" / "sampling_extrema.pdf")
fig.savefig(ROOT / "figures" / "sampling_extrema.png", dpi=170)
print(json.dumps({"figure": "figures/sampling_extrema.pdf", "constants": constants[:4]}, indent=2))
