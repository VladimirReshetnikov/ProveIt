"""Reproduce the article figures from proved bounds and recorded formula values.

Figure 1 uses exact rational sums for D_k and the preceding report's Dhat_k:
  D_k    = sum_j C(k,j) (2/(3k))^j (k-j+2)!/(k+2)!
  Dhat_k = sum_j C(k,j) (2/(3k))^j 2/(j+2)!
The curves are 1/D_k and 1/Dhat_k, relative to the geometric ceiling v_k.

Figure 2 plots excess above 1/3. The finite-parameter values come verbatim
from data/verify_norm_limit.json; the simple rate is 10*2^(-floor(d/8)).
The finite-parameter decimals were evaluated at 100-digit precision by that
checker, not certified by interval arithmetic. No curve estimates an optimum.

Run with Python, matplotlib, and numpy. Output files are written in figures/.
"""
from decimal import Decimal, getcontext
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import PercentFormatter, ScalarFormatter
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
FIGURES.mkdir(exist_ok=True)
getcontext().prec = 80

NAVY = "#213A5C"
TEAL = "#187B75"
GRAY = "#737D88"
GRID = "#E2E7EB"

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 10,
    "axes.titlesize": 12,
    "axes.labelsize": 10,
    "xtick.labelsize": 9,
    "ytick.labelsize": 9,
    "legend.fontsize": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.edgecolor": "#A5ADB5",
    "axes.labelcolor": "#273746",
    "text.color": "#273746",
    "xtick.color": "#455563",
    "ytick.color": "#455563",
    "figure.facecolor": "white",
    "axes.facecolor": "white",
    "savefig.facecolor": "white",
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})


def save(fig, name):
    fig.savefig(FIGURES / f"{name}.pdf", bbox_inches="tight", pad_inches=0.05)
    fig.savefig(FIGURES / f"{name}.png", dpi=240, bbox_inches="tight", pad_inches=0.05)
    plt.close(fig)


degrees = np.arange(1, 101)
new, old = [], []
for k in degrees:
    k = int(k)
    scale = Fraction(2, 3 * k)
    d_new = sum(Fraction(comb(k, j)) * scale ** j
                * Fraction(factorial(k - j + 2), factorial(k + 2))
                for j in range(k + 1))
    d_old = sum(Fraction(comb(k, j)) * scale ** j
                * Fraction(2, factorial(j + 2)) for j in range(k + 1))
    new.append(float(1 / d_new))
    old.append(float(1 / d_old))

fig, ax = plt.subplots(figsize=(6.3, 3.65))
ax.set_title("Local phase-removal coefficients", loc="left", pad=11)
ax.axhline(1, color=GRAY, linestyle=(0, (4, 3)), linewidth=1.2,
           label="Geometric ceiling")
ax.plot(degrees, new, color=TEAL, linewidth=2.2,
        label=r"New face cover: $1/D_k$")
ax.plot(degrees, old, color=NAVY, linewidth=1.9,
        label=r"Previous cover: $1/\widehat D_k$")
ax.set_xscale("log")
ax.set_xlim(1, 100)
ax.set_xticks([1, 2, 5, 10, 20, 50, 100])
ax.get_xaxis().set_major_formatter(ScalarFormatter())
ax.set_ylim(0.79, 1.008)
ax.set_yticks([0.80, 0.85, 0.90, 0.95, 1.00])
ax.yaxis.set_major_formatter(PercentFormatter(1, decimals=0))
ax.set_xlabel(r"Degree parameter $k$ (logarithmic scale)")
ax.set_ylabel(r"Fraction of the geometric ceiling $v_k$")
ax.grid(axis="y", color=GRID, linewidth=0.7)
ax.legend(loc="center right", bbox_to_anchor=(1, 0.42), frameon=False)
fig.text(0.125, 0.015,
         r"Proved lower coefficients; the limit $m\to\infty$ is taken first for each $k$.",
         fontsize=8, color=GRAY)
fig.tight_layout(rect=[0, 0.06, 1, 1])
save(fig, "localization_retention")


norm_source = ROOT / "data" / "verify_norm_limit.json"
norm = json.loads(norm_source.read_text())
table = norm["finite_parameter_table"]
table_d = np.array([row["d"] for row in table])
third = Decimal(1) / Decimal(3)
table_excess = np.array([
    float(Decimal(row["finite_parameter_upper_bound"]) - third)
    for row in table
])
rate_d = np.arange(80, 161)
rate_excess = 10.0 * np.power(2.0, -(rate_d // 8))

fig, ax = plt.subplots(figsize=(6.3, 3.85))
ax.set_title("Upper bounds approaching the limiting constant", loc="left", pad=11)
ax.semilogy(table_d, table_excess, color=TEAL, marker="o", markersize=4.2,
            linewidth=1.65, label="Finite-parameter bound (table values)")
ax.step(rate_d, rate_excess, where="post", color=NAVY, linewidth=1.65,
        label=r"Simple rate: $10\,2^{-\lfloor d/8\rfloor}$")
ax.set_xlim(45, 162)
ax.set_ylim(4e-6, 0.30)
ax.set_xticks([48, 64, 80, 96, 112, 128, 144, 160])
ax.set_xlabel(r"Gowers norm order $d$")
ax.set_ylabel(r"Upper bound minus the proved limit $1/3$")
ax.grid(axis="y", which="major", color=GRID, linewidth=0.7)
ax.legend(loc="upper right", frameon=False)
fig.text(0.125, 0.042,
         "Markers evaluate the proved parameter inequality; joining lines guide the eye.",
         fontsize=8, color=GRAY)
fig.text(0.125, 0.008,
         "Table decimals use 100-digit arithmetic and are not interval-certified.",
         fontsize=8, color=GRAY)
fig.tight_layout(rect=[0, 0.09, 1, 1])
save(fig, "norm_upper_bounds")


inputs = {
    "localization_retention": {
        "degrees": "integer k = 1,...,100",
        "new_denominator": "sum_{j=0}^k binom(k,j)*(2/(3*k))^j*(k-j+2)!/(k+2)!",
        "previous_denominator": "sum_{j=0}^k binom(k,j)*(2/(3*k))^j*2/(j+2)!",
        "arithmetic": "exact rational sums, converted to floats only for plotting",
        "meaning": "proved asymptotic lower coefficients divided by the geometric ceiling",
    },
    "norm_upper_bounds": {
        "finite_parameter_source": "data/verify_norm_limit.json: finite_parameter_table",
        "simple_rate_excess": "10*2^(-floor(d/8)), for integers d=80,...,160",
        "ordinate": "displayed upper bound minus 1/3",
        "numerical_status": norm["scope"],
        "meaning": "bounds from proved inequalities; no numerical estimate of an optimum",
    },
}
(FIGURES / "figure_inputs.json").write_text(json.dumps(inputs, indent=2) + "\n")
print("Wrote localization_retention and norm_upper_bounds as PDF and PNG.")
