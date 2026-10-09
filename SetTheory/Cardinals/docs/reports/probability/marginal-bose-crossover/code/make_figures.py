"""Rebuild the article's scientific figures from formulas and saved validation.

Run from any directory. Figures are written as vector PDF and 200-dpi PNG.
The curve data are saved separately; no external network access is required.
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from mpmath import mp
from scipy.special import zeta

from bose_crossover import evaluate


ROOT = Path(__file__).resolve().parents[1]
FIG = ROOT / "figures"
DATA = ROOT / "data"
COLORS = ["#176B73", "#C27832", "#5E548E", "#A84451"]
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9,
    "axes.titlesize": 10, "axes.titleweight": "bold",
    "axes.labelsize": 9, "legend.fontsize": 8,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.edgecolor": "#56616A", "axes.labelcolor": "#17324D",
    "text.color": "#17324D", "xtick.color": "#56616A",
    "ytick.color": "#56616A", "grid.alpha": 0.2,
    "pdf.fonttype": 42, "ps.fonttype": 42,
})


def save(fig, name):
    fig.savefig(FIG / f"{name}.pdf", bbox_inches="tight")
    fig.savefig(FIG / f"{name}.png", dpi=200, bbox_inches="tight")
    plt.close(fig)


def main():
    FIG.mkdir(exist_ok=True)
    mp.dps = 45
    curve = []
    for s_float in np.geomspace(1e-5, 1, 90):
        s = mp.mpf(str(s_float))
        g = evaluate(s, abs_tol=mp.mpf("1e-27")).midpoint
        constant = 2 * g / mp.gamma(mp.mpf(1)/4) - mp.log(8/(s*s))
        curve.append({"s": str(s), "G": str(g),
                      "normalized_finite_part": str(constant)})

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.05, 2.75), layout="constrained")
    ax.semilogx([float(r["s"]) for r in curve],
                [float(r["normalized_finite_part"]) for r in curve],
                color=COLORS[0], lw=1.8, label="convergent representation")
    independent = json.loads((DATA / "independent_validation.json").read_text())
    points = [r for r in independent["rows"] if 1e-5 <= float(r["lambda"]) <= 1]
    ax.scatter([float(r["lambda"]) for r in points],
               [float(r["normalized_log_constant_plus_corrections"]) for r in points],
               color=COLORS[1], marker="o", s=26, zorder=4,
               label="independent quadrature")
    ax.axhline(np.pi/2, color=COLORS[2], ls="--", lw=1.2,
               label=r"proved limit $\pi/2$")
    ax.set(xlabel=r"stiffness $s$", ylabel=r"$2G(s)/\Gamma(1/4)-\log(8/s^2)$",
           title="A. The finite marginal constant", ylim=(1.53, 2.07))
    ax.legend(loc="upper left", frameon=False)
    ax.grid(axis="y")

    j = np.arange(1, 751)
    degree = 4*j + 1
    bound_curves = []
    for color, s in zip(COLORS, [0.1, 1., 3., 4.9]):
        log_bound = (.5*np.log10(np.pi) + np.log10(zeta(2*j+1, 1))
                     - np.log10(4*j+2) - .25*np.log10(2*j+.25)
                     + (4*j+2)*np.log10(s/np.sqrt(8*np.pi)))
        bx.semilogx(degree, log_bound, color=color, lw=1.5,
                    label=rf"$s={s:g}$")
        bound_curves.append({"s": s, "degrees": degree.tolist(),
                             "log10_analytic_error_bounds": log_bound.tolist()})
    bx.axhline(-30, color="#777777", ls=":", lw=1)
    bx.set(xlabel="retained degree", ylabel=r"$\log_{10}$ of contour error bound",
           title="B. Explicit convergence rates", ylim=(-40, 0), xlim=(5, 3001))
    bx.legend(loc="lower left", frameon=False, ncol=2)
    bx.grid(axis="y")
    save(fig, "continuum_accuracy")

    lattice = json.loads((DATA / "lattice_validation.json").read_text())
    algorithm = json.loads((DATA / "algorithm_validation.json").read_text())
    zero_rows = sorted([r for r in lattice["rows"]
                        if r["s_delta_over_sqrtT"] == 0], key=lambda r:r["T"])
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(7.05, 2.75), layout="constrained")
    x = np.sqrt([r["T"] for r in zero_rows])
    y = [r["difference_divided_by_T32"] for r in zero_rows]
    b, d = lattice["constants"]["B"], lattice["constants"]["C2_at_zero"]
    line_x = np.linspace(0, .33, 120)
    ax.plot(line_x, (b+d*line_x)*1000, color=COLORS[0], lw=1.6,
            label=r"$\mathcal{B}+\mathcal{D}\sqrt{T}$")
    ax.scatter(x, np.array(y)*1000, s=32, color=COLORS[1], zorder=4,
               label="subtracted lattice quadrature")
    ax.axhline(b*1000, ls="--", color=COLORS[2], lw=1,
               label=r"limit $\mathcal{B}$")
    ax.set(xlabel=r"$\sqrt{T}$", ylabel=r"$10^3(N_{\rm lat}-N_{\rm con})/T^{3/2}$",
           title="A. First two lattice coefficients", xlim=(0, .34))
    ax.legend(frameon=False, loc="upper left")
    ax.grid(axis="y")

    inverse = sorted(algorithm["inversions"], key=lambda r:float(r["delta"]))
    delta = [float(r["delta"]) for r in inverse]
    for order, label, color in zip(range(3),
             [r"$T_0$ (Lambert $W$)", "first correction", "second correction"], COLORS):
        errors = [float(r["absolute_errors_order_0_1_2"][order]) for r in inverse]
        bx.loglog(delta, errors, marker="o", ms=3.5, lw=1.4, color=color, label=label)
    bx.set(xlabel=r"stiffness $\delta$", ylabel="absolute temperature error",
           title=r"B. Continuum inversion, $n_*=0.1$")
    bx.legend(frameon=False, loc="lower right")
    bx.grid(axis="both", which="major")
    save(fig, "lattice_and_inverse")

    (DATA / "figure_data.json").write_text(json.dumps({
        "status": "Ordinary floating-point plot data; proofs and certified balls are separate.",
        "finite_part_curve": curve,
        "contour_bound_curves": bound_curves,
        "other_panels": "Use lattice_validation.json and algorithm_validation.json directly."
    }, indent=2)+"\n")
    print("Wrote two vector figures, PNG previews, and figure_data.json")


if __name__ == "__main__":
    main()
