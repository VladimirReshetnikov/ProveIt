#!/usr/bin/env python3
"""Plot recorded complex-resonance diagnostics and analytic reference curves.

Usage:
  python3 code/plot_complex_resonance.py --data data/complex_resonance_checks.json

Only the supplied JSON supplies numerical observations. Reference lines are
computed from exact analytic coefficient formulas; no curve is fitted to data.
Dependencies: matplotlib, numpy, mpmath.

For panel (b), with lambda=2*pi*i and r1=gamma-1, let
  r2=((gamma-1)^2+zeta(2)+1)/2,
  r3=r1^3/6+r1*(zeta(2)+1)/2+(zeta(3)-1)/3,
  D=r2+gamma_1, J=gamma_2/2-r3,
  c=+/-sqrt(-2*lambda*D), d=-lambda*(r1+4*D/3),
  e=lambda^2/c * (J+r1^2/2+(3*gamma-2)*D+13*D^2/9).
Then u=t/y=1+c*Y^(-1/2)+d*Y^(-1)+e*Y^(-3/2)+O(Y^(-2)).
The two branches have identical |d| and |e|. Their reference error laws
are |d|/Y and |e|/Y^(3/2), respectively.
"""

import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FixedLocator, FuncFormatter, NullFormatter
import mpmath as mp
import numpy as np


def complex_value(record):
    return mp.mpc(record["real"], record["imag"])


def reference_constants():
    mp.mp.dps = 70
    gamma = mp.euler
    r1 = gamma - 1
    r2 = (r1*r1 + mp.zeta(2) + 1) / 2
    r3 = r1**3 / 6 + r1*(mp.zeta(2)+1)/2 + (mp.zeta(3)-1)/3
    D = r2 + mp.stieltjes(1)
    J = mp.stieltjes(2)/2 - r3
    lam = 2j*mp.pi
    c = mp.sqrt(-2*lam*D)
    d = -lam*(r1+4*D/3)
    e = lam**2/c * (J+r1*r1/2+(3*gamma-2)*D+mp.mpf(13)/9*D**2)
    return float(abs(d)), float(abs(e))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"complex_resonance_checks.json")
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parents[1]/"figures")
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 70

    plt.rcParams.update({
        "font.family": "STIXGeneral",
        "mathtext.fontset": "stix",
        "font.size": 8.5,
        "axes.labelsize": 9,
        "axes.titlesize": 10,
        "xtick.labelsize": 8,
        "ytick.labelsize": 8,
        "legend.fontsize": 7.8,
        "axes.linewidth": 0.65,
        "xtick.major.width": 0.65,
        "ytick.major.width": 0.65,
        "xtick.major.size": 3,
        "ytick.major.size": 3,
        "text.color": "#20252b",
        "axes.labelcolor": "#20252b",
        "axes.edgecolor": "#6b7280",
        "xtick.color": "#404751",
        "ytick.color": "#404751",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
    })
    # Exact target width: 16 cm. Height keeps the two panels readable in print.
    fig, axes = plt.subplots(1, 2, figsize=(16/2.54, 7.8/2.54))
    fig.subplots_adjust(left=0.092, right=0.985, bottom=0.185,
                        top=0.86, wspace=0.34)
    palette = {"0.1": "#176b91", "-0.15": "#8857a5", "0.2": "#b86b21"}

    ax = axes[0]
    grid_k = np.linspace(0.88, 3.12, 150)
    for beta_string in ("0.1", "-0.15", "0.2"):
        beta = mp.mpf(beta_string)
        eps = 1j*beta
        z1 = eps*mp.zeta(1+eps)
        a0 = mp.exp((mp.log(z1)-mp.loggamma(1-eps))/eps)
        intercept = float(mp.log10(abs(a0)))
        slope = float(-2*mp.pi/(abs(beta)*mp.log(10)))
        reference = slope*grid_k + intercept
        color = palette[beta_string]
        ax.plot(grid_k, reference, color=color, lw=1.05,
                linestyle=(0, (3.5, 2.4)), zorder=1)
        rows = sorted((r for r in data["critical_lattice"] if r["beta"] == beta_string),
                      key=lambda r: abs(r["k"]))
        observations = [float(mp.log10(mp.mpf(r["tau"])*abs(complex_value(r["t_over_tau"]))))
                        for r in rows]
        ax.plot([abs(r["k"]) for r in rows], observations,
                linestyle="none", marker="o", ms=4.0, mew=0.6,
                mec="white", mfc=color, zorder=3,
                label=rf"$\beta={beta_string}$")
    ax.set_title("(a)  Geometric accumulation", loc="left", pad=10)
    ax.set_xlabel(r"Lattice index $|k|$")
    ax.set_ylabel(r"$\log_{10}|t_{c,k}|$")
    ax.set_xlim(0.8, 3.2)
    ax.set_ylim(-88, -9)
    ax.set_xticks([1, 2, 3])
    ax.set_yticks([-80, -60, -40, -20])
    ax.grid(axis="y", color="#dbe0e5", lw=0.55, zorder=0)
    ax.legend(loc="lower left", frameon=False, handletextpad=0.4,
              borderpad=0.2, labelspacing=0.30)
    ax.text(0.99, 0.98, "dots: computation\ndashes: analytic core",
            transform=ax.transAxes, va="top", ha="right", fontsize=7.1,
            linespacing=1.15, color="#555c64")

    ax = axes[1]
    color1 = "#176b91"
    color2 = "#b34a3d"
    d_abs, e_abs = reference_constants()
    grid_y = np.geomspace(73, 345, 150)
    ax.plot(grid_y, d_abs/grid_y, color=color1, lw=1.1,
            linestyle=(0, (3.5, 2.4)), alpha=0.95, zorder=1)
    ax.plot(grid_y, e_abs/grid_y**1.5, color=color2, lw=1.1,
            linestyle=(0, (3.5, 2.4)), alpha=0.95, zorder=1)
    for branch, marker, fill in ((1, "o", True), (-1, "^", False)):
        rows = sorted((r for r in data["branch_splitting"]
                       if r["k"] == 1 and r["branch"] == branch), key=lambda r: r["Y"])
        Y = [r["Y"] for r in rows]
        for field, color in (("first_order_error", color1), ("second_order_error", color2)):
            values = [float(r[field]) for r in rows]
            ax.plot(Y, values, color=color, lw=0.55, alpha=0.7, zorder=2)
            ax.plot(Y, values, linestyle="none", marker=marker, ms=4.0,
                    markeredgewidth=0.8, mec=color, mfc=color if fill else "white", zorder=3)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(70, 360)
    ax.set_ylim(0.0033, 0.19)
    ax.xaxis.set_major_locator(FixedLocator([80, 160, 320]))
    ax.xaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:g}"))
    ax.xaxis.set_minor_locator(FixedLocator([]))
    ax.yaxis.set_minor_formatter(NullFormatter())
    ax.set_title("(b)  Inverse approximation errors", loc="left", pad=10)
    ax.set_xlabel(r"$Y=\log(1/y)$,  $\lambda_0=2\pi i$")
    ax.set_ylabel(r"Absolute error in $u=t/y$")
    ax.grid(axis="y", which="major", color="#dbe0e5", lw=0.55, zorder=0)
    handles = [
        Line2D([0], [0], color=color1, marker="o", ms=3.2, lw=0.65,
               label=r"$u^{(1)}=1+c_\pm Y^{-1/2}$"),
        Line2D([0], [0], color=color2, marker="o", ms=3.2, lw=0.65,
               label=r"$u^{(2)}=u^{(1)}+dY^{-1}$"),
        Line2D([0], [0], color="#656b73", lw=1.0, linestyle=(0, (3.5, 2.4)),
               label="Theoretical leading errors"),
    ]
    ax.legend(handles=handles, loc="lower left", frameon=False,
              handlelength=1.8, handletextpad=0.6, borderpad=0.2, labelspacing=0.33)
    ax.text(0.99, 0.98, r"$\bullet\;+$ branch   $\triangle\;-$ branch",
            transform=ax.transAxes, va="top", ha="right", fontsize=7.4,
            color="#555c64")

    for ax in axes:
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.tick_params(which="both", direction="out")

    base = args.output_dir/"complex_resonance_figure"
    fig.savefig(base.with_suffix(".pdf"), metadata={
        "Title": "Geometric critical-point accumulation and complex inverse convergence",
        "Subject": "Recorded high-precision diagnostics and exact analytic reference terms",
        "Creator": "plot_complex_resonance.py / matplotlib",
    })
    fig.savefig(base.with_suffix(".png"), dpi=300)
    plt.close(fig)
    print(json.dumps({"pdf": str(base.with_suffix(".pdf")),
                      "png": str(base.with_suffix(".png")),
                      "width_cm": 16, "height_cm": 7.8,
                      "reference_abs_d": d_abs, "reference_abs_e": e_abs}, indent=2))


if __name__ == "__main__":
    main()
