#!/usr/bin/env python3
"""Publication figures generated from proved formulas and bundled diagnostics."""
from pathlib import Path
import json
import math

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
FIGURES.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Serif", "font.size": 9,
    "axes.titlesize": 10, "axes.labelsize": 9,
    "legend.fontsize": 7.6, "xtick.labelsize": 8, "ytick.labelsize": 8,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.linewidth": 0.7, "lines.linewidth": 1.5,
    "savefig.facecolor": "white", "pdf.fonttype": 42,
})
NAVY, TEAL, ORANGE = "#163f60", "#16786f", "#b95e31"


def finish(fig, name):
    fig.tight_layout(pad=1.0, w_pad=2.0)
    fig.savefig(FIGURES / (name + ".pdf"),
                metadata={"CreationDate": None, "ModDate": None})
    fig.savefig(FIGURES / (name + ".png"), dpi=220)
    plt.close(fig)


def geometry():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.55, 3.15))
    u = np.linspace(0, 1.5, 500)
    ax.set_facecolor("#e6f1ee")
    ax.fill_between(u, 0, np.maximum(1-u, 0), color="#f5e8df")
    ax.plot([0, 1], [1, 0], color=ORANGE, lw=2)
    ax.plot([0, 1], [1, 0], "o", ms=4, mfc="white", mec=ORANGE)
    ax.text(.82, 1.04, "One sign change\nin an integrable density",
            ha="center", va="center", fontsize=8.4, color=TEAL)
    ax.text(.32, .23, "No finite\nsigned measure",
            ha="center", va="center", fontsize=8.4, color="#78472d")
    ax.annotate("Endpoint atom", xy=(.54, .46), xytext=(.93, .53),
                fontsize=8, ha="center", color=ORANGE,
                arrowprops={"arrowstyle": "-", "color": ORANGE, "lw": .8})
    ax.text(.2, .81, r"$a+b=1$", rotation=-45, fontsize=8.4, color=ORANGE)
    ax.set(xlim=(0, 1.5), ylim=(0, 1.5), xlabel="Outer order a",
           ylabel="Inner order b", title="A. Sharp measure threshold")
    ax.set_aspect("equal")
    grid = np.linspace(0, 1, 350)
    X, Y = np.meshgrid(grid, grid)
    signed = np.ma.masked_where(X*X+Y*Y > 1, 2*X-X*X-Y*Y)
    bx.contourf(X, Y, signed, levels=[-2, 0, 2],
                colors=["#edf0f5", "#e6f1ee"])
    q = np.linspace(0, np.pi/2, 300)
    bx.plot(np.cos(q), np.sin(q), color="#737d84", lw=1)
    R = np.linspace(0, 1, 350)
    x = R*R/2
    y = np.sqrt(R*R-x*x)
    bx.plot(x, y, color=ORANGE, lw=2)
    bx.plot([.5], [math.sqrt(3)/2], "o", ms=4, color=ORANGE)
    bx.text(.07, .79, r"$\mathrm{Im}\,F<0$", color=NAVY, fontsize=8.5)
    bx.text(.62, .32, r"$\mathrm{Im}\,F>0$", color=TEAL, fontsize=8.5)
    bx.annotate(r"$\theta=\pi/3$", xy=(.5, math.sqrt(3)/2),
                xytext=(.73, .95), fontsize=8.5, ha="center",
                arrowprops={"arrowstyle": "-", "color": ORANGE, "lw": .8})
    bx.set(xlim=(0, 1.03), ylim=(0, 1.03), xlabel=r"$\mathrm{Re}\,z$",
           ylabel=r"$\mathrm{Im}\,z$", title=r"B. Exact zero arc, $a=b=1$")
    bx.set_aspect("equal")
    finish(fig, "measure_geometry")


def boundary():
    rows = json.loads((ROOT/"data/geometry_boundary_diagnostics.json").read_text())["rows"]
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.55, 3.15))
    for b, color, marker in [("0.25", NAVY, "o"), ("0.5", TEAL, "s"), ("0.75", ORANGE, "^")]:
        branch = sorted((r for r in rows if r["b"] == b), key=lambda r: float(r["epsilon"]))
        eps = np.array([float(r["epsilon"]) for r in branch])
        actual = np.array([float(r["T_crossing"]) for r in branch])
        asymptotic = np.array([float(r["leading_crossing"]) for r in branch])
        ax.loglog(eps, actual, marker=marker, ms=3.5, color=color, label="b = "+b)
        ax.loglog(eps, asymptotic, "--", color=color, lw=.8, alpha=.85)
    ax.set(xlabel=r"$\varepsilon=a+b-1$", ylabel=r"Crossing $T_\varepsilon$",
           title="A. Power-law support edge")
    ax.grid(which="major", alpha=.15)
    ax.legend(loc="upper left", frameon=False)
    yy = np.linspace(0, 2.1, 400)
    bx.plot(yy, 1-np.exp(-yy), color=NAVY, label="Exponential limit")
    for eps, color, marker in [("0.02", ORANGE, "o"), ("0.002", "#97658c", "s"),
                               ("0.0001", TEAL, "^")]:
        row = next(r for r in rows if r["b"] == "0.5" and r["epsilon"] == eps)
        checks = row["Y_distribution"]
        bx.plot([float(v["y"]) for v in checks],
                [float(v["positive_mass_cdf"]) for v in checks],
                linestyle="none", marker=marker, ms=4.5,
                mfc="none", color=color, label=r"$\varepsilon=$"+eps)
    bx.set(xlim=(0, 2.12), ylim=(0, 1), xlabel=r"$y=-\varepsilon\log T$",
           ylabel="Normalized positive-mass CDF",
           title=r"B. Exponential mass scale, $b=1/2$")
    bx.grid(alpha=.15)
    bx.legend(loc="lower right", frameon=False)
    finish(fig, "boundary_two_scales")


def moments():
    rows = json.loads((ROOT/"data/moment_numerics.json").read_text())["rows"]
    mp.mp.dps = 40
    c = float(mp.zeta(2)/(2*mp.euler)-mp.euler)
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(6.55, 3.15))
    ss = np.linspace(-1.1, 1.1, 400)
    ax.plot(ss, np.exp(c*np.exp(-ss)), color=NAVY,
            label=r"Limit $\exp(c e^{-s})$")
    for m, color, marker in [(100, ORANGE, "s"), (1000, TEAL, "o")]:
        branch = [r for r in rows if r["m"] == m]
        ax.plot([float(r["t"])-math.log(m) for r in branch],
                [float(r["ratio_y"]) for r in branch], linestyle="none",
                marker=marker, ms=4.6, mfc="none", color=color, label="m = "+str(m))
    ax.set(xlabel=r"$s=n/(m+1)-\log m$", ylabel=r"Normalized moment $\mathcal{R}_{n,m}$",
           title="A. Uniform transition profile")
    ax.grid(alpha=.15)
    ax.legend(frameon=False, loc="upper right")
    center = [r for r in rows if r["s_target"] == 0]
    mm = [r["m"] for r in center]
    for key, label, color, marker in [
            ("leading", "Leading profile", "#697784", "o"),
            ("one_correction", r"Through $C_1/m$", ORANGE, "s"),
            ("two_corrections", r"Through $C_2/m^2$", TEAL, "^")]:
        error = [abs(float(mp.mpf(r["ratio_y"])-mp.mpf(r[key]))) for r in center]
        bx.loglog(mm, error, marker=marker, color=color, ms=4, label=label)
    bx.set(xlabel="m", ylabel="Absolute approximation error",
           title="B. Central transition errors")
    bx.grid(which="major", alpha=.15)
    bx.legend(frameon=False, loc="lower left")
    finish(fig, "moment_transition")


if __name__ == "__main__":
    geometry()
    boundary()
    moments()
    print("Created three PDF figures and three PNG previews from recorded data.")
