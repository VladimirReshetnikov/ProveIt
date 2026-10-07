#!/usr/bin/env python3
"""Regenerate publication figures by evaluating the proved exact formulas."""
from pathlib import Path
import csv
import math

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from verification.fourier_verify import A_STAR, phi4_solution, allr_solution

ROOT = Path(__file__).resolve().parent
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
FIGURES.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9,
    "axes.labelsize": 10, "axes.titlesize": 10,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.edgecolor": "#637684", "axes.labelcolor": "#15374B",
    "xtick.color": "#405464", "ytick.color": "#405464",
    "text.color": "#15374B", "grid.color": "#DCE5EA",
    "grid.linewidth": .6, "legend.frameon": False,
    "pdf.fonttype": 42, "ps.fonttype": 42,
})


def phi3(a):
    if a <= math.pi / 4:
        return 0.
    if a <= math.pi / 2:
        c = math.cos(a)
        return (1 - 2*c*c) / (3 + 2*c - 4*c*c)
    return allr_solution(3, a)["rho"]


def profiles():
    aa = np.unique(np.concatenate((np.linspace(0, math.pi, 1601),
          [math.pi/5, 2*math.pi/5, A_STAR, math.pi/2,
           3*math.pi/5, 5*math.pi/7, 4*math.pi/5])))
    yy4 = np.array([phi4_solution(float(a))["rho"] for a in aa])
    yy3 = np.array([phi3(float(a)) for a in aa])
    with (DATA / "fourier_profile_values.csv").open("w", newline="") as fp:
        writer = csv.writer(fp)
        writer.writerow(["a_over_pi", "Phi4", "Phi3"])
        writer.writerows(zip(aa/math.pi, yy4, yy3))

    fig, axs = plt.subplots(1, 2, figsize=(6.25, 3.55),
                            gridspec_kw={"width_ratios": [1.16, 1]},
                            layout="constrained")
    for ax in axs:
        ax.axvspan(A_STAR/math.pi, .6, color="#DEF0EB", zorder=0)
        ax.plot(aa/math.pi, yy4, color="#126E83", lw=1.9,
                label=r"$\Phi_4$ (complete formula)")
        ax.plot(aa/math.pi, yy3, color="#C7793D", lw=1.5, ls="--",
                label=r"$\Phi_3$ (earlier profile)")
        ax.set_xlabel(r"Forbidden half-angle $a/\pi$")
        ax.grid(True, alpha=.8)
    axs[0].set(xlim=(0, 1), ylim=(-.015, 1.025),
               ylabel="Guaranteed normalized moment")
    axs[0].set_title("A. All radii", loc="left", fontweight="bold")
    axs[0].set_xticks([0, .2, .4, .6, .8, 1.])
    axs[0].legend(loc="upper left", fontsize=7.6)
    axs[1].set(xlim=(.4, .625), ylim=(.238, .49))
    axs[1].set_title("B. Central branch detail", loc="left", fontweight="bold")
    axs[1].set_xticks([.4, .45, .5, .55, .6])
    axs[1].axvline(A_STAR/math.pi, color="#75938C", lw=.8, ls=":")
    axs[1].annotate(r"$a_*/\pi$", xy=(A_STAR/math.pi, .257),
                     xytext=(.467, .254), fontsize=8,
                     arrowprops={"arrowstyle": "-", "lw": .7,
                                 "color": "#75938C"})
    axs[1].plot([.5], [(math.sqrt(3)-1)/2], "o", color="#126E83", ms=3.5)
    axs[1].annotate(r"$(\sqrt{3}-1)/2$", (.5, (math.sqrt(3)-1)/2),
                     xytext=(.412, .415), fontsize=8,
                     arrowprops={"arrowstyle": "-", "lw": .7,
                                 "color": "#126E83"})
    fig.savefig(FIGURES / "fourier_profiles.pdf", bbox_inches="tight")
    fig.savefig(FIGURES / "fourier_profiles.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


def grid_value(n):
    rho = (math.sqrt(3)-1)/2
    if n % 12 == 0:
        return rho
    k = 5*n/12
    u = math.cos(2*math.pi*math.ceil(k)/n)
    v = math.cos(2*math.pi*math.floor(k)/n)
    s, p = u+v, u*v
    t = (4*s*s-4*p-3)/8
    return t/(t-s*p)


def grid():
    nn = list(range(8, 513, 4))
    rho = (math.sqrt(3)-1)/2
    vals = [(n, n % 12, grid_value(n), n*n*(grid_value(n)-rho)) for n in nn]
    with (DATA / "half_circle_grid_values.csv").open("w", newline="") as fp:
        writer = csv.writer(fp)
        writer.writerow(["N", "N_mod_12", "Phi4_N", "N_squared_error"])
        writer.writerows(vals)
    fig, ax = plt.subplots(figsize=(6.25, 3.15), layout="constrained")
    colors = {0: "#70818B", 4: "#126E83", 8: "#C7793D"}
    markers = {0: ".", 4: "o", 8: "s"}
    for residue in [4, 8, 0]:
        selected = [v for v in vals if v[1] == residue and v[0] >= 20]
        ax.plot([v[0] for v in selected], [v[3] for v in selected],
                marker=markers[residue], ms=3, lw=.7, color=colors[residue],
                label=rf"$N\equiv {residue}\ (\mathrm{{mod}}\ 12)$")
    limit = 2*math.pi**2*(2*math.sqrt(3)-3)/9
    ax.axhline(limit, color="#75938C", ls="--", lw=1,
               label=r"Limit $2\pi^2(2\sqrt{3}-3)/9$")
    ax.set(xlim=(14, 516), ylim=(-.06, 1.23), xlabel="Cyclic group order $N$",
           ylabel=r"$N^2[\Phi_{4,N}(\pi/2)-\Phi_4(\pi/2)]$")
    ax.grid(True, alpha=.8)
    ax.legend(loc="center right", fontsize=8.1)
    fig.savefig(FIGURES / "grid_correction.pdf", bbox_inches="tight")
    fig.savefig(FIGURES / "grid_correction.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    profiles()
    grid()
    print("Generated two vector figures and their CSV data.")
