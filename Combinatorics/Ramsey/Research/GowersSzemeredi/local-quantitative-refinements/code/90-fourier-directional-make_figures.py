#!/usr/bin/env python3
"""Render the article's publication figures from its proved formulas.

Dependencies: Python 3, NumPy, SciPy, Matplotlib.
Run from any directory: python path/to/code/make_figures.py

The script is self-contained and reads no other program or data file.
It evaluates formulas for illustration; the figures are not numerical proofs.
"""

import argparse
import json
from math import acos, cos, pi, sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
import numpy as np
from scipy.optimize import brentq


C_MINUS = (1.0 - sqrt(5.0)) / 4.0
V_SEMICIRCLE = -sqrt(3.0) / 2.0
RHO_ZERO = (sqrt(3.0) - 1.0) / 2.0
GRID_LIMIT = 2.0 * pi**2 * (2.0 * sqrt(3.0) - 3.0) / 9.0


def switch_polynomial(c):
    return -1.0 + 5.0*c + 11.0*c*c - 6.0*c**3 - 12.0*c**4


C_STAR = brentq(switch_polynomial, 0.0, 1.0/6.0, xtol=1e-15, rtol=1e-14)
A_STAR = acos(C_STAR)


def branch_polynomial(c, v):
    leading = 4.0 * (1.0-c) * (1.0+2.0*c)
    return (leading*v**3 + leading*c*v*v
            + (1.0+c)*(4.0*c*c-3.0)*v + c*(4.0*c*c-3.0))


def branch_node(c):
    """The unique scalar cubic root on the interval proved in the article."""
    # The exact endpoint/root identities avoid signed-zero bracket artifacts.
    if abs(c - C_MINUS) <= 4e-14:
        return -1.0
    if abs(c) <= 4e-14:
        return V_SEMICIRCLE
    if not C_MINUS - 5e-14 <= c <= C_STAR + 5e-14:
        raise ValueError("Cosine coordinate is outside the algebraic branch")
    return brentq(lambda v: branch_polynomial(c, v), -1.0, V_SEMICIRCLE,
                  xtol=1e-15, rtol=1e-14)


def branch_data(a):
    c = cos(a)
    v = branch_node(c)
    rho = (1.0 + 2.0*c*v) / (1.0 - 2.0*c - 2.0*v)
    mass = (-rho-v) / (c-v)
    third = mass*(4.0*c**3 - 3.0*c) + (1.0-mass)*(4.0*v**3 - 3.0*v)
    return rho, third, v, mass


def piece_value(piece, a):
    c = cos(a)
    if piece == 0:
        return 0.0
    if piece == 1:
        return (1.0+2.0*c-4.0*c*c) / (3.0+10.0*c-12.0*c*c)
    if piece == 2:
        return (1.0-2.0*c*c) / (3.0+2.0*c-4.0*c*c)
    if piece == 3:
        return branch_data(a)[0]
    if piece == 4:
        return 2.0*c*(c-1.0) / (2.0*c*c-2.0*c+1.0)
    if piece == 5:
        b = pi-a
        z, w = cos(b), cos(4.0*b)
        return (z-w) / (2.0-z-w)
    if piece == 6:
        return -c
    raise ValueError("Expected a piece index between zero and six")


def semicircle_scaled_gap(n):
    """Evaluate the exact adjacent-node formula without subtractive loss."""
    if n < 8 or n % 4:
        raise ValueError("Expected an aligned modulus N >= 8 divisible by four")
    if n % 12 == 0:
        # This is an exact theorem identity, not a rounding-to-zero rule.
        return 0.0
    j = (5*n) // 12
    r = cos(2.0*pi*(j+1)/n)
    s = cos(2.0*pi*j/n)
    numerator = 4.0*(r*r+r*s+s*s)-3.0
    direct_value = numerator / (numerator - 8.0*r*s*(r+s))
    q1 = r*s*(r+s)
    q2 = (1.0-r*r-r*s-s*s)/2.0
    normalizer = -q1-q2+1.0/8.0
    v, p = V_SEMICIRCLE, 1.0/sqrt(3.0)
    gap = ((1.0-p)*(-v)*(-r-s-v)/normalizer
           * (v-r)*(s-v))
    # Independent forms of the same exact formula should agree at plot precision.
    if abs((RHO_ZERO+gap)-direct_value) > 2e-12:
        raise ArithmeticError("Adjacent-node and gap formulas disagree")
    if gap <= 0.0:
        raise ArithmeticError("A nonzero residue class must have a positive gap")
    return n*n*gap


def publication_style():
    plt.rcParams.update({
        "font.family": "STIXGeneral",
        "font.size": 10.5,
        "mathtext.fontset": "stix",
        "axes.titlesize": 11.5,
        "axes.labelsize": 11.0,
        "xtick.labelsize": 10.0,
        "ytick.labelsize": 10.0,
        "legend.fontsize": 10.0,
        "axes.linewidth": 0.7,
        "axes.edgecolor": "#56616b",
        "axes.spines.top": False,
        "axes.spines.right": False,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "xtick.major.width": 0.65,
        "ytick.major.width": 0.65,
        "grid.color": "#d7dde2",
        "grid.linewidth": 0.55,
        "grid.alpha": 0.8,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
    })


def save_figure(fig, directory, stem, dpi):
    pdf = directory / f"{stem}.pdf"
    png = directory / f"{stem}.png"
    fig.savefig(pdf, metadata={"Title": stem.replace("_", " "),
                             "Author": "Research article companion",
                             "CreationDate": None, "ModDate": None})
    fig.savefig(png, dpi=dpi)
    plt.close(fig)
    return [str(pdf), str(png)]


def frontier_figure(directory, dpi):
    bounds = [0.0, pi/5.0, 2.0*pi/5.0, A_STAR,
              3.0*pi/5.0, 5.0*pi/7.0, 4.0*pi/5.0, pi]
    for i in range(1, 7):
        if abs(piece_value(i-1, bounds[i])-piece_value(i, bounds[i])) > 2e-11:
            raise ArithmeticError(f"Frontier pieces fail to meet at junction {i}")

    fig, axes = plt.subplots(2, 1, figsize=(6.1, 6.5),
                             gridspec_kw={"height_ratios": [1.02, 1.0]})
    fig.subplots_adjust(left=0.12, right=0.975, bottom=0.085,
                        top=0.95, hspace=0.44)
    upper, lower = axes
    blue, teal, orange = "#1f4b79", "#147d80", "#bd5b26"

    upper.set_title("A. The complete four-frequency frontier", loc="left", pad=9)
    upper.axvspan(A_STAR/pi, 3.0/5.0, facecolor="#e5f2f1", zorder=0)
    for a in bounds[1:-1]:
        upper.axvline(a/pi, color="#b7c1c9", linewidth=0.7,
                      linestyle=(0, (2, 3)), zorder=1)
    for piece in range(7):
        angles = np.linspace(bounds[piece], bounds[piece+1], 180)
        values = np.array([piece_value(piece, float(a)) for a in angles])
        upper.plot(angles/pi, values, color=teal if piece == 3 else blue,
                   linewidth=2.25 if piece == 3 else 1.85, zorder=3)
        midpoint = (bounds[piece]+bounds[piece+1])/(2.0*pi)
        upper.text(midpoint, 0.965, ["I", "II", "III", "IV", "V", "VI", "VII"][piece],
                   transform=upper.get_xaxis_transform(), ha="center", va="top",
                   fontsize=9.5, color=teal if piece == 3 else "#65717a")
    transitions = [(a/pi, piece_value(i, a)) for i, a in enumerate(bounds[1:-1])]
    upper.scatter([p[0] for p in transitions], [p[1] for p in transitions],
                  s=15, facecolor="white", edgecolor=blue, linewidth=0.9, zorder=4)
    upper.annotate(r"$a_*$", xy=(A_STAR/pi, branch_data(A_STAR)[0]),
                   xytext=(-16, 30), textcoords="offset points", ha="right",
                   fontsize=11, color=teal,
                   arrowprops={"arrowstyle": "-", "color": teal,
                               "linewidth": 0.85, "shrinkA": 3, "shrinkB": 4})
    upper.set_xlim(0, 1)
    upper.set_ylim(-0.035, 1.115)
    upper.set_xticks([0, 1/5, 2/5, 3/5, 5/7, 4/5, 1],
                     ["0", r"$1/5$", r"$2/5$", r"$3/5$",
                      r"$5/7$", r"$4/5$", "1"])
    upper.set_yticks([0, 0.25, 0.5, 0.75, 1])
    upper.set_xlabel(r"Excluded half-width $a/\pi$")
    upper.set_ylabel(r"$\Phi_4(a)$")
    upper.grid(axis="y")

    angles = np.linspace(A_STAR, 3.0*pi/5.0, 401)
    rows = np.array([branch_data(float(a)) for a in angles])
    rho, third = rows[:, 0], rows[:, 1]
    if np.any(np.abs(third) > rho + 2e-11):
        raise ArithmeticError("Third moment is outside its proved active bounds")
    lower.set_title("B. Moment switching on the algebraic branch (IV)", loc="left", pad=9)
    lower.fill_between(angles/pi, -rho, rho, facecolor="#f0f3f5", zorder=0)
    lower.axhline(0, color="#bcc6ce", linewidth=0.7, zorder=1)
    lower.plot(angles/pi, -rho, color=blue, linewidth=1.9,
               label=r"$m_1=m_2=-\rho$")
    lower.plot(angles/pi, third, color=orange, linewidth=2.1,
               label=r"$m_3$")
    lower.plot(angles/pi, rho, color=teal, linewidth=1.9,
               label=r"$m_4=\rho$")
    lower.scatter([angles[0]/pi, angles[-1]/pi], [third[0], third[-1]],
                  s=27, facecolor="white", edgecolor=orange, linewidth=1.15, zorder=5)
    lower.set_xlim(A_STAR/pi-0.003, 0.603)
    lower.set_ylim(-0.49, 0.51)
    lower.set_xticks([A_STAR/pi, 0.5, 0.55, 0.6],
                     [r"$a_*/\pi$", r"$1/2$", r"$11/20$", r"$3/5$"])
    lower.set_yticks([-0.4, -0.2, 0.0, 0.2, 0.4])
    lower.set_xlabel(r"Excluded half-width $a/\pi$")
    lower.set_ylabel(r"Real Fourier moment $m_j$")
    lower.grid(axis="y")
    for x, sign, text, color, offset in [
        (0.478, -1, r"$m_1=m_2=-\rho$", blue, (5, -14)),
        (0.508, 1, r"$m_4=\rho$", teal, (6, 12)),
    ]:
        value = sign*branch_data(x*pi)[0]
        lower.annotate(text, xy=(x, value), xytext=offset,
                       textcoords="offset points", fontsize=10.8, color=color,
                       ha="left", va="center")
    x = 0.55
    lower.annotate(r"$m_3$", xy=(x, branch_data(x*pi)[1]),
                   xytext=(5, -17), textcoords="offset points",
                   fontsize=10.8, color=orange, ha="left", va="center")
    return save_figure(fig, directory, "fourier_frontier", dpi)


def grid_figure(directory, dpi, max_modulus):
    fig, axis = plt.subplots(figsize=(6.1, 3.85))
    fig.subplots_adjust(left=0.12, right=0.975, bottom=0.16, top=0.87)
    axis.set_title("Aligned semicircle grids: the exact finite correction", loc="left", pad=12)
    colors = {0: "#525c65", 4: "#147d80", 8: "#bd5b26"}
    markers = {0: "o", 4: "^", 8: "s"}
    for residue in [4, 8, 0]:
        moduli = [n for n in range(8, max_modulus+1, 4) if n % 12 == residue]
        values = [semicircle_scaled_gap(n) for n in moduli]
        axis.plot(moduli, values, color=colors[residue], marker=markers[residue],
                  markersize=4.3, linewidth=1.1, markerfacecolor="white",
                  markeredgewidth=0.95, label=rf"$N\equiv {residue}$ (mod 12)",
                  zorder=3)
    axis.axhline(GRID_LIMIT, color="#77648c", linewidth=1.1,
                 linestyle=(0, (4, 3)), zorder=1)
    axis.text(max_modulus-1, GRID_LIMIT-0.055,
              r"$2\pi^2(2\sqrt{3}-3)/9$", ha="right", va="top",
              fontsize=10.5, color="#655178")
    zero_label_x = min(90, max_modulus*0.60)
    axis.annotate(r"Exact equality: $12\mid N$", xy=(zero_label_x, 0.0),
                  xytext=(zero_label_x, 0.18), ha="center", va="bottom",
                  color=colors[0], fontsize=10.5,
                  arrowprops={"arrowstyle": "-", "color": colors[0],
                              "linewidth": 0.75, "shrinkA": 4, "shrinkB": 5})
    axis.set_xlim(4, max_modulus+4)
    axis.set_ylim(-0.065, 1.42)
    axis.set_xlabel(r"Modulus $N$ ($4\mid N$)")
    axis.set_ylabel(r"$N^2[\Phi_{4,N}(\pi/2)-\rho_0]$")
    locator = MaxNLocator(nbins=5, integer=True)
    ticks = [8] + [int(t) for t in locator.tick_values(8, max_modulus)
                    if 16 <= t <= max_modulus]
    axis.set_xticks(sorted(set(ticks)))
    axis.set_yticks([0.0, 0.4, 0.8, 1.2])
    axis.grid(axis="y")
    axis.legend(loc="upper right", ncol=1, frameon=False,
                borderaxespad=0.25, labelspacing=0.35, handlelength=2.0)
    return save_figure(fig, directory, "semicircle_grid", dpi)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "figures")
    parser.add_argument("--max-modulus", type=int, default=160)
    parser.add_argument("--dpi", type=int, default=220)
    args = parser.parse_args()
    if args.max_modulus < 24 or args.dpi < 72:
        parser.error("Use --max-modulus >= 24 and --dpi >= 72")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    publication_style()
    output = frontier_figure(args.output_dir, args.dpi)
    output += grid_figure(args.output_dir, args.dpi, args.max_modulus)
    print(json.dumps({"files": output, "c_star": C_STAR,
                      "a_star_over_pi": A_STAR/pi, "rho_zero": RHO_ZERO,
                      "nonzero_residue_limit": GRID_LIMIT,
                      "scope": "Illustrations of proved formulas; not numerical proofs"},
                     indent=2))


if __name__ == "__main__":
    main()
