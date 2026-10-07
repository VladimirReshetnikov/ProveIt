#!/usr/bin/env python3
"""Reproduce the power-exponent region used in Section 5.

Run from any directory:
    python3 figures/make_parameter_region.py

Requires Python 3 and matplotlib. The output is a vector PDF next to this
script. The figure is computed from the exact boundary vertices; it is
not based on estimates or numerical van der Waerden data.
"""

from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon


def main() -> None:
    # Exact vertices of 0 <= sigma <= a and 2*a + sigma <= 1.
    vertices = (
        (Fraction(0), Fraction(0)),
        (Fraction(1, 2), Fraction(0)),
        (Fraction(1, 3), Fraction(1, 3)),
    )
    endpoint = vertices[2]
    assert endpoint[1] / 8 == Fraction(1, 24)
    for a, sigma in vertices:
        assert 0 <= sigma <= a and 2 * a + sigma <= 1

    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["STIXGeneral", "DejaVu Serif"],
        "mathtext.fontset": "stix",
        "font.size": 11,
        "axes.labelsize": 12,
        "xtick.labelsize": 11,
        "ytick.labelsize": 11,
        "axes.linewidth": 0.7,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
    })

    fig, ax = plt.subplots(figsize=(5.03, 3.75))
    fig.subplots_adjust(left=0.12, right=0.965, bottom=0.13, top=0.95)
    ax.set_xlim(0, 0.55)
    ax.set_ylim(0, 0.445)
    ax.set_aspect("equal", adjustable="box")

    edge = "#264D66"
    fill = "#E2ECF2"
    guides = "#9EA9B0"
    accent = "#9A342A"

    ax.add_patch(Polygon(
        [(float(a), float(sigma)) for a, sigma in vertices],
        closed=True,
        facecolor=fill,
        edgecolor=edge,
        linewidth=1.15,
        joinstyle="miter",
        zorder=2,
    ))
    a_star = sigma_star = float(Fraction(1, 3))
    ax.plot([a_star, a_star], [0, sigma_star], color=guides,
            linewidth=0.65, dashes=(3, 3), zorder=3)
    ax.plot([0, a_star], [sigma_star, sigma_star], color=guides,
            linewidth=0.65, dashes=(3, 3), zorder=1)

    ax.annotate(r"$\sigma=a$", xy=(0.145, 0.145), xytext=(-9, 9),
                textcoords="offset points", rotation=45,
                rotation_mode="anchor", ha="center", va="bottom",
                color=edge)
    ax.annotate(r"$2a+\sigma=1$", xy=(0.43, 0.14), xytext=(13, 6),
                textcoords="offset points", rotation=-63.43494882,
                rotation_mode="anchor", ha="center", va="center",
                color=edge)

    ax.text(0.292, 0.118, "Feasible exponents", ha="center", va="center",
            fontsize=10.5, color="#26343D",
            bbox={"facecolor": fill, "edgecolor": "none", "pad": 1.5})
    ax.text(0.292, 0.084, r"$c<\sigma/8$", ha="center", va="center",
            fontsize=12, color="#26343D",
            bbox={"facecolor": fill, "edgecolor": "none", "pad": 1.5})

    ax.plot(a_star, sigma_star, "o", markersize=4.5, color=accent,
            markeredgecolor="white", markeredgewidth=0.6, zorder=5)
    ax.annotate(r"$a=\sigma=\frac{1}{3}$" + "\n" + r"$c=\frac{1}{24}$",
                xy=(a_star, sigma_star), xytext=(0.37, 0.392),
                ha="center", va="center", fontsize=11, linespacing=1.55,
                arrowprops={"arrowstyle": "-", "color": accent,
                            "linewidth": 0.7, "shrinkA": 3, "shrinkB": 4},
                color=accent)

    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_color("#48525A")
    ax.spines["bottom"].set_color("#48525A")
    ax.tick_params(axis="both", direction="out", length=3, width=0.7,
                   colors="#34414B", pad=4)
    ax.set_xticks([0, 1 / 3, 1 / 2], [r"$0$", r"$\frac{1}{3}$", r"$\frac{1}{2}$"])
    ax.set_yticks([0, 1 / 3], [r"$0$", r"$\frac{1}{3}$"])
    ax.set_xlabel(r"$a$", labelpad=2)
    ax.set_ylabel(r"$\sigma$", rotation=0, labelpad=9)
    ax.xaxis.set_label_coords(1.01, -0.027)
    ax.yaxis.set_label_coords(-0.05, 0.995)

    target = Path(__file__).resolve().with_name("parameter_region.pdf")
    fig.savefig(target, metadata={
        "Title": "Power-exponent parameter region",
        "Subject": "Closed region 0 <= sigma <= a, 2a + sigma <= 1",
        "Creator": "make_parameter_region.py (matplotlib)",
        "CreationDate": None,
        "ModDate": None,
    })
    plt.close(fig)
    print(target)


if __name__ == "__main__":
    main()
