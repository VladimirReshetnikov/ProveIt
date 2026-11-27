"""Draw the fully resonant two-frequency example used in the paper.

Run with Python 3, NumPy, and Matplotlib. The only output is resonant-model.pdf
next to this script. In the second panel, n ranges over consecutive integers,
so the plotted phases involve no random-number generator.
"""

from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def curve(t):
    return np.cos(t), np.cos(2 * t)


def support_edges(x):
    lower = x**2 - 2
    upper = lower + (2 - np.abs(x))**2
    return lower, upper


def main():
    n = np.arange(1, 12001, dtype=float)
    first_x, first_y = curve(n ** (4 / 3))
    second_x, second_y = curve(n ** (5 / 3))
    pooled_x = first_x + second_x
    pooled_y = first_y + second_y
    lower, upper = support_edges(pooled_x)
    assert np.all(lower - 1e-12 <= pooled_y)
    assert np.all(pooled_y <= upper + 1e-12)

    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 8.5,
        "mathtext.fontset": "stix",
        "pdf.fonttype": 42,
        "axes.linewidth": 0.55,
        "axes.labelcolor": "#202c34",
        "xtick.color": "#39474f",
        "ytick.color": "#39474f",
    })
    fig, axes = plt.subplots(1, 2, figsize=(6.2, 3.05))
    fig.subplots_adjust(left=0.085, right=0.985, bottom=0.18, top=0.83, wspace=0.31)
    outline = "#203e4d"
    points = "#417e85"
    for ax in axes:
        ax.spines[["top", "right"]].set_visible(False)
        ax.spines[["left", "bottom"]].set_color("#687781")
        ax.tick_params(length=3, width=0.55, pad=3)
        ax.set_box_aspect(0.86)
        ax.set_xlabel("$X$", labelpad=1.5)
        ax.set_ylabel("$Y$", labelpad=1)
        ax.set_axisbelow(True)
        ax.grid(color="#dce1e3", linewidth=0.4)

    ax = axes[0]
    x = np.linspace(-1, 1, 601)
    ax.plot(x, 2 * x**2 - 1, linewidth=1.7, color=outline)
    ax.text(0, 0.56, "$Y=2X^2-1$", ha="center", color=outline, fontsize=10.5)
    ax.set(xlim=(-1.08, 1.08), ylim=(-1.12, 1.12),
           xticks=(-1, 0, 1), yticks=(-1, 0, 1))
    ax.set_title("One scale", loc="left", weight="bold", color=outline, fontsize=10, pad=21)
    ax.text(0, 1.035, r"$F(t)=(\cos t,\,\cos 2t)$",
            transform=ax.transAxes, va="bottom", color=outline, fontsize=9.5)

    ax = axes[1]
    x = np.linspace(-2, 2, 801)
    lower, upper = support_edges(x)
    ax.scatter(pooled_x, pooled_y, s=0.9, alpha=0.65, color=points,
               edgecolors="none", rasterized=True)
    ax.plot(x, lower, color=outline, linewidth=1.1)
    ax.plot(x, upper, color=outline, linewidth=1.1)
    ax.set(xlim=(-2.16, 2.16), ylim=(-2.22, 2.22),
           xticks=(-2, -1, 0, 1, 2), yticks=(-2, -1, 0, 1, 2))
    ax.set_title("Two deterministic scales", loc="left", weight="bold",
                 color=outline, fontsize=10, pad=21)
    ax.text(0, 1.035, r"$F(n^{4/3})+F(n^{5/3}),\quad 1\leq n\leq 12\,000$",
            transform=ax.transAxes, va="bottom", color=outline, fontsize=9.5)

    fig.savefig(Path(__file__).with_name("resonant-model.pdf"), dpi=360,
                metadata={"Title": "A fully resonant model at one and two scales",
                          "CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
