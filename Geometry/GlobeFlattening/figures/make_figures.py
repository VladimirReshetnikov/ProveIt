#!/usr/bin/env python3
"""Reproduce the two vector illustrations for the verification report.

Requires Python 3 and Matplotlib. Run from any directory:
    python3 make_figures.py

The Cantor staircase is a finite, eight-stage piecewise-linear illustration.
The limiting staircase, not its finite approximants, has derivative zero
almost everywhere. All output artwork is vector PDF.
"""

from pathlib import Path
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch, Rectangle


HERE = Path(__file__).resolve().parent
NAVY = "#17324D"
TEAL = "#187F86"
ORANGE = "#D58A34"
LIGHT_TEAL = "#DCEFF0"
LIGHT_ORANGE = "#F8E6CB"
LIGHT_BLUE = "#E4EAF0"
GRID = "#D8E0E6"

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 8.6,
    "axes.titlesize": 10.0,
    "axes.labelsize": 8.8,
    "axes.titleweight": "semibold",
    "axes.labelcolor": NAVY,
    "axes.edgecolor": NAVY,
    "text.color": NAVY,
    "xtick.color": NAVY,
    "ytick.color": NAVY,
    "xtick.labelsize": 8.0,
    "ytick.labelsize": 8.0,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "savefig.facecolor": "white",
})


def cantor_vertices(stages=8):
    """Exact breakpoints of the standard piecewise-linear approximant."""
    segments = [(0.0, 0.0, 1.0, 1.0)]
    for _ in range(stages):
        refined = []
        for x0, y0, x1, y1 in segments:
            if y0 == y1:
                refined.append((x0, y0, x1, y1))
                continue
            a = x0 + (x1 - x0) / 3
            b = x0 + 2 * (x1 - x0) / 3
            c = (y0 + y1) / 2
            refined.extend([
                (x0, y0, a, c),
                (a, c, b, c),
                (b, c, x1, y1),
            ])
        segments = refined
    xs = [segments[0][0]] + [s[2] for s in segments]
    ys = [segments[0][1]] + [s[3] for s in segments]
    return xs, ys


def style_axis(ax):
    ax.set_axisbelow(True)
    ax.grid(color=GRID, lw=0.55, alpha=0.8)
    ax.tick_params(length=3, width=0.7)
    for spine in ax.spines.values():
        spine.set_linewidth(0.7)


def singular_staircase():
    xs, ys = cantor_vertices(8)
    fig, axes = plt.subplots(1, 2, figsize=(6.3, 3.25))
    fig.subplots_adjust(left=0.085, right=0.98, bottom=0.26,
                        top=0.85, wspace=0.37)
    ax = axes[0]
    ax.plot(xs, ys, color=TEAL, lw=1.65)
    ax.set_title(r"Cantor staircase $C_8(t)$", pad=9)
    ax.set(xlim=(0, 1), ylim=(0, 1.025), xlabel=r"$t$")
    ax.set_xticks([0, 0.5, 1])
    ax.set_yticks([0, 0.5, 1])
    ax.text(0.53, 0.40, "Flat middle third", fontsize=8.1)
    ax.annotate("", xy=(0.51, 0.5), xytext=(0.69, 0.47),
                arrowprops={"arrowstyle": "-", "color": NAVY, "lw": 0.7})
    style_axis(ax)

    ax = axes[1]
    ax.plot([0, 1], [0, 1], color=NAVY, ls=(0, (4, 3)), lw=1.1,
            label=r"Identity $t$")
    ax.plot(xs, [x + 0.25 * y for x, y in zip(xs, ys)],
            color=ORANGE, lw=1.65, label=r"$f_8(t)$")
    ax.set_title(r"$f_8(t)=t+0.25\,C_8(t)$", pad=9)
    ax.set(xlim=(0, 1), ylim=(0, 1.29), xlabel=r"$t$")
    ax.set_xticks([0, 0.5, 1])
    ax.set_yticks([0, 0.5, 1, 1.25])
    ax.legend(loc="upper left", frameon=False, fontsize=8.0,
              handlelength=2.0, borderaxespad=0.5)
    style_axis(ax)

    fig.text(0.5, 0.105,
             "Illustration: eight stages of a finite piecewise-linear approximation.",
             ha="center", fontsize=8.1)
    fig.text(0.5, 0.054,
             "Only the limiting staircase has derivative zero almost everywhere.",
             ha="center", fontsize=8.1)
    fig.savefig(HERE / "singular_staircase.pdf")
    plt.close(fig)


def refinement_stage():
    theta = 1 / 16
    rho = theta
    endpoint = 1.15
    fig, axes = plt.subplots(1, 2, figsize=(6.3, 3.7))
    fig.subplots_adjust(left=0.08, right=0.98, bottom=0.32,
                        top=0.86, wspace=0.38)

    ax = axes[0]
    ax.set_title(r"One grid cell ($\theta=1/16$)", pad=13)
    ax.add_patch(Rectangle((0, 0), 1, 1, facecolor="white",
                           edgecolor=NAVY, lw=0.9))
    ax.add_patch(Rectangle((0, theta), 1 - theta, 1 - 2 * theta,
                           facecolor=LIGHT_TEAL, edgecolor="none"))
    ax.add_patch(Rectangle((1 - theta, 0), theta, 1,
                           facecolor=LIGHT_ORANGE, edgecolor="none"))
    for y in (0, 1 - theta):
        ax.add_patch(Rectangle((0, y), 1, theta,
                               facecolor=LIGHT_BLUE, edgecolor="none"))
    ax.add_patch(Rectangle((rho, theta + rho),
                           1 - theta - 2 * rho, 1 - 2 * theta - 2 * rho,
                           facecolor="none", edgecolor=TEAL, lw=1.25,
                           linestyle=(0, (4, 2))))
    ax.plot([1 - theta, 1 - theta], [theta, 1 - theta],
            color=ORANGE, lw=0.8)
    ax.text(0.45, 0.72, "Affine tile", ha="center", fontsize=9.1)
    ax.text(0.45, 0.47, "Deep interior", ha="center", fontsize=9.1,
            color=TEAL, fontweight="semibold")
    ax.text(0.45, 0.35, r"distance $\geq\rho=\theta$", ha="center",
            fontsize=8.4, color=TEAL)
    ax.annotate("", xy=(0.96875, 0.58), xytext=(0.79, 0.58),
                arrowprops={"arrowstyle": "->", "color": ORANGE,
                            "lw": 0.9, "mutation_scale": 7})
    ax.set(xlim=(-0.02, 1.02), ylim=(-0.02, 1.02),
           xlabel="Longitude (normalized)", ylabel="Latitude (normalized)")
    ax.set_xticks([0, 1])
    ax.set_yticks([0, 1])
    ax.set_aspect("equal")
    ax.tick_params(length=3, width=0.7)
    ax.spines["left"].set_visible(False)
    ax.spines["bottom"].set_visible(False)

    ax = axes[1]
    ax.set_title("One longitude period", pad=13)
    ax.plot([0, 1], [0, endpoint], color=NAVY,
            ls=(0, (4, 3)), lw=1.2, label=r"Old profile $P(t)=1.15t$")
    ax.plot([0, 1 - theta], [0, 1 - theta],
            color=TEAL, lw=1.7, label=r"New profile $Q(t)$")
    ax.plot([1 - theta, 1], [1 - theta, endpoint],
            color=ORANGE, lw=1.9)
    ax.plot([1 - theta, 1 - theta], [0, 1 - theta],
            color=GRID, ls=(0, (2, 2)), lw=0.8, zorder=0)
    ax.scatter([0, 1], [0, endpoint], color=NAVY, s=12, zorder=5)
    ax.text(0.46, 0.30, r"Slope $b=1$", color=TEAL, fontsize=8.5)
    ax.annotate("Catch-up", xy=(0.978, 1.075), xytext=(0.71, 1.065),
                ha="center", va="center", fontsize=8.0, color=ORANGE,
                arrowprops={"arrowstyle": "-", "color": ORANGE, "lw": 0.7})
    ax.set(xlim=(-0.02, 1.03), ylim=(-0.02, 1.3),
           xlabel=r"$t$", ylabel="Profile value")
    ax.set_xticks([0, 0.5, 1])
    ax.set_yticks([0, 0.5, 1])
    ax.legend(loc="upper left", bbox_to_anchor=(-0.01, 1.015),
              frameon=False, fontsize=7.6, handlelength=1.65,
              borderaxespad=0.2, labelspacing=0.5)
    style_axis(ax)

    legend_handles = [
        Patch(facecolor=LIGHT_BLUE, edgecolor="none",
              label="Latitude interpolation layers"),
        Patch(facecolor=LIGHT_ORANGE, edgecolor="none",
              label="Longitude catch-up strip"),
        Line2D([0], [0], color=TEAL, lw=1.25, ls=(0, (4, 2)),
               label="Trimmed tile interior"),
    ]
    fig.legend(handles=legend_handles, loc="lower center",
               bbox_to_anchor=(0.5, 0.025), ncol=1, frameon=False,
               fontsize=8.0, handlelength=2.2, labelspacing=0.45)
    fig.savefig(HERE / "refinement_stage.pdf")
    plt.close(fig)


if __name__ == "__main__":
    singular_staircase()
    refinement_stage()
    print(HERE / "singular_staircase.pdf")
    print(HERE / "refinement_stage.pdf")
