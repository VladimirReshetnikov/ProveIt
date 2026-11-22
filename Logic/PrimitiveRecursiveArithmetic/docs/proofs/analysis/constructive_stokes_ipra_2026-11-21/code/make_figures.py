#!/usr/bin/env python3
"""Generate the report's two vector figures.

Requirements: Python 3 and matplotlib (with its usual dependencies).
Run from any directory; outputs default to ../report/figures relative to here.
No stochastic sampling, external data, or TeX executable is used.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch, Rectangle
from mpl_toolkits.mplot3d.art3d import Poly3DCollection


NAVY = "#193F55"
TEAL = "#438E87"
GRID = "#BDC9CE"
INK = "#263B47"


def configure() -> None:
    plt.rcParams.update(
        {
            "font.family": "DejaVu Serif",
            "font.size": 10,
            "mathtext.fontset": "stix",
            "axes.labelcolor": INK,
            "text.color": INK,
            "xtick.color": INK,
            "ytick.color": INK,
            "axes.edgecolor": "#80919A",
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
            "savefig.facecolor": "white",
        }
    )


def export(fig: plt.Figure, directory: Path, name: str, title: str) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    fig.savefig(
        directory / f"{name}.pdf",
        bbox_inches="tight",
        pad_inches=0.08,
        metadata={
            "Title": title,
            "Creator": "Constructive Stokes research package; make_figures.py",
            "CreationDate": None,
            "ModDate": None,
        },
    )
    fig.savefig(
        directory / f"{name}.png",
        bbox_inches="tight",
        pad_inches=0.08,
        dpi=220,
    )
    plt.close(fig)


def arrow(ax, start, end, *, color, width, size, zorder=3):
    ax.add_patch(
        FancyArrowPatch(
            start,
            end,
            arrowstyle="-|>",
            mutation_scale=size,
            linewidth=width,
            color=color,
            shrinkA=0,
            shrinkB=0,
            zorder=zorder,
        )
    )


def grid_cancellation(directory: Path) -> None:
    fig, ax = plt.subplots(figsize=(5.6, 5.1))
    fig.subplots_adjust(left=0.08, right=0.93, bottom=0.14, top=0.9)
    ax.set_aspect("equal")
    ax.set_xlim(-0.14, 1.14)
    ax.set_ylim(-0.14, 1.14)
    ax.axis("off")

    ax.add_patch(Rectangle((0, 0), 1, 1, facecolor="#F7FAFA", edgecolor="none"))
    ax.plot([0.5, 0.5], [0, 1], color=GRID, lw=0.9, ls=(0, (3, 3)))
    ax.plot([0, 1], [0.5, 0.5], color=GRID, lw=0.9, ls=(0, (3, 3)))

    # Each small square has its own counterclockwise orientation.  The slight
    # insets expose the two opposite copies of each shared edge distinctly.
    inset, short = 0.035, 0.085
    for left in (0.0, 0.5):
        for bottom in (0.0, 0.5):
            right, top = left + 0.5, bottom + 0.5
            segments = (
                ((left + short, bottom + inset), (right - short, bottom + inset)),
                ((right - inset, bottom + short), (right - inset, top - short)),
                ((right - short, top - inset), (left + short, top - inset)),
                ((left + inset, top - short), (left + inset, bottom + short)),
            )
            for start, end in segments:
                arrow(ax, start, end, color=TEAL, width=1.4, size=10)

    # The surviving outer orientation is counterclockwise.
    ax.plot([0, 1, 1, 0, 0], [0, 0, 1, 1, 0], color=NAVY, lw=2.1, zorder=4)
    for start, end in (
        ((0.27, 0), (0.73, 0)),
        ((1, 0.27), (1, 0.73)),
        ((0.73, 1), (0.27, 1)),
        ((0, 0.73), (0, 0.27)),
    ):
        arrow(ax, start, end, color=NAVY, width=2.1, size=13, zorder=5)

    ax.text(0.5, -0.08, r"$+\,du$", ha="center", va="center", fontsize=12)
    ax.text(1.075, 0.5, r"$+\,dv$", ha="center", va="center", fontsize=12)
    ax.text(0.5, 1.075, r"$-\,du$", ha="center", va="center", fontsize=12)
    ax.text(-0.075, 0.5, r"$-\,dv$", ha="center", va="center", fontsize=12)
    ax.text(1.075, -0.035, r"$u$", ha="center", va="center", fontsize=13)
    ax.text(-0.035, 1.075, r"$v$", ha="center", va="center", fontsize=13)

    ax.set_title("Opposite interior orientations cancel", fontsize=12, pad=13)
    fig.legend(
        handles=(
            Line2D([0], [0], color=TEAL, lw=1.4, label="Individual cell boundaries"),
            Line2D([0], [0], color=NAVY, lw=2.1, label="Surviving outer boundary"),
        ),
        loc="lower center",
        ncol=1,
        frameon=False,
        fontsize=9,
        bbox_to_anchor=(0.51, 0.015),
        handlelength=2.5,
    )
    export(fig, directory, "grid_cancellation", "Oriented cubical face cancellation")


def volume_sum(n: int) -> Fraction:
    return Fraction((n - 1) ** 2 * (8 * n - 1), 12 * n**3)


def boundary_sum(n: int) -> Fraction:
    return Fraction((n - 1) * (4 * n + 1), 6 * n**2)


def example_convergence(directory: Path) -> None:
    fig = plt.figure(figsize=(9.0, 3.75))
    gs = fig.add_gridspec(
        1, 2, width_ratios=(1.0, 1.48), left=0.015, right=0.985,
        top=0.88, bottom=0.2, wspace=0.29,
    )
    ax3d = fig.add_subplot(gs[0, 0], projection="3d")
    ax = fig.add_subplot(gs[0, 1])

    # A finite vector mesh for the bilinear surface; no raster rendering.
    mesh = 12
    faces, colors = [], []
    for i in range(mesh):
        for j in range(mesh):
            a, b = i / mesh, (i + 1) / mesh
            c, d = j / mesh, (j + 1) / mesh
            faces.append(((a, c, a * c), (b, c, b * c),
                          (b, d, b * d), (a, d, a * d)))
            mid_z = ((a + b) / 2) * ((c + d) / 2)
            colors.append((0.68 - 0.16 * mid_z, 0.84 - 0.08 * mid_z,
                           0.82 - 0.07 * mid_z, 0.88))
    ax3d.add_collection3d(
        Poly3DCollection(faces, facecolors=colors, edgecolors="#669F9A", linewidths=0.35)
    )
    s = [j / 32 for j in range(33)]
    for u, v, z in (
        (s, [0.0] * len(s), [0.0] * len(s)),
        ([1.0] * len(s), s, s),
        (s, [1.0] * len(s), s),
        ([0.0] * len(s), s, [0.0] * len(s)),
    ):
        ax3d.plot(u, v, z, color=NAVY, lw=1.65)
    for x, y, z, dx, dy, dz in (
        (0.41, 0.0, 0.0, 0.18, 0.0, 0.0),
        (1.0, 0.41, 0.41, 0.0, 0.18, 0.18),
        (0.59, 1.0, 0.59, -0.18, 0.0, -0.18),
        (0.0, 0.59, 0.0, 0.0, -0.18, 0.0),
    ):
        ax3d.quiver(x, y, z, dx, dy, dz, color=NAVY, linewidth=1.3, arrow_length_ratio=0.34)
    ax3d.set(xlim=(0, 1), ylim=(0, 1), zlim=(0, 1))
    ax3d.set_xticks([0, 1])
    ax3d.set_yticks([0, 1])
    ax3d.set_zticks([0, 1])
    ax3d.set_xlabel(r"$u$", labelpad=-3, fontsize=11)
    ax3d.set_ylabel(r"$v$", labelpad=-3, fontsize=11)
    ax3d.set_zlabel(r"$z$", labelpad=-6, fontsize=11)
    ax3d.tick_params(labelsize=8, pad=-1)
    ax3d.set_box_aspect((1.0, 1.0, 0.83))
    ax3d.view_init(elev=24, azim=-56)
    for axis in (ax3d.xaxis, ax3d.yaxis, ax3d.zaxis):
        axis.pane.fill = False
        axis.pane.set_edgecolor("#E2E7E9")
    ax3d.grid(False)
    ax3d.set_title(r"$\sigma(u,v)=(u,v,uv)$", fontsize=12, pad=9)

    ns = list(range(2, 257))
    dyadic = [2**j for j in range(1, 9)]
    # Fractions compute the exact formulas; float conversion is only for plotting.
    ax.plot(ns, [float(volume_sum(n)) for n in ns], color=NAVY, lw=1.8)
    ax.plot(ns, [float(boundary_sum(n)) for n in ns], color=TEAL, lw=1.8)
    ax.plot(dyadic, [float(volume_sum(n)) for n in dyadic], color=NAVY,
            marker="o", lw=0, ms=4, label=r"Interior sum $V_N$")
    ax.plot(dyadic, [float(boundary_sum(n)) for n in dyadic], color=TEAL,
            marker="s", lw=0, ms=4, label=r"Boundary sum $B_N$")
    ax.axhline(float(Fraction(2, 3)), color="#687780", ls=(0, (4, 3)),
               lw=1.15, label=r"Common integral $2/3$")
    ax.set_xscale("log", base=2)
    ax.set_xticks(dyadic, [str(n) for n in dyadic])
    ax.set_xlim(1.85, 280)
    ax.set_ylim(0.12, 0.705)
    ax.set_yticks([0.2, 0.4, 0.6])
    ax.set_xlabel(r"Mesh size $N$ per coordinate", labelpad=7, fontsize=10)
    ax.set_ylabel("Integral approximation", labelpad=8, fontsize=10)
    ax.set_title("Finite sums approach the same value", fontsize=11, pad=10)
    ax.tick_params(labelsize=9)
    ax.grid(axis="y", color="#E3E9EB", lw=0.65)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.legend(loc="lower right", frameon=False, fontsize=9, labelspacing=0.65,
              borderpad=0.15, handlelength=2.3)
    export(fig, directory, "example_convergence", "Bilinear surface and exact Stokes sum convergence")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir", type=Path,
        default=Path(__file__).resolve().parents[1] / "report" / "figures",
    )
    args = parser.parse_args()
    configure()
    grid_cancellation(args.output_dir)
    example_convergence(args.output_dir)
    print(f"Wrote PDF and PNG figures to {args.output_dir.resolve()}")


if __name__ == "__main__":
    main()
