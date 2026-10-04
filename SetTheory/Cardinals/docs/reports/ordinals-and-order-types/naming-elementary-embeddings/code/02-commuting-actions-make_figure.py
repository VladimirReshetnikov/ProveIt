#!/usr/bin/env python3
"""Generate the exact integer staircase figure for the research article.

Requires matplotlib. Run from any directory:
    python3 make_figure.py

Outputs figures/staircases.pdf and figures/staircases.png beside this script.
The PDF is a precise vector plot; the PNG is a preview of the same figure.
"""

from io import BytesIO
from pathlib import Path
import os
from tempfile import NamedTemporaryFile

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch


INK = "#20384A"
BLUE = "#28618A"
PALE = "#E8F0F5"
ORANGE = "#B86A27"
RED = "#AD3D44"
GRAY = "#9EADB7"


def atomic_write(path, data):
    """Keep the previous complete artifact until its replacement is complete."""
    temporary = None
    try:
        with NamedTemporaryFile(dir=path.parent, prefix=path.name + ".",
                                suffix=".tmp", delete=False) as handle:
            temporary = Path(handle.name)
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def height(bits, m):
    if m <= 0:
        return -m
    return -m - 2 - sum(bit < m - 1 for bit in bits)


def draw_panel(axis, bits, title):
    xmin, xmax = -3, 7
    ymin, ymax = -12, 5
    for m in range(xmin, xmax + 1):
        axis.axvline(m, color="#DDE4E9", linewidth=0.45, zorder=0)
    for n in range(ymin, ymax + 1):
        axis.axhline(n, color="#DDE4E9", linewidth=0.45, zorder=0)

    # A half-open staircase drawing convention: h(m) is drawn across the
    # column [m,m+1), with a vertical drop at m+1. Only the integer lattice
    # points, not the shading convention, define U_S.
    xs, ys = [], []
    for m in range(xmin, xmax + 1):
        xs.extend([m, m + 1])
        ys.extend([height(bits, m), height(bits, m)])
    axis.fill_between(xs, ys, ymax + 0.45, color=PALE, zorder=1)
    axis.plot(xs, ys, color=BLUE, linewidth=1.8, zorder=3)

    present_x, present_y, absent_x, absent_y = [], [], [], []
    boundary_x, boundary_y = [], []
    for m in range(xmin, xmax + 1):
        boundary = height(bits, m)
        for n in range(ymin, ymax + 1):
            if n >= boundary:
                present_x.append(m)
                present_y.append(n)
            else:
                absent_x.append(m)
                absent_y.append(n)
        if ymin <= boundary <= ymax:
            boundary_x.append(m)
            boundary_y.append(boundary)
    axis.scatter(absent_x, absent_y, s=6, color="#CFD7DD", linewidths=0, zorder=2)
    axis.scatter(present_x, present_y, s=11, color=BLUE, linewidths=0, zorder=4)
    axis.scatter(boundary_x, boundary_y, s=27, color=BLUE,
                 edgecolor="white", linewidth=0.5, zorder=5)

    # The drop d(0)=3 is shared by every code and is the unique rigid marker.
    axis.plot([1, 1], [0, -3], color=RED, linewidth=3.0, zorder=6)
    axis.annotate("Unique drop: 3", xy=(1, -1.5), xytext=(2.15, -0.65),
                  color=RED, fontsize=10,
                  arrowprops={"arrowstyle": "-", "color": RED, "lw": 0.9},
                  ha="left", va="center", zorder=7)

    start = (3, 2)
    arrow = {"arrowstyle": "-|>", "lw": 1.8, "mutation_scale": 14,
             "shrinkA": 0, "shrinkB": 0}
    axis.annotate("", xy=(4, 2), xytext=start,
                  arrowprops={**arrow, "color": ORANGE}, zorder=8)
    axis.annotate("", xy=(3, 3), xytext=start,
                  arrowprops={**arrow, "color": INK}, zorder=8)
    axis.text(4.22, 1.92, "$f$", color=ORANGE, fontsize=13, ha="left", va="center")
    axis.text(3, 3.35, "$g$", color=INK, fontsize=13, ha="center", va="bottom")
    axis.text(-2.65, -10.8, "$n<h_S(m)$", color="#798994", fontsize=10)
    axis.text(4.8, 4.1, "$U_S$", color=BLUE, fontsize=13)

    axis.set_title(title, color=INK, fontsize=12.5, pad=13)
    axis.set_xlim(xmin - 0.35, xmax + 0.35)
    axis.set_ylim(ymin - 0.35, ymax + 0.35)
    axis.set_xticks(range(-3, 8, 2))
    axis.set_yticks(range(-12, 6, 2))
    axis.tick_params(axis="both", labelsize=9, colors=INK, length=3)
    axis.set_xlabel("$m$", fontsize=12, color=INK, labelpad=7)
    axis.set_ylabel("$n$", fontsize=12, color=INK, rotation=0, labelpad=9)
    axis.set_aspect("equal", adjustable="box")
    for spine in axis.spines.values():
        spine.set_color(GRAY)
        spine.set_linewidth(0.8)


def main():
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "mathtext.fontset": "dejavusans",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "axes.unicode_minus": True,
    })
    figure, axes = plt.subplots(1, 2, figsize=(9.2, 7.6))
    draw_panel(axes[0], set(), "$S=\u2205$")
    draw_panel(axes[1], {0, 2, 3}, r"$S=\{0,2,3\}$")
    figure.suptitle("Two commuting injections on coded staircases", x=0.5, y=0.982,
                     fontsize=16, fontweight="bold", color=INK)
    figure.text(0.5, 0.947,
                r"$U_S=\{(m,n)\in\mathbb{Z}^2:n\geq h_S(m)\}$"
                "    ·    $f(m,n)=(m+1,n)$    ·    $g(m,n)=(m,n+1)$",
                ha="center", va="center", fontsize=10.5, color=INK)
    legend = [
        Line2D([0], [0], marker="o", color="none", markerfacecolor=BLUE,
               markersize=4, label="Points of $U_S$"),
        Patch(facecolor=PALE, edgecolor="none", label="Region above the boundary"),
        Line2D([0], [0], color=RED, linewidth=2.5, label="Marker $d_S(0)=3$"),
    ]
    figure.legend(handles=legend, loc="lower center", bbox_to_anchor=(0.5, 0.018),
                  ncol=3, frameon=False, fontsize=9.2,
                  columnspacing=1.8, handlelength=1.8)
    figure.subplots_adjust(left=0.07, right=0.975, top=0.88, bottom=0.11, wspace=0.24)
    destination = Path(__file__).resolve().parent / "figures"
    destination.mkdir(parents=True, exist_ok=True)
    metadata = {
        "Title": "Coded staircases for two commuting injections",
        "Author": "Research manuscript prepared with ChatGPT",
        "Subject": "Exact integer-grid examples; finite windows of infinite sets",
        "CreationDate": None,
        "ModDate": None,
    }
    pdf_buffer, png_buffer = BytesIO(), BytesIO()
    figure.savefig(pdf_buffer, format="pdf", metadata=metadata,
                   facecolor="white", bbox_inches="tight", pad_inches=0.14)
    figure.savefig(png_buffer, format="png", dpi=220,
                   facecolor="white", bbox_inches="tight", pad_inches=0.14)
    pdf_data, png_data = pdf_buffer.getvalue(), png_buffer.getvalue()
    if not pdf_data.startswith(b"%PDF-") or not pdf_data.rstrip().endswith(b"%%EOF"):
        raise RuntimeError("Matplotlib did not produce a complete PDF.")
    atomic_write(destination / "staircases.pdf", pdf_data)
    atomic_write(destination / "staircases.png", png_data)
    plt.close(figure)
    print("Wrote figures/staircases.pdf and figures/staircases.png")


if __name__ == "__main__":
    main()
