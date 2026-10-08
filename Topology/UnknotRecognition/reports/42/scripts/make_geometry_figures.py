"""Make the exact normal-extraction article figures from recorded results.

This script performs no benchmarking and never expands a normal surface.
Matplotlib is the only non-standard dependency. PDF output uses vector paths
and embedded TrueType text; the companion PNGs are rendered at 320 dpi.
"""

from __future__ import annotations

import argparse
import json
from math import log2
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from matplotlib.ticker import FixedLocator, ScalarFormatter


INK = "#14334A"
TEAL = "#137B80"
BLUE = "#456D9B"
ORANGE = "#B96627"
TRIANGLE = "#CFE6E3"
QUAD = "#D7E3F1"
PALE = "#F1F4F6"
GRID = "#D8E0E5"


def configure():
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "mathtext.fontset": "cm",
        "axes.labelsize": 9,
        "axes.titlesize": 10,
        "axes.titleweight": "bold",
        "axes.labelcolor": INK,
        "axes.edgecolor": "#72828C",
        "text.color": INK,
        "xtick.color": INK,
        "ytick.color": INK,
        "xtick.labelsize": 8,
        "ytick.labelsize": 8,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.linewidth": 0.7,
        "grid.color": GRID,
        "grid.linewidth": 0.6,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
    })


def save_figure(figure, output, stem, title):
    output.mkdir(parents=True, exist_ok=True)
    figure.savefig(output / f"{stem}.pdf", bbox_inches="tight", pad_inches=0.08,
                   metadata={"Title": title, "Author": "ProveIt research continuation",
                             "Creator": "Matplotlib; make_geometry_figures.py",
                             "CreationDate": None, "ModDate": None})
    figure.savefig(output / f"{stem}.png", bbox_inches="tight", pad_inches=0.08,
                   dpi=320, metadata={"Title": title})
    plt.close(figure)


def draw_face_overlap(output):
    figure, ax = plt.subplots(figsize=(6.50, 3.44))
    figure.subplots_adjust(left=0.02, right=0.98, top=0.91, bottom=0.04)
    ax.set_xlim(-0.99, 3.07)
    ax.set_ylim(-0.56, 3.49)
    ax.axis("off")
    ax.set_title("Sharp face overlap: five gluing bands", loc="left", pad=9)

    # Three equal rank bins represent the three individual normal arcs in
    # this type. Block boundaries and internal prism gaps are different data.
    height = 0.43
    rows = {"Source": 2.68, "Target": 1.69, "Overlaps": 0.60}
    for rank in range(4):
        ax.plot([rank, rank], [0.31, 3.00], color=GRID, linewidth=0.8,
                linestyle=(0, (2.5, 3)), zorder=0)

    def block(start, stop, y, color, label, position=None):
        ax.add_patch(Rectangle((start, y - height / 2), stop - start, height,
                               facecolor=color, edgecolor=INK, linewidth=0.8, zorder=2))
        ax.text((start + stop) / 2 if position is None else position,
                y, label, ha="center", va="center", fontsize=12, zorder=4)

    block(0, 1, rows["Source"], TRIANGLE, r"$T_1$", 0.50)
    block(1, 3, rows["Source"], QUAD, r"$Q$", 1.50)
    block(0, 2, rows["Target"], TRIANGLE, r"$T_1$", 0.50)
    block(2, 3, rows["Target"], QUAD, r"$Q$", 2.50)
    ax.text(2.5, rows["Source"], r"$Q$", ha="center", va="center", fontsize=12)
    ax.text(1.5, rows["Target"], r"$T_1$", ha="center", va="center", fontsize=12)

    for name, y in rows.items():
        ax.text(-0.14, y, name, ha="right", va="center", fontsize=9.5,
                fontweight="bold" if name == "Overlaps" else "normal")

    # A source Q gap at rank boundary 2 meets the target T/Q residual region.
    # Conversely, a target T gap at rank boundary 1 meets the source T/Q residue.
    for rank, y, text in ((2, rows["Source"], "one source prism gap"),
                          (1, rows["Target"], "one target prism gap")):
        ax.plot([rank, rank], [y - height / 2, y + height / 2],
                color=ORANGE, linewidth=1.8, zorder=5)
        ax.scatter([rank], [y + height / 2], s=22, color=ORANGE, zorder=6)
        ax.annotate(text, xy=(rank, y + height / 2 + 0.018),
                    xytext=(rank, y + 0.47), ha="center", va="center",
                    fontsize=8, color=ORANGE,
                    arrowprops={"arrowstyle": "-", "color": ORANGE,
                                "lw": 0.8, "shrinkA": 2, "shrinkB": 1})

    labels = (r"$T\to T$", r"$Q\to T$", r"$Q\to Q$")
    index_maps = (r"$0\mapsto0$", r"$0\mapsto1$", r"$1\mapsto0$")
    for index, (label, indices) in enumerate(zip(labels, index_maps)):
        block(index, index + 1, rows["Overlaps"], PALE, label)
        ax.text(index + 0.5, 0.16, indices, ha="center", va="center", fontsize=9)
    for rank in range(4):
        ax.text(rank, -0.065, str(rank), ha="center", va="center", fontsize=8)
    ax.text(-0.14, -0.065, "rank", ha="right", va="center", fontsize=8)
    ax.text(0, -0.40,
            "This arc type: 3 bands.  Other two arc types: 1 + 1.  Total: 5.",
            ha="left", va="center", fontsize=8.4, color=TEAL)
    save_figure(figure, output, "normal_face_overlap",
                "Sharp normal face overlap and two singleton prism contacts")


def integer(value):
    if type(value) is int:
        return value
    if type(value) is str and value.startswith("0x"):
        return int(value, 16)
    raise ValueError("expected a recorded nonnegative integer or hexadecimal string")


def draw_scaling(report, output):
    records = report["scaling"]["layered_tori"]
    sizes = [integer(row["tetrahedra"]) for row in records]
    discs = [integer(row["normal_discs"]) for row in records]
    surface = [integer(row["surface_face_bands"]) for row in records]
    prism = [integer(row["prism_face_bands"]) for row in records]
    residue = [integer(row["local_residual_cells"]) for row in records]
    if any(s != 6 * t - 4 or p != 6 * t - 14 or r != 4 * t
           for t, s, p, r in zip(sizes, surface, prism, residue)):
        raise ValueError("the supplied rows are not the stated layered-torus fixture family")

    figure, axes = plt.subplots(1, 2, figsize=(6.50, 3.05))
    figure.subplots_adjust(left=0.10, right=0.985, top=0.855, bottom=0.21, wspace=0.40)
    left, right = axes
    left.set_title("(a) Represented normal discs", loc="left", pad=9)
    left.plot(sizes, [log2(count) for count in discs], color=INK, linewidth=1.7,
              marker="o", markersize=4.3, markerfacecolor="white", markeredgewidth=1)
    left.set_xlabel(r"Tetrahedra $t$")
    left.set_ylabel(r"$\log_2 D_t$", labelpad=6)
    left.set_xlim(0, 1070)
    left.set_ylim(0, 780)
    left.set_xticks((0, 256, 512, 768, 1024))
    left.set_yticks((0, 200, 400, 600))
    left.grid(axis="both", zorder=0)
    left.annotate(r"$D_{128}\approx2.79\times10^{27}$",
                  xy=(128, log2(discs[sizes.index(128)])), xytext=(345, 150),
                  fontsize=9, color=INK,
                  arrowprops={"arrowstyle": "-", "color": INK, "lw": 0.75})
    left.text(0.06, 0.88, r"$D_t=F_{t+5}-5$", transform=left.transAxes,
              fontsize=11, ha="left", va="center")

    right.set_title("(b) Extracted local records", loc="left", pad=9)
    right.plot(sizes, [value / t for value, t in zip(surface, sizes)],
               color=BLUE, linewidth=1.5, marker="o", markersize=4.2,
               markerfacecolor="white", markeredgewidth=1,
               label=r"Surface bands: $6-4/t$")
    right.plot(sizes, [value / t for value, t in zip(prism, sizes)],
               color=TEAL, linewidth=1.5, marker="s", markersize=3.9,
               markerfacecolor="white", markeredgewidth=1,
               label=r"Prism bands: $6-14/t$")
    right.plot(sizes, [value / t for value, t in zip(residue, sizes)],
               color=ORANGE, linewidth=1.3, marker="^", markersize=3.9,
               markerfacecolor="white", markeredgewidth=1,
               label="Residual cells: 4")
    right.set_xscale("log", base=2)
    right.set_xlim(6.8, 1210)
    right.set_ylim(3.80, 6.15)
    right.xaxis.set_major_locator(FixedLocator((8, 32, 128, 512, 1024)))
    right.xaxis.set_major_formatter(ScalarFormatter())
    right.set_yticks((4, 4.5, 5, 5.5, 6))
    right.set_xlabel(r"Tetrahedra $t$ (log$_2$ scale)")
    right.set_ylabel("Record count divided by t", labelpad=6)
    right.grid(axis="both", zorder=0)
    right.legend(loc="center right", bbox_to_anchor=(1.035, 0.42), frameon=True,
                 facecolor="white", edgecolor="white", fontsize=7.4,
                 handlelength=1.7, borderpad=0.35, labelspacing=0.7,
                 framealpha=0.96)
    figure.text(0.10, 0.035,
                "Exact structural counts from the recorded inputs; no expanded surfaces or new timings.",
                ha="left", va="center", fontsize=7.6, color="#5D6F7D")
    save_figure(figure, output, "normal_extraction_scaling",
                "Normal-coordinate extraction: exponential represented weight and linear local records")


def main():
    package = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path,
                        default=package / "results" / "normal_interval_verification.json")
    parser.add_argument("--output-dir", type=Path,
                        default=package / "article" / "figures")
    options = parser.parse_args()
    report = json.loads(options.results.read_text())
    configure()
    draw_face_overlap(options.output_dir)
    draw_scaling(report, options.output_dir)
    print(json.dumps({"figures": ["normal_face_overlap", "normal_extraction_scaling"],
                      "formats": ["pdf", "png"], "output_dir": str(options.output_dir),
                      "source_results": str(options.results)}, indent=2))


if __name__ == "__main__":
    main()
