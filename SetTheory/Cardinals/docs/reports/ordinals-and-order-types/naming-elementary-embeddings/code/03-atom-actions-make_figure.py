#!/usr/bin/env python3
"""Draw two finite windows of exact upward sets in Z^2.

The full sets are S_A = ({(0,0)} union {(n,-n): n in A}) + N^2.
Their intersections with x+y=0 recover exactly the selected roots.  The plot
is an illustration; the general cardinality argument is in the article.
Requires Matplotlib. Run this script from any directory.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D


def main() -> None:
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 10,
        "mathtext.fontset": "dejavusans",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "axes.spines.top": False,
        "axes.spines.right": False,
    })
    colors = {"member": "#245B7A", "root": "#D86C2D",
              "absent": "#D0D6DD", "line": "#768394"}
    figure, axes = plt.subplots(1, 2, figsize=(9.8, 4.8), sharey=True)
    for axis, selected in zip(axes, ({1, 3, 5}, {2, 3, 5})):
        root_indices = {0} | selected
        roots = {(n, -n) for n in root_indices}
        included, excluded = [], []
        for x in range(-1, 7):
            for y in range(-6, 2):
                member = any(x >= n and y >= -n for n in root_indices)
                (included if member else excluded).append((x, y))
        for points, color, size, zorder in (
            (excluded, colors["absent"], 17, 2),
            (included, colors["member"], 25, 3),
            (sorted(roots), colors["root"], 66, 4),
        ):
            x_values, y_values = zip(*points)
            axis.scatter(x_values, y_values, color=color, s=size,
                         zorder=zorder, edgecolors="white", linewidths=0.35)
        axis.plot([-1.35, 6.35], [1.35, -6.35], color=colors["line"],
                  linestyle=(0, (4, 3)), linewidth=1.0, zorder=1)
        axis.axhline(0, color="#C1C8D0", linewidth=0.7, zorder=0)
        axis.axvline(0, color="#C1C8D0", linewidth=0.7, zorder=0)
        axis.set(xlim=(-1.4, 6.4), ylim=(-6.4, 1.4),
                 xticks=range(-1, 7), yticks=range(-6, 2),
                 xlabel=r"$x$", aspect="equal")
        set_text = ",".join(str(n) for n in sorted(selected))
        axis.set_title(r"$A=\{" + set_text + r"\}$", pad=11,
                       fontsize=12)
        axis.text(5.55, -6.0, r"$x+y=0$", fontsize=8.5,
                  rotation=-45, ha="right", va="bottom",
                  color="#5F6D7F")
        axis.tick_params(length=3, width=0.6, colors="#4B5563")
        for spine in ("left", "bottom"):
            axis.spines[spine].set_color("#9AA5B1")
            axis.spines[spine].set_linewidth(0.7)
    axes[0].set_ylabel(r"$y$", rotation=0, labelpad=12)
    legend = [
        Line2D([], [], marker="o", linestyle="None", color=colors["root"],
               markersize=7, label=r"Selected root $(n,-n)$"),
        Line2D([], [], marker="o", linestyle="None", color=colors["member"],
               markersize=5, label=r"Other point of $S_A$"),
        Line2D([], [], marker="o", linestyle="None", color=colors["absent"],
               markersize=4, label=r"Point outside $S_A$"),
    ]
    figure.legend(handles=legend, loc="lower center", ncol=3,
                  bbox_to_anchor=(0.5, 0.008), frameon=False,
                  handletextpad=0.45, columnspacing=1.8)
    figure.subplots_adjust(left=0.075, right=0.985, bottom=0.18,
                           top=0.90, wspace=0.17)
    destination = Path(__file__).resolve().parent
    pdf = destination / "antichain_upsets.pdf"
    png = destination / "antichain_upsets.png"
    figure.savefig(pdf, bbox_inches="tight", metadata={
        "Title": "Antichain coding of upward subsets of Z^2",
        "Subject": "Two exact finite windows; roots recover the selected subsets",
        "Author": ""})
    figure.savefig(png, dpi=160, bbox_inches="tight")
    print(f"Wrote {pdf}")
    print(f"Wrote {png}")


if __name__ == "__main__":
    main()
