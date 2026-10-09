#!/usr/bin/env python3
"""Regenerate publication figures from the frozen stage summary CSV."""
from __future__ import annotations

import argparse
import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parent.parent
    parser.add_argument("--csv", type=Path,
                        default=root / "article/generated/stage-plot-data.csv")
    parser.add_argument("--output", type=Path, default=root / "article/figures")
    args = parser.parse_args()
    with args.csv.open(newline="") as source:
        rows = list(csv.DictReader(source))
    n = [int(row["crossings"]) for row in rows]
    policies = [
        ("baseline_default", "Default", "#34495e", "o"),
        ("baseline_forest", "Primitive forest", "#b56a23", "s"),
        ("singleton", "Singleton batch", "#177b73", "D"),
    ]
    plt.rcParams.update({
        "font.family": "serif", "font.size": 9, "axes.titlesize": 10,
        "axes.labelsize": 9, "xtick.labelsize": 8, "ytick.labelsize": 8,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "axes.spines.top": False, "axes.spines.right": False,
    })
    fig, axes = plt.subplots(1, 2, figsize=(6.5, 3.1))
    for ax, field, title, ylabel in zip(
            axes, ("median_ms", "search_work"),
            ("(a) Checked elapsed time", "(b) Charged search work"),
            ("Median milliseconds", "Search work units")):
        for key, label, color, marker in policies:
            values = [float(row[f"{key}_{field}"]) for row in rows]
            ax.plot(n, values, color=color, marker=marker, markersize=4,
                    linewidth=1.5, label=label)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log", base=10)
        ax.set_xticks(n)
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.minorticks_off()
        ax.grid(axis="y", which="major", color="#d8d8d8", linewidth=.5)
        ax.set_axisbelow(True)
        ax.set_title(title, loc="left", pad=9)
        ax.set_xlabel("Crossings (initial group rank)")
        ax.set_ylabel(ylabel)
    axes[0].set_yticks([1, 10, 100, 1000])
    axes[0].yaxis.set_major_formatter(ScalarFormatter())
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, ncol=3, loc="lower center", frameon=False,
               bbox_to_anchor=(.5, .005), fontsize=9)
    fig.subplots_adjust(left=.095, right=.985, bottom=.24, top=.88, wspace=.37)
    args.output.mkdir(parents=True, exist_ok=True)
    stem = args.output / "stage_scaling"
    fig.savefig(stem.with_suffix(".pdf"), metadata={"Title": "Checked group-stage scaling"})
    fig.savefig(stem.with_suffix(".png"), dpi=220)
    plt.close(fig)
    print(str(stem.with_suffix(".pdf")))


if __name__ == "__main__":
    main()
