#!/usr/bin/env python3
"""Reproduce the two static figures in the Herglotz research article.

Requires matplotlib and numpy.  No network connection, external TeX
installation, or interactive display is needed.  Paths are resolved
relative to this file, so the script can be called from any directory.

  python code/reproduce_figures.py
  python code/reproduce_figures.py --output-dir figures --dpi 300

The rank plot reads exact integer data from data/rank_table.csv.  Its rank
is the algebraic dimension of a span of exterior symbols over Q.  The
second plot evaluates the proved coefficient formula directly.
"""

import argparse
import csv
from math import isqrt
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


NAVY = "#17324D"
TEAL = "#126B72"
OCHRE = "#B65E26"
GRAY = "#677681"
GRID = "#DDE3E8"


def style():
    plt.rcParams.update({
        "font.family": "serif",
        "font.serif": ["DejaVu Serif"],
        "font.size": 10.5,
        "mathtext.fontset": "cm",
        "axes.titlesize": 14,
        "axes.titleweight": "normal",
        "axes.labelsize": 11.5,
        "axes.labelcolor": NAVY,
        "axes.edgecolor": GRAY,
        "axes.linewidth": 0.7,
        "text.color": NAVY,
        "xtick.color": GRAY,
        "ytick.color": GRAY,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "legend.fontsize": 10,
        "legend.frameon": False,
        "savefig.facecolor": "white",
        "figure.facecolor": "white",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def finish_axes(ax):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.tick_params(axis="both", length=3.5, width=0.7)
    ax.set_axisbelow(True)
    ax.grid(axis="y", color=GRID, linewidth=0.6)


def save(fig, output_dir, stem, dpi, title, subject):
    output_dir.mkdir(parents=True, exist_ok=True)
    for extension in ["pdf", "png"]:
        metadata = {"Title": title, "Creator": "reproduce_figures.py"}
        if extension == "pdf":
            metadata.update({"Subject": subject, "CreationDate": None,
                             "ModDate": None})
        fig.savefig(output_dir / f"{stem}.{extension}", dpi=dpi,
                    bbox_inches="tight", pad_inches=0.08, metadata=metadata)
    plt.close(fig)


def rank_figure(data_file, output_dir, dpi):
    with data_file.open(newline="") as handle:
        rows = [{key: int(value) for key, value in row.items()}
                for row in csv.DictReader(handle)]
    rows = [row for row in rows if 1 <= row["q"] <= 200]
    if [row["q"] for row in rows] != list(range(1, 201)):
        raise ValueError("The input must contain each conductor 1,...,200")
    for row in rows:
        if row["q"] >= 3 and (4 * row["boundary_rank"] !=
                row["phi"] - row["roots_plus"] - row["roots_minus"]):
            raise ValueError(f"Rank formula mismatch at q={row['q']}")
    primes = [row for row in rows if is_prime(row["q"])]
    composites = [row for row in rows if row["q"] >= 4 and not is_prime(row["q"])]
    fig, ax = plt.subplots(figsize=(6.7, 4.35))
    fig.subplots_adjust(left=0.12, bottom=0.16, top=0.86, right=0.98)
    ax.scatter([r["q"] for r in composites],
               [r["boundary_rank"] for r in composites],
               s=23, marker="o", facecolor=TEAL, edgecolor="white",
               linewidth=0.35, alpha=0.78, label="Composite conductors", zorder=3)
    ax.scatter([r["q"] for r in primes], [r["boundary_rank"] for r in primes],
               s=40, marker="^", facecolor=OCHRE, edgecolor="white",
               linewidth=0.35, label="Prime conductors", zorder=4)
    ax.scatter([1], [rows[0]["boundary_rank"]], s=26, marker="s",
               facecolor="white", edgecolor=GRAY, linewidth=0.8,
               label=r"$q=1$ (convention)", zorder=5)
    finish_axes(ax)
    ax.set_xlim(-3, 203)
    ax.set_ylim(-1.4, 52)
    ax.set_xticks([0, 50, 100, 150, 200])
    ax.set_yticks([0, 10, 20, 30, 40, 50])
    ax.set_xlabel(r"Conductor $q$", labelpad=7)
    ax.set_ylabel(r"Exact symbol rank $d(q)$", labelpad=7)
    ax.legend(loc="upper left", borderaxespad=0.3, labelspacing=0.6,
              handletextpad=0.4)
    ax.text(0.025, 0.65,
            r"$d(q)=\dim_{\mathbb{Q}}\mathrm{span}\{\beta_q(a):(a,q)=1\}$",
            transform=ax.transAxes, fontsize=10.5, color=NAVY)
    fig.suptitle("Exact cyclotomic symbol ranks", x=0.55, y=0.985)
    fig.text(0.55, 0.90, r"$1\leq q\leq 200$; dimension over $\mathbb{Q}$",
             ha="center", fontsize=10.5, color=GRAY)
    save(fig, output_dir, "cyclotomic_rank", dpi,
         "Exact cyclotomic symbol ranks through conductor 200",
         "Exact rational dimension of the Herglotz exterior-symbol span, from rank_table.csv.")


def optimal_phase_figure(output_dir, dpi):
    t = np.linspace(0, 1, 1001)
    coefficient = 2 * np.minimum(t, 1 - t) ** 2 - 13 / 24
    fig, ax = plt.subplots(figsize=(6.7, 4.35))
    fig.subplots_adjust(left=0.13, bottom=0.17, top=0.82, right=0.98)
    ax.axvline(0.5, color=GRAY, linestyle=(0, (3, 3)), linewidth=0.85, alpha=0.65)
    ax.plot(t, coefficient, color=TEAL, linewidth=2.2, zorder=3)
    ax.scatter([0, 0.5, 1], [-13 / 24, -1 / 24, -13 / 24],
               s=34, facecolor=NAVY, edgecolor="white", linewidth=0.6, zorder=4)
    finish_axes(ax)
    ax.set_xlim(-0.025, 1.025)
    ax.set_ylim(-0.585, 0.075)
    ax.set_xticks([0, 0.25, 0.5, 0.75, 1],
                  ["0", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "1"])
    ax.set_yticks([-13/24, -3/8, -1/4, -1/8, -1/24],
                  [r"$-\frac{13}{24}$", r"$-\frac{3}{8}$", r"$-\frac{1}{4}$",
                   r"$-\frac{1}{8}$", r"$-\frac{1}{24}$"])
    ax.set_xlabel(r"Phase $t=\mathrm{frac}(\pi x-\frac{1}{4})$", labelpad=7)
    ax.set_ylabel(r"First correction coefficient $c(t)$", labelpad=7)
    ax.annotate("Leading-order cutoff tie", xy=(0.5, -1/24),
                xytext=(0.76, 0.033), ha="center", va="center", fontsize=9.5,
                arrowprops={"arrowstyle": "-", "color": GRAY,
                            "linewidth": 0.8, "shrinkB": 7})
    ax.text(0.5, -0.47,
            r"$c(t)=2\min(t,1-t)^2-\frac{13}{24}$",
            ha="center", va="center", fontsize=13, color=NAVY,
            bbox={"facecolor": "white", "edgecolor": "none", "pad": 3})
    fig.suptitle("Periodic correction to the optimal error", x=0.55, y=0.985)
    fig.text(0.55, 0.895,
             r"$\min_N R_N(x)=\frac{e^{-2\pi x}}{\sqrt{x}}"
             r"\left[1+\frac{c(t)}{2\pi x}+O(x^{-2})\right]$",
             ha="center", fontsize=12, color=GRAY)
    save(fig, output_dir, "optimal_correction", dpi,
         "Periodic first correction to the optimal Herglotz truncation error",
         "The exact coefficient 2 min(t,1-t)^2-13/24 as a function of the phase t.")


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rank-data", type=Path,
                        default=root / "data" / "rank_table.csv")
    parser.add_argument("--output-dir", type=Path, default=root / "figures")
    parser.add_argument("--dpi", type=int, default=300)
    args = parser.parse_args()
    if args.dpi < 72:
        parser.error("Use a resolution of at least 72 dpi")
    style()
    rank_figure(args.rank_data, args.output_dir, args.dpi)
    optimal_phase_figure(args.output_dir, args.dpi)
    print(f"Wrote cyclotomic_rank and optimal_correction as PDF and PNG to {args.output_dir}")


if __name__ == "__main__":
    main()
