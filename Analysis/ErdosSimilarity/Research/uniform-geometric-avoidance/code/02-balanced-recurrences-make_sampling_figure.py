#!/usr/bin/env python3
"""Regenerate the sampling illustration (requires matplotlib).

The sequence terms and sample indices are computed with Fraction before
conversion to floating-point plot coordinates. The image is an illustration,
not a numerical verification of the universal theorem.
"""
from __future__ import annotations

import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from verify_exact import EXAMPLES, F, scalar_recurrence, verify_example


def main() -> None:
    directory = Path(__file__).resolve().parents[1] / "figures"
    directory.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.family": "DejaVu Serif", "font.size": 8.5,
        "axes.labelsize": 8.5, "axes.titlesize": 10,
        "xtick.labelsize": 7.5, "ytick.labelsize": 7.5,
        "axes.spines.top": False, "axes.spines.right": False,
        "figure.facecolor": "white", "savefig.facecolor": "white",
        "pdf.fonttype": 42
    })
    ink, teal, orange, gray = "#183C48", "#146F77", "#BF602B", "#7E8991"
    figure, axes = plt.subplots(
        2, 2, figsize=(7.05, 4.9), sharex="col",
        gridspec_kw={"height_ratios": [1, 1.9]}
    )
    titles = [
        r"$a_n=\operatorname{Re}((3/10+2i/5)^n)$",
        r"$a_n=\operatorname{Re}((i/2)^n)$"
    ]
    for column, (example, title) in enumerate(zip(EXAMPLES[:2], titles)):
        receipt = verify_example(example)
        values = scalar_recurrence(example, 40)
        indices = list(range(38))
        blocks = [max(abs(values[n]), abs(values[n + 1])) for n in indices]
        selected = receipt["samples"]
        selected_n = [row["original_index"] for row in selected]
        selected_g_n = [row["block_index"] for row in selected]
        top, bottom = axes[0, column], axes[1, column]
        normalized = [float(values[n] / F(1, 2) ** n) for n in indices]
        top.plot(indices, normalized, "-", color=gray, linewidth=0.8, zorder=1)
        top.scatter(indices, normalized, s=9, color=ink, zorder=2)
        top.scatter(selected_n, [normalized[n] for n in selected_n],
                    s=26, color=orange, zorder=3)
        top.axhline(0, color="#C8CFD2", linewidth=0.6)
        top.set_title(title, color=ink, pad=8)
        top.set_ylim(-1.17, 1.17)
        top.set_yticks([-1, 0, 1])
        if column == 0:
            top.set_ylabel(r"$a_n / 2^{-n}$")
        for row in selected:
            j = row["level"]
            upper = math.log2(float(example.scale ** j))
            lower = math.log2(float(example.alpha * example.scale ** j))
            bottom.axhspan(lower, upper, color="#EEF3F3", zorder=0)
            bottom.axhline(upper, color="#CCD9DA", linewidth=0.55,
                           linestyle=":", zorder=0)
        bottom.plot(indices, [math.log2(float(g)) for g in blocks],
                    "-", color=teal, linewidth=1.05, zorder=2,
                    label=r"block norm $g_n$")
        bottom.scatter(
            selected_g_n, [math.log2(float(blocks[n])) for n in selected_g_n],
            marker="o", facecolors="white", edgecolors=teal, linewidths=1.05,
            s=30, zorder=3, label=r"first block crossing $\nu_j$"
        )
        bottom.scatter(
            selected_n, [math.log2(float(abs(values[n]))) for n in selected_n],
            marker="D", color=orange, s=23, zorder=4,
            label=r"selected scalar $a_{\nu_j+k_j}$"
        )
        for row in selected:
            block_n, original_n = row["block_index"], row["original_index"]
            if block_n != original_n:
                y = math.log2(float(abs(values[original_n])))
                bottom.plot([block_n, original_n], [y, y], color=orange,
                            linewidth=0.8, zorder=3)
        bottom.set_xlim(-0.8, 37.5)
        bottom.set_ylim(-41, 1)
        bottom.set_yticks([0, -6, -12, -18, -24, -30, -36])
        bottom.set_xticks([0, 6, 12, 18, 24, 30, 36])
        bottom.set_xlabel("original index n")
        if column == 0:
            bottom.set_ylabel(r"$\log_2$ of absolute scale")
    handles, labels = axes[1, 0].get_legend_handles_labels()
    figure.legend(handles, labels, loc="lower center", ncol=3,
                  frameon=False, bbox_to_anchor=(0.5, 0.018), fontsize=7.8,
                  columnspacing=1.3, handlelength=1.9)
    figure.suptitle(
        r"Signed block sampling: $g_n=\max(|a_n|,|a_{n+1}|)$, "
        r"$Q=1/64$, $\alpha=1/20$",
        fontsize=10, color=ink, y=0.987
    )
    figure.text(
        0.5, 0.006,
        r"Shaded bands are $\alpha Q^j<|a|\leq Q^j$. "
        "Circles mark block crossings; diamonds mark actual sequence terms.",
        ha="center", va="bottom", fontsize=7.4, color=gray
    )
    figure.subplots_adjust(left=0.092, right=0.985, bottom=0.16,
                           top=0.87, hspace=0.20, wspace=0.20)
    figure.savefig(directory / "signed_block_sampling.pdf")
    figure.savefig(directory / "signed_block_sampling.png", dpi=220)
    plt.close(figure)
    print(directory / "signed_block_sampling.pdf")


if __name__ == "__main__":
    main()

