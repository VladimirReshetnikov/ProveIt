#!/usr/bin/env python3
"""Render the exact verification examples; requires matplotlib and numpy.

The source data are computed with Fraction by verification/verify_recurrence.py.
Only rendering converts the already-verified values to floating point.
"""

from pathlib import Path
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent / "verification"))
from verify_recurrence import examples, sample, states_until  # noqa: E402


def style() -> None:
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.labelcolor": "#243449",
        "text.color": "#243449",
        "axes.edgecolor": "#718198",
        "xtick.color": "#53647a",
        "ytick.color": "#53647a",
        "pdf.fonttype": 42,
        "savefig.facecolor": "white",
    })


def save(fig, name: str) -> None:
    fig.savefig(HERE / f"{name}.pdf", bbox_inches="tight")
    fig.savefig(HERE / f"{name}.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    style()
    cases = examples()
    fig, axes = plt.subplots(1, 3, figsize=(11.4, 3.7), constrained_layout=True)
    for ax, example in zip(axes, cases):
        selected, _ = sample(example, 6)
        j = np.array([item["j"] for item in selected], dtype=float)
        upper = j * np.log10(float(example.q))
        lower = upper + np.log10(float(example.c))
        actual = np.array([np.log10(abs(float(item["quotient"]))) for item in selected])
        ax.fill_between(j, lower, upper, color="#dcecf7", label="Guaranteed annulus")
        ax.plot(j, lower, color="#8eb7d3", linewidth=0.8)
        ax.plot(j, upper, color="#8eb7d3", linewidth=0.8)
        ax.plot(j, actual, color="#b64d35", marker="o", markersize=4,
                linewidth=1.2, label="Selected quotient term")
        for item, xx, yy in zip(selected, j, actual):
            ax.annotate(str(item["index"]), (xx, yy), xytext=(0, 5),
                        textcoords="offset points", ha="center", fontsize=7)
        ax.set_title(example.title, fontsize=10, pad=10)
        ax.set_xlabel("Annular index $j$")
        ax.set_xticks(j)
        ax.grid(axis="y", alpha=0.17)
    axes[0].set_ylabel(r"$\log_{10}|h_{m_j}|$")
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="outside lower center", ncol=2, frameon=False)
    fig.suptitle("State norms select actual scalar terms inside common annuli",
                 fontsize=12, fontweight="bold")
    save(fig, "sampling_envelopes")

    fig, axes = plt.subplots(1, 3, figsize=(11.4, 3.5), constrained_layout=True)
    for ax, example in zip(axes, cases):
        states = states_until(example, 32)
        n = np.arange(len(states))
        values = np.array([float(state[0]) for state in states])
        zero = values == 0
        ax.vlines(n[~zero], 0, values[~zero], color="#5e89a8", linewidth=0.85)
        ax.scatter(n[~zero], values[~zero], color="#275c82", s=11, zorder=3)
        ax.scatter(n[zero], np.zeros(zero.sum()), facecolors="white", edgecolors="#b64d35",
                   s=17, linewidths=0.9, zorder=4, label="Exact zero")
        ax.axhline(0, color="#8b99a9", linewidth=0.65)
        ax.set_yscale("symlog", linthresh=1e-8, linscale=0.65)
        ax.set_ylim(-1.6, 1.6)
        ax.set_yticks([-1, -1e-2, -1e-4, -1e-6, -1e-8,
                      0, 1e-8, 1e-6, 1e-4, 1e-2, 1])
        ax.set_title(example.title, fontsize=10, pad=10)
        ax.set_xlabel("Original sequence index $n$")
        ax.set_xticks([0, 8, 16, 24, 32])
        ax.grid(axis="y", alpha=0.15)
    axes[0].set_ylabel("Normalized scalar term (symmetric log scale)")
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="outside lower center", frameon=False)
    fig.suptitle("Oscillation, exact zeros, and repeated roots", fontsize=12, fontweight="bold")
    save(fig, "signed_terms")
    print("Generated sampling_envelopes.pdf/png and signed_terms.pdf/png")


if __name__ == "__main__":
    main()
