#!/usr/bin/env python3
"""Regenerate exact explanatory plots for the hat-guessing article."""

from pathlib import Path
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
FIGURES = ROOT / "figures"


def main():
    FIGURES.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.family": "DejaVu Sans",
            "font.size": 9,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.titlesize": 10,
            "axes.titleweight": "bold",
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )
    r, a = 2, 4
    t = 2**r - 1
    n = 2 * a * t
    fig, (left, right) = plt.subplots(
        1, 2, figsize=(8.8, 3.35), gridspec_kw={"width_ratios": [1.9, 1]}
    )
    colors = ["#176B87", "#4B83B4", "#748DA8"]
    pairs = np.arange(a * t + 1)
    physical = 2 * pairs
    for c, color in zip(range(1, t + 1), colors):
        excess = np.maximum(0, (pairs + t - c) // t)
        left.step(
            physical, excess, where="post", color=color, lw=1.7,
            label=f"Successful column {c}"
        )
    left.plot(
        physical, physical / (2 * t), "--", color="#222222", lw=1.3,
        label=r"Profile $u/(2t)$"
    )
    left.set(
        xlabel="Players in prefix (complete pairs)",
        ylabel=r"Local excess $D_u$",
        title="Every successful round adds one",
        xlim=(0, n),
        ylim=(-0.25, a + 0.4),
        xticks=np.arange(0, n + 1, 6),
        yticks=np.arange(a + 1),
    )
    left.grid(axis="y", color="#E1E6EC", linewidth=0.6)
    left.legend(frameon=False, fontsize=7.5, loc="upper left")
    scores = [0, a * (t + 1)]
    probabilities = [1 / (t + 1), t / (t + 1)]
    right.bar(
        [0, 1], probabilities, width=0.55, color=["#B85C50", "#176B87"],
        zorder=3
    )
    right.set(
        xticks=[0, 1],
        xticklabels=[f"{scores[0]} correct", f"{scores[1]} correct"],
        ylabel="Exact probability",
        title="Finite score distribution",
        ylim=(0, 1),
        yticks=[0, 0.25, 0.5, 0.75, 1],
    )
    right.grid(axis="y", color="#E1E6EC", linewidth=0.6, zorder=0)
    for x, p, label in zip([0, 1], probabilities, ["1/4", "3/4"]):
        right.text(x, p + 0.035, label, ha="center", fontsize=10)
    right.text(
        0.5, 0.94, r"$\mathbb{E}S_{24}=12$", transform=right.transAxes,
        ha="center", va="top", fontsize=10
    )
    fig.tight_layout(pad=1.2, w_pad=2.5)
    fig.savefig(FIGURES / "block_prefix.pdf", bbox_inches="tight")
    fig.savefig(FIGURES / "block_prefix.png", dpi=200, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    main()
