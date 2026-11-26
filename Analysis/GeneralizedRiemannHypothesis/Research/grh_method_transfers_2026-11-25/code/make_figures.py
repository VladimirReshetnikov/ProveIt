#!/usr/bin/env python3
"""Produce the report's static scientific figures from recorded data."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.labelcolor": "#17334A", "text.color": "#17334A",
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.titleweight": "bold", "savefig.bbox": "tight"})


def rows(name):
    with (ROOT / "results" / name).open() as f:
        return list(csv.DictReader(f))


def main():
    (ROOT / "figures").mkdir(exist_ok=True)
    fig, ax = plt.subplots(figsize=(7.1, 3.7))
    for filename, label, color, style in [
        ("cubic_checkpoints.csv", "Prime root counts (main criterion)", "#197A84", "-"),
        ("cubic_primepower_checkpoints.csv", "Full Dedekind prime powers", "#A56534", "--")]:
        data = rows(filename)
        ax.plot([int(r["n"]) for r in data], [float(r["n2_B_n"]) for r in data],
                style, color=color, lw=1.7, marker="o", ms=3.4, label=label)
    ax.axhline(0, color="#8896A0", lw=.7)
    ax.set(xlabel=r"Checkpoint index $n$ (cutoffs $n^4$ and $16n^4$)",
           ylabel=r"Scaled finite increment $n^2B(n)$",
           title=r"Cubic field $\alpha^3-\alpha-1=0$: finite illustration")
    ax.set_xticks([1, 5, 10, 15, 20])
    ax.grid(alpha=.16)
    ax.legend(frameon=False, loc="upper right", fontsize=8.8)
    fig.tight_layout()
    fig.savefig(ROOT / "figures/cubic_checkpoints.pdf")
    fig.savefig(ROOT / "figures/cubic_checkpoints.png", dpi=180)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7.1, 3.7))
    j = np.geomspace(2, 3000, 300)
    for r, label, color in [(3, "Cubic grid: loss decays", "#546B85"),
                             (4, "Quartic grid: limit 2", "#197A84"),
                             (5, "Quintic grid: loss grows", "#A56534")]:
        u = r * np.log1p(1 / j)
        loss = np.log(np.expm1(u) / u) - 1 + u / np.expm1(u)
        x_star = u * j ** r / (-np.expm1(-u))
        ax.loglog(j, np.sqrt(x_star) * loss, color=color, lw=2, label=label)
    ax.axhline(2, color="#8896A0", lw=.7, ls=":")
    ax.set(xlabel=r"Checkpoint index $j$ for grid $x_j=j^r$",
           ylabel=r"Scaled loss $\sqrt{x_*}\,R(x_*)$, where $R$ is maximal",
           title="Sharp loss from positivity alone")
    ax.grid(which="major", alpha=.16)
    ax.legend(frameon=False, fontsize=8.8)
    fig.tight_layout()
    fig.savefig(ROOT / "figures/sampling_loss.pdf")
    fig.savefig(ROOT / "figures/sampling_loss.png", dpi=180)
    plt.close(fig)
    print("Wrote two PDF figures and two PNG previews.")


if __name__ == "__main__":
    main()
