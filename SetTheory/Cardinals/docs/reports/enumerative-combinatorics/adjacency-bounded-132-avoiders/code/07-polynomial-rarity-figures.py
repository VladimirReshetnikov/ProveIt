#!/usr/bin/env python3
"""Reproduce the article figures from the theorem and exact-count CSV file.

Requires NumPy and Matplotlib. Run verify.py first to regenerate the data.
Default Matplotlib colors are used. The theorem plot is not a data fit.
"""
from __future__ import annotations

import csv
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
FIGURES = ROOT / "figures"


def save(fig: plt.Figure, stem: str) -> None:
    fig.tight_layout()
    fig.savefig(FIGURES / f"{stem}.pdf")
    fig.savefig(FIGURES / f"{stem}.png", dpi=180)
    plt.close(fig)


def main() -> None:
    FIGURES.mkdir(parents=True, exist_ok=True)
    data_path = ROOT / "data" / "phase_counts.csv"
    if not data_path.is_file():
        raise FileNotFoundError("Run python code/verify.py to create phase_counts.csv")

    theta = np.linspace(0.181, 0.96, 6000)
    exponent = np.floor(1 / theta) / 2
    fig, ax = plt.subplots(figsize=(7.2, 3.7))
    ax.plot(theta, exponent, linewidth=1.8)
    ax.set_xlabel(r"Adjacency fraction $\theta$")
    ax.set_ylabel(r"Exponent $\lfloor 1/\theta\rfloor/2$")
    ax.set_xticks([1/5, 1/4, 1/3, 1/2, 3/4])
    ax.set_xticklabels([r"$1/5$", r"$1/4$", r"$1/3$", r"$1/2$", r"$3/4$"])
    ax.set_xlim(0.181, 0.96)
    ax.set_ylim(0.35, 2.65)
    ax.grid(True, alpha=0.25)
    save(fig, "phase_exponents")

    with data_path.open(newline="") as f:
        rows = list(csv.DictReader(f))
    fig, ax = plt.subplots(figsize=(7.2, 3.7))
    for fraction in ["1/2", "2/5", "1/3", "1/4"]:
        subset = [r for r in rows if r["theta"] == fraction]
        ax.plot([int(r["n"]) for r in subset],
                [float(r["scaled_probability"]) for r in subset],
                marker="o", label=rf"$\theta={fraction}$")
    ax.set_xlabel(r"Permutation size $n$")
    ax.set_ylabel(r"$n^{\lfloor1/\theta\rfloor/2}\Pr(M_n\leq\lfloor\theta n\rfloor)$")
    ax.legend()
    ax.grid(True, alpha=0.25)
    save(fig, "finite_counts")
    print("Saved both article figures.")


if __name__ == "__main__":
    main()
