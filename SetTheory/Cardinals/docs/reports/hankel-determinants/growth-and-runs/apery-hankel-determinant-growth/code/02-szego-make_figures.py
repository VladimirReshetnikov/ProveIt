#!/usr/bin/env python3
"""Regenerate the article's figures from the supplied numerical data.
Requires matplotlib. This plots existing data; it does not recompute norms.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    with (root / "data/norms.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    constants = json.loads((root / "data/constant.json").read_text())
    K = float(constants["K"])
    limit = float(constants["OEIS_plot_limit"])
    figures = root / "figures"
    figures.mkdir(parents=True, exist_ok=True)

    selected = [row for row in rows if 11 <= int(row["n"]) <= 200]
    if not selected:
        raise ValueError("The CSV has no rows in the displayed index range.")
    fig, ax = plt.subplots(figsize=(8.0, 4.7))
    ax.plot([int(row["n"]) - 1 for row in selected],
            [float(row["R_previous"]) for row in selected],
            label="Normalized Apéry determinant ratio")
    ax.axhline(limit, linestyle="--",
               label=f"Integral-defined limit ≈ {limit:.10f}")
    ax.set_xlabel("n")
    ax.set_ylabel(r"$D_{n+1}/(\Lambda^{2n+1}D_n)$")
    ax.set_title("The oscillating ratios converge to a well-defined constant")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figures / "ratio_limit.pdf")
    fig.savefig(figures / "ratio_limit.png", dpi=220)
    plt.close(fig)

    selected = [row for row in rows if 10 <= int(row["n"]) <= 200]
    fig, ax = plt.subplots(figsize=(8.0, 4.7))
    ax.plot([int(row["n"]) for row in selected],
            [float(row["U_n"]) for row in selected],
            label=r"Original normalized norm $U_n$")
    ax.plot([int(row["n"]) for row in selected],
            [float(row["E_even"]) for row in selected],
            label=r"Monotone upper envelope $E_{2n}$")
    ax.axhline(K, linestyle="--", label=f"K ≈ {K:.10f}")
    ax.set_xlabel("n")
    ax.set_ylabel("Normalized value")
    ax.set_title("Related Hankel determinants produce monotone upper bounds")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figures / "monotone_envelope.pdf")
    fig.savefig(figures / "monotone_envelope.png", dpi=220)
    plt.close(fig)


if __name__ == "__main__":
    main()
