#!/usr/bin/env python3
"""Regenerate the two illustrations; matplotlib is needed only for this script.

All sequence terms come from the exact integer implementation. Floating-point
arithmetic is used only for the normalized asymptotic illustration, not proofs.
"""
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from mixed_base import dense_coefficients, interleaved_count

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"


def main() -> None:
    FIGURES.mkdir(parents=True, exist_ok=True)
    coefficients = dense_coefficients(2, 3, 5, 5)
    ones = [s for s, value in enumerate(coefficients) if value == 1]
    fig, ax = plt.subplots(figsize=(7.2, 3.25))
    ax.step(range(len(coefficients)), coefficients, where="mid", linewidth=1.2,
            label="Coefficient of $x^s$")
    ax.scatter(ones, [1] * len(ones), marker="o", s=42, zorder=3,
               label="Coefficients equal to 1")
    ax.set_xlabel("Exponent $s$")
    ax.set_ylabel("$[x^s]P_{10}(x)$")
    ax.set_xlim(-3, len(coefficients)+2)
    ax.set_ylim(bottom=-0.5)
    ax.grid(alpha=0.2)
    ax.legend(frameon=False, loc="upper center")
    fig.tight_layout()
    fig.savefig(FIGURES / "coefficient_profile.pdf")
    fig.savefig(FIGURES / "coefficient_profile.png", dpi=180)
    plt.close(fig)

    alpha = math.log(2) / math.log(3)
    growth = 2**(1-alpha)
    ns = list(range(2, 501))
    normalized = [interleaved_count(2, 3, 2*n) / growth**n for n in ns]
    fig, ax = plt.subplots(figsize=(7.2, 3.25))
    ax.scatter(ns, normalized, s=9, label="$a_n/\\lambda^n$")
    ax.axhline(2**(-alpha), linestyle="--", linewidth=1,
               label="Proved limiting bounds")
    ax.axhline(2**(1-alpha), linestyle="--", linewidth=1)
    ax.set_xlabel("Paired index $n$")
    ax.set_ylabel("Normalized coefficient-one count")
    ax.set_xlim(0, 505)
    ax.grid(alpha=0.2)
    ax.legend(frameon=False, loc="lower left", bbox_to_anchor=(0, 1.01), ncol=2)
    fig.tight_layout()
    fig.savefig(FIGURES / "normalized_counts.pdf")
    fig.savefig(FIGURES / "normalized_counts.png", dpi=180)
    plt.close(fig)
    print("Created coefficient_profile and normalized_counts (PDF and PNG).")
    print(f"alpha={alpha:.12f}, lambda={growth:.12f}, R={1/growth:.12f}, "
          f"sqrt(R)={math.sqrt(1/growth):.12f}")


if __name__ == "__main__":
    main()
