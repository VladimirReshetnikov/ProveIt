#!/usr/bin/env python3
"""Regenerate the two vector figures in A Catalan Law Behind Growing Shifts.

Run from any directory: python /path/to/code/make_figures.py
The curves are floating-point diagnostics, not interval certificates.
"""
from __future__ import annotations

from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from verify import distribution, free_energy, parameters


def main() -> None:
    output = Path(__file__).resolve().parents[1] / "figures"
    output.mkdir(parents=True, exist_ok=True)

    s = np.linspace(0.0, 3.0, 121)
    fig, ax = plt.subplots(figsize=(7.1, 4.3))
    for n in (64, 256, 1024):
        beta = float(parameters(n, n)[3])
        values = []
        for x in s:
            tau = x / np.sqrt(beta)
            log_r, _ = distribution(n, n, tau)
            values.append(np.exp(log_r - tau))
        ax.plot(s, values, label=f"N = m = {n}")
    ax.plot(s, np.exp(-s * s / 2), "--", label="Limit: exp(−s²/2)")
    ax.set(xlabel="s = τ√β", ylabel="R(τ) exp(−τ)")
    ax.legend()
    ax.grid(alpha=0.2)
    fig.tight_layout()
    fig.savefig(output / "determinant_crossover.pdf")
    plt.close(fig)

    t = np.linspace(0.0, 5.0, 151)
    fig, ax = plt.subplots(figsize=(7.1, 4.3))
    shapes = [
        (0.0, "θ = 0: m/N → ∞"),
        (2 / 3, "θ = 2/3: m/N → 1"),
        (1.0, "θ = 1: m/N → 0"),
    ]
    for theta, label in shapes:
        ax.plot(t, [free_energy(theta, x) for x in t], label=label)
    ax.set(xlabel="t = βτ", ylabel="Limiting scaled logarithm Fθ(t)")
    ax.legend()
    ax.grid(alpha=0.2)
    fig.tight_layout()
    fig.savefig(output / "free_energy.pdf")
    plt.close(fig)
    print(f"Saved both figures to {output}")


if __name__ == "__main__":
    main()
