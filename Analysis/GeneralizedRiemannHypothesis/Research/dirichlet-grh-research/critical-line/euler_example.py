"""Evaluate the ordinary sharp Euler products for the primitive character mod 4.

Run with Python 3, numpy, matplotlib and mpmath.
The finite experiment illustrates the analytic theorem. It uses floating point.
"""
import argparse
import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


def primes_up_to(limit):
    flags = np.ones(limit + 1, dtype=bool)
    flags[:2] = False
    for p in range(2, int(limit**0.5) + 1):
        if flags[p]:
            flags[p*p::p] = False
    return np.flatnonzero(flags)


def beta_and_limit():
    mp.mp.dps = 45
    s = mp.mpf("0.5")
    beta = (mp.zeta(s, mp.mpf(1)/4) - mp.zeta(s, mp.mpf(3)/4)) / 2
    k_real = mp.quad(lambda t: mp.cos(mp.pi*t/2)/t, [1, 2])/2
    return float(beta), float(beta*mp.exp(k_real))


def evaluate(primes, cutoffs):
    odd_primes = primes[primes > 2]
    logs = np.log(odd_primes)
    coefficients = np.where(odd_primes % 4 == 1, 1., -1.) / np.sqrt(odd_primes)
    for x in cutoffs:
        stop = int(np.searchsorted(odd_primes, x, side="right"))
        values = coefficients[:stop]
        angle = (-0.5j*np.pi/np.log(x)) * logs[:stop]
        central_log = -np.log1p(-values).sum()
        moving_log = -np.log1p(-values * np.exp(angle)).sum()
        yield [int(x), float(np.exp(central_log)), float(np.exp(moving_log.real))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-x", type=int, default=10**7)
    parser.add_argument("--output-dir", type=Path, default=Path("."))
    args = parser.parse_args()
    if args.max_x < 100:
        parser.error("--max-x must be at least 100")
    output = args.output_dir
    output.mkdir(parents=True, exist_ok=True)
    beta, moving_limit = beta_and_limit()
    central_prediction = np.sqrt(2.) * beta
    cutoffs = np.unique(np.rint(np.geomspace(100, args.max_x, 130)).astype(int))
    rows = list(evaluate(primes_up_to(args.max_x), cutoffs))
    with (output / "euler_example.csv").open("w", newline="") as target:
        writer = csv.writer(target)
        writer.writerow(["x", "fixed_center", "moving_modulus"])
        writer.writerows(rows)
    print(f"beta(1/2) = {beta:.12f}")
    print(f"Fixed-center DRH prediction = {central_prediction:.12f}")
    print(f"Proved moving-modulus limit = {moving_limit:.12f}")
    print(f"Final cutoff and finite products: {rows[-1]}")
    data = np.array(rows)
    fig, axes = plt.subplots(1, 2, figsize=(8.0, 2.85))
    for ax, column, target, title, color, label in (
        (axes[0], 1, central_prediction, "Fixed central height", "#74442d", "DRH prediction"),
        (axes[1], 2, moving_limit, "Moving height π/(2 log x)", "#216478", "proved limit"),
    ):
        ax.semilogx(data[:, 0], data[:, column], lw=1.15, color=color)
        ax.axhline(target, color="#30343b", lw=1.0, ls="--", label=label)
        ax.set_title(title, fontsize=10, loc="left")
        ax.set_xlabel("prime cutoff x", fontsize=9)
        ax.tick_params(labelsize=8)
        ax.spines[["right", "top"]].set_visible(False)
        ax.legend(loc="best", frameon=False, fontsize=8)
    axes[0].set_ylabel("partial product modulus", fontsize=9)
    fig.tight_layout()
    fig.savefig(output / "euler_example.pdf", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    main()
