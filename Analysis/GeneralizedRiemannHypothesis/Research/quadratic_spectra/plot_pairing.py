"""Plot the exact-formula pairing and its height-100 approximation for conductor 3."""
import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def main():
    here = Path(__file__).resolve().parent
    with (here / "zeros_mod3.csv").open() as stream:
        zeros = np.array([float(row["positive_ordinate"]) for row in csv.DictReader(stream)])
    h = 0.14
    centers = np.linspace(0.23, 1.76, 1400)
    nodes, weights = np.polynomial.legendre.leggauss(40)
    offsets = h * (nodes + 1) / 2
    def gamma_term(u):
        return np.exp(-1.5 * u) / (-np.expm1(-2*u))
    arch = np.sum((gamma_term(centers[:, None]+offsets) +
                   gamma_term(centers[:, None]-offsets)) *
                  (h-offsets)*weights*h/2, axis=1)
    full = -arch
    for n, prime, char in [(2,2,-1), (3,3,0), (4,2,1), (5,5,-1)]:
        tent = np.maximum(0, h-np.abs(centers-np.log(n)))
        full -= char * np.log(prime) / np.sqrt(n) * tent
    partial = np.cos(centers[:, None]*zeros) @ (8*(np.sin(h*zeros/2)/zeros)**2)
    fig, ax = plt.subplots(figsize=(6.25, 2.37), layout="constrained")
    ax.axhline(0, color="#727d84", linewidth=0.65)
    ax.plot(centers, full, label="Full pairing", color="#1b405a", lw=1.9)
    ax.plot(centers, partial, label="Zeros through height 100", color="#ba552e",
            lw=1.15, dashes=(4, 2.3))
    ticks = np.log([2,3,4,5])
    ax.set_xticks(ticks, [r"$\log 2$",r"$\log 3$",r"$\log 4$",r"$\log 5$"])
    ax.set_ylim(-0.069,0.114)
    ax.set_ylabel("Interval pairing")
    ax.set_xlabel("Separation of the interval starts")
    ax.legend(loc="upper left", fontsize=8, frameon=False)
    ax.spines[["top","right"]].set_visible(False)
    ax.grid(axis="y", alpha=0.14)
    fig.savefig(here/"interval_pairing.pdf", metadata={"Title":"Interval pairings for the character modulo three"})


if __name__ == "__main__":
    main()
