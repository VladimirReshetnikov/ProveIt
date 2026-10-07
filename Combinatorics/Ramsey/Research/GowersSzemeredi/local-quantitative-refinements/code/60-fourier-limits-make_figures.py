#!/usr/bin/env python3
"""Make the optional exact-profile illustration (NumPy and Matplotlib).

The figure visualizes proved formulas; it is not used to prove any inequality.
Run from any directory: python3 code/make_figures.py
"""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.ticker import MultipleLocator
import numpy as np


def main():
    root = Path(__file__).resolve().parents[1]
    destination = root / "figures"
    destination.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({
        "font.family": "DejaVu Serif",
        "font.size": 10.5,
        "mathtext.fontset": "dejavuserif",
        "axes.spines.top": False,
        "axes.spines.right": False,
        "pdf.fonttype": 42,
    })
    fig, (ax, grid) = plt.subplots(
        1, 2, figsize=(8.1, 4.0), gridspec_kw={"width_ratios": [1.55, 1]}
    )
    s = 16
    delta = np.linspace(0, 0.25, 901)
    exact = (1 - (1 - 4 * delta)**s) / 4 - 2**(2*s-3) * delta**(s-1) * (1-2*delta)
    previous = s*delta*(1-2*delta)*((1-2*delta)**(s-2) - (2*delta)**(s-2))
    ax.plot(delta, exact, color="#096973", lw=2.2, label=r"New $B_{16}(\delta)$")
    ax.plot(delta, previous, color="#65748b", lw=1.7, ls="--", label=r"Source 33: $F_{16}(\delta)$")
    examples = 1 / (2*np.arange(3, 25))
    values = (1-(1-4*examples)**s)/4 - 2**(2*s-3)*examples**(s-1)*(1-2*examples)
    ax.scatter(examples, values, s=18, color="#d18331", edgecolor="white", linewidth=0.35,
               label=r"Equality distances $1/(2n)$", zorder=4)
    ax.axvspan(0, 1/(4*(s-1)), color="#096973", alpha=0.08)
    ax.set(xlim=(0, .25), ylim=(0, .275), xlabel=r"Distance $\delta$ to the vertical model class",
           ylabel=r"Lower bound for failure $\varepsilon_{16}$")
    ax.xaxis.set_major_locator(MultipleLocator(.05))
    ax.yaxis.set_major_locator(MultipleLocator(.05))
    ax.grid(axis="y", color="#dddddd", lw=.5)
    ax.set_title("A. The full local polynomial", loc="left", pad=12, weight="bold", fontsize=10.5)
    ax.legend(frameon=False, loc="center", bbox_to_anchor=(.59,.54), fontsize=9)
    matrix = np.array([[int(x % 4 == 0 and y % 2 == 1) for y in range(8)] for x in range(12)])
    grid.imshow(matrix, cmap=ListedColormap(["#edf0f3", "#096973"]), vmin=0, vmax=1,
                interpolation="nearest", aspect="equal", origin="upper")
    grid.set_xticks(range(8))
    grid.set_yticks(range(12))
    grid.set_xticks(np.arange(-.5, 8, 1), minor=True)
    grid.set_yticks(np.arange(-.5, 12, 1), minor=True)
    grid.grid(which="minor", color="white", lw=1.5)
    grid.tick_params(which="minor", bottom=False, left=False)
    grid.tick_params(which="major", length=0)
    grid.set(xlabel=r"$y\in\mathbb{Z}_8$", ylabel=r"$x\in\mathbb{Z}_{12}$")
    grid.set_title("B. Equality map", loc="left", pad=12, weight="bold", fontsize=10.5)
    grid.text(.5, -0.17, r"$C=\{0,4,8\}$; $\ell_2(y)$ is parity"+"\n"+r"Dark cells: $f=1$; $\delta=1/8$",
              transform=grid.transAxes, ha="center", va="top", fontsize=9)
    fig.subplots_adjust(left=.115, right=.98, top=.86, bottom=.26, wspace=.4)
    metadata = {"Title": "Arrangement profile and its equality family",
                "Author": "ProveIt research manuscript", "CreationDate": None,
                "ModDate": None}
    fig.savefig(destination / "arrangement_profiles.pdf", metadata=metadata)
    fig.savefig(destination / "arrangement_profiles.png", dpi=170)
    plt.close(fig)
    print(destination / "arrangement_profiles.pdf")


if __name__ == "__main__":
    main()
