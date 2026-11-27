"""Render the exact Hausdorff dimension formula in the main paper."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def main():
    limit = 1 / np.log(2)
    h = np.linspace(0.002, limit, 600)
    dimension = 1 / np.expm1(1 / h)
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                         "pdf.fonttype": 42, "axes.spines.top": False,
                         "axes.spines.right": False})
    fig, ax = plt.subplots(figsize=(5.85, 2.65), layout="constrained")
    ax.plot(np.r_[0, h], np.r_[0, dimension], color="#20536A", linewidth=2.3)
    for base in (4, 3, 2):
        x = 1 / np.log(base)
        y = 1 / (base - 1)
        ax.plot([x, x], [0, y], color="#ABB5B9", linestyle=":", linewidth=0.8)
        ax.scatter(x, y, s=22, color="#20536A", zorder=3)
    ax.set(xlim=(-0.02, limit + 0.05), ylim=(-0.02, 1.04),
           xlabel=r"Lower normalized decay rate $h$",
           ylabel="Hausdorff dimension",
           xticks=[0, 1/np.log(4), 1/np.log(3), limit],
           xticklabels=["0", r"$1/\log 4$", r"$1/\log 3$", r"$1/\log 2$"],
           yticks=[0, 1/3, 1/2, 1], yticklabels=["0", "1/3", "1/2", "1"])
    ax.tick_params(direction="out", length=3)
    for side in ("bottom", "left"):
        ax.spines[side].set_color("#626D72")
    fig.savefig(Path(__file__).with_name("spectrum.pdf"),
                metadata={"Title": "Hausdorff dimension of the heat-decay level sets",
                          "CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
