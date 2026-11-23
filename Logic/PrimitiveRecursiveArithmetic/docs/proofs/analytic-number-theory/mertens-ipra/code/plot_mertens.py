"""Regenerate the cover figure. Requires Matplotlib; the PDF is already included."""
from pathlib import Path
from math import sqrt

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from check_mertens import mobius_prefix


def main():
    end = 10000
    _, values = mobius_prefix(end)
    indices = range(2, end + 1)
    ratios = [values[n] / sqrt(n) for n in indices]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 8, "pdf.fonttype": 42})
    figure, axis = plt.subplots(figsize=(6.5, 1.67))
    axis.set_xscale("log")
    axis.plot(indices, ratios, color="#195665", lw=0.65)
    for level in (-1, 1):
        axis.axhline(level, lw=0.65, linestyle=(0, (3, 3)), color="#829296", zorder=0)
    axis.axhline(0, color="#a3b0b2", lw=0.65, zorder=0)
    axis.plot([5], [values[5] / sqrt(5)], marker="o", color="#a64e2b", ms=3.2)
    axis.annotate(r"$n=5$", xy=(5, values[5] / sqrt(5)), xytext=(9, -0.72),
                  ha="left", fontsize=8, color="#8b3d1c",
                  arrowprops={"arrowstyle": "-", "color": "#a64e2b", "lw": 0.65})
    axis.set_xlim(1.9, 10000)
    axis.set_ylim(-1.12, 1.12)
    axis.set_xticks([2, 10, 100, 1000, 10000], labels=["2", "10", "100", "1,000", "10,000"])
    axis.minorticks_off()
    axis.set_yticks([-1, 0, 1])
    axis.set_ylabel(r"$M(n)/\sqrt{n}$")
    axis.tick_params(length=0, pad=3, colors="#38474a")
    for spine in axis.spines.values():
        spine.set_visible(False)
    figure.subplots_adjust(left=0.085, right=0.966, bottom=0.15, top=0.95)
    target = Path(__file__).resolve().parents[1] / "figures" / "mertens-quotient.pdf"
    target.parent.mkdir(exist_ok=True)
    figure.savefig(target)
    plt.close(figure)


if __name__ == "__main__":
    main()
