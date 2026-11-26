#!/usr/bin/env python3
"""Generate the exact endpoint table and a static publication plot."""
from fractions import Fraction
from pathlib import Path
import csv
import math
ROOT = Path(__file__).resolve().parent.parent

def endpoints(p, h0, B):
    B = Fraction(B)
    old = h0 + math.ceil(p ** h0 * B * (h0 + B + 2))
    sharp = h0 + math.floor(p ** (h0 - 1) * B)
    return old, sharp

def main():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    data, figs = ROOT / "data", ROOT / "figures"
    data.mkdir(exist_ok=True)
    figs.mkdir(exist_ok=True)
    cases = [(2,1,1),(2,1,10),(3,2,1),(3,2,5),(2,3,10),(5,2,2)]
    with (data / "bound_comparison.csv").open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["p","h0","B","previous_endpoint","sharp_endpoint"])
        for p,h0,B in cases:
            writer.writerow([p,h0,B,*endpoints(p,h0,B)])
    xs = list(range(21))
    old, new = zip(*(endpoints(2,1,x) for x in xs))
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":11,
                         "axes.spines.top":False,"axes.spines.right":False})
    fig, ax = plt.subplots(figsize=(7.8,4.1), constrained_layout=True)
    ax.plot(xs, old, color="#596b87", marker="o", markersize=3.5,
            linewidth=1.8, label="Previous sufficient endpoint")
    ax.plot(xs, new, color="#007f82", marker="o", markersize=3.5,
            linewidth=2.4, label="Sharp universal endpoint")
    ax.scatter([10,10],[261,11],s=45,color=["#596b87","#007f82"],zorder=5)
    ax.annotate("261",xy=(10,261),xytext=(10.5,380),color="#415571")
    ax.annotate("11",xy=(10,11),xytext=(10.5,7.1),color="#006568")
    ax.set_yscale("log")
    ax.set_xlabel("Valuation budget B")
    ax.set_ylabel("Largest required order exponent H")
    ax.set_xticks([0,5,10,15,20])
    ax.set_xlim(-.5,20.7)
    ax.grid(axis="y",alpha=.18,which="both")
    ax.legend(frameon=False,loc="upper left")
    ax.set_title("Exact aggregate selection: p = 2, starting level 1",
                 loc="left",fontweight="bold",fontsize=12,pad=12)
    fig.savefig(figs / "order_bounds.pdf")
    fig.savefig(figs / "order_bounds.png",dpi=200)
    print("Generated bound_comparison.csv and order_bounds.pdf/png")

if __name__ == "__main__":
    main()

