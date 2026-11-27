#!/usr/bin/env python3
"""Draw the paper's figure from rigorously outward-rounded CSV bounds."""
import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

folder = Path(__file__).resolve().parent
with (folder / "window_bounds.csv").open(newline="") as source:
    data = list(csv.DictReader(source))
n = [int(row["n"]) for row in data]
lower = [float(row["lower_bound"]) for row in data]
upper = [float(row["upper_bound"]) for row in data]
assert n == list(range(119))

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.edgecolor": "#75828A", "xtick.color": "#34454D",
                     "ytick.color": "#34454D", "pdf.fonttype": 42})
fig, (wide, zoom) = plt.subplots(1, 2, figsize=(7.0, 2.8),
                                gridspec_kw={"width_ratios": [1.65, 1]})
for ax in (wide, zoom):
    ax.grid(axis="y", color="#E3E8E9", linewidth=.6)
    ax.set_axisbelow(True)
    ax.axhline(0, color="#708088", linewidth=.8)
    ax.set_xlabel("Li coefficient index $n$")
    ax.tick_params(length=3)

wide.fill_between(n, lower, upper, color="#5EAAA5")
wide.plot(n, lower, color="#206D6C", linewidth=1.25)
wide.plot(n, upper, color="#206D6C", linewidth=.75)
wide.set(xlim=(0, 120), ylim=(-.0025, .049), xticks=[0, 30, 60, 90, 118],
         yticks=[0, .01, .02, .03, .04])
wide.set_ylabel("Second difference $d_n$")
wide.set_title("Certified bounds through index 118", loc="left", fontsize=10)
wide.scatter([118], [(lower[-1]+upper[-1])/2], s=15, color="#A74334", zorder=4)

for j in range(113, 119):
    color = "#A74334" if j == 118 else "#206D6C"
    mid = (lower[j]+upper[j])/2
    zoom.errorbar(j, mid*1000, yerr=(upper[j]-lower[j])*500, fmt="none",
                  capsize=4, capthick=1.5, color=color, linewidth=2)
zoom.set(xlim=(112.5,118.5), ylim=(-.49, 2.45), xticks=[113, 115, 117, 118],
         yticks=[0, .5, 1., 1.5, 2.])
zoom.set_ylabel("$10^3 d_n$")
zoom.set_title("First change of sign", loc="left", fontsize=10)
fig.subplots_adjust(bottom=.23, left=.10, right=.97, top=.85, wspace=.47)
fig.savefig(folder / "curvature_bounds.pdf", metadata={"Title":"Certified Li second differences"})
if __name__ == "__main__":
    print("Wrote curvature_bounds.pdf")
