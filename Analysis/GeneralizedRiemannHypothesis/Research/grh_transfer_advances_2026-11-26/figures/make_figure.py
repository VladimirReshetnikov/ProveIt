#!/usr/bin/env python3
"""Illustrate the proved discrete minima. All proof decisions are in checks/."""
from pathlib import Path
import math
import csv
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

base = Path(__file__).parent
new = {34, 36, 38, 42, 44, 46, 50}
F = lambda u: math.sqrt(4+math.sqrt(8+u+math.sqrt(26-3*u)))
G = lambda n: 2*math.sqrt(math.cos(math.pi/n)**2+math.cos(2*math.pi/n)**2)
rows = []
for n in range(8, 51, 2):
    value = G(n)
    form = "alternating formula"
    if n >= 32 and n % 8 == 0:
        value, form = F(2*math.cos(8*math.pi/n)), "period-eight formula"
    if n == 50:
        value, form = 2.8115689061565, "midpoint of certified interval"
    rows.append((n,value,G(n),"new" if n in new else "predecessor",form))
with (base/"cycle_optima.csv").open("w",newline="") as fp:
    w=csv.writer(fp);w.writerow(["n","minimum_plot_value","alternating_family","status","exact_source"]);w.writerows(rows)

plt.rcParams.update({"font.family":"DejaVu Sans","font.size":9,
                     "axes.labelcolor":"#17384B","text.color":"#17384B",
                     "axes.edgecolor":"#C8D2D7","xtick.color":"#536675",
                     "ytick.color":"#536675","pdf.fonttype":42})
fig, axes = plt.subplots(1,2,figsize=(9.0,3.55),gridspec_kw={"width_ratios":[1,1.35]})
for ax in axes:
    ax.set_facecolor("white")
    ax.spines[["top","right"]].set_visible(False)
    ax.grid(axis="y",color="#E7ECEF",linewidth=.7)
    ax.set_axisbelow(True)
    ax.plot([r[0] for r in rows],[r[2] for r in rows],color="#9CAAB3",
            linewidth=1.2,linestyle="--",label="Alternating family")
    for st,color,marker,label in [
        ("predecessor","#375D80","s","Revalidated predecessor"),
        ("new","#158496","o","New exact cases")]:
        chosen=[r for r in rows if r[3]==st]
        ax.scatter([r[0] for r in chosen],[r[1] for r in chosen],
                   s=32,color=color,marker=marker,label=label,zorder=3,
                   edgecolor="white",linewidth=.5)
    ax.set_xlabel("Number of vertices")
axes[0].set(xlim=(7,51),ylim=(2.27,2.86),ylabel="Minimum spectral radius")
axes[0].set_xticks([8,16,24,32,40,50])
axes[0].set_title("Every even size, 8 to 50",loc="left",fontsize=10,fontweight="bold",pad=9)
axes[1].set(xlim=(31,51.5),ylim=(2.779,2.829))
axes[1].set_xticks([32,36,40,44,48,50])
axes[1].set_title("The new boundary pattern at 50",loc="left",fontsize=10,fontweight="bold",pad=9)
axes[1].annotate("50: positive cycle product",
                 xy=(50,2.8115689061565),xytext=(34,2.8205),
                 fontsize=8.5,color="#167D8D",
                 arrowprops={"arrowstyle":"-","color":"#167D8D","linewidth":.8})
handles,labels=axes[0].get_legend_handles_labels()
fig.legend(handles,labels,loc="lower center",bbox_to_anchor=(.5,-.015),
           ncol=3,frameon=False,fontsize=8.3)
fig.tight_layout(rect=(0,.09,1,1),w_pad=2)
for extension in ("pdf","png"):
    fig.savefig(base/f"cycle_optima.{extension}",dpi=190,bbox_inches="tight",facecolor="white")
