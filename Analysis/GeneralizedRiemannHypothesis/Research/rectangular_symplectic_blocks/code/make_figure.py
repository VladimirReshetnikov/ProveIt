#!/usr/bin/env python3
"""Create the standalone scientific figure from exact rational evaluations."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from exact_laws import laws, eta, theta

root=Path(__file__).resolve().parents[1]
out=root/"figures"
out.mkdir(exist_ok=True)
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,"axes.spines.top":False,
                     "axes.spines.right":False,"axes.labelcolor":"#23354d",
                     "text.color":"#23354d","axes.titlesize":11})
fig,axes=plt.subplots(1,2,figsize=(10,3.8),layout="constrained")
colors=["#176B87","#B94F38","#6B61A6"]
delta=float(theta(2,64)*(1-eta(2,64)))
for gap,color in zip((0,2,6),colors):
    bs=list(range(2,26,2))
    rows=[laws(2,b+gap,b) for b in bs]
    axes[0].plot(bs,[float(r["full_tv"]) for r in rows],"o-",markersize=3,
                 color=color,label=fr"$a-b={gap}$")
    axes[1].semilogy(bs,[float(r["rank_tv"]) for r in rows],"o-",markersize=3,
                     color=color,label=fr"$a-b={gap}$")
axes[0].axhline(delta,color="#53616C",linestyle="--",linewidth=1,label=fr"$\Delta_2={delta:.6f}\ldots$")
axes[0].set_title("All matrix entries: persistent discrepancy",loc="left",pad=12)
axes[1].set_title("Only rank: exponentially vanishing discrepancy",loc="left",pad=12)
for ax in axes:
    ax.set_xlabel(r"Number of columns $b$")
    ax.set_ylabel("Total variation distance")
    ax.set_xticks([2,6,10,14,18,22,26])
    ax.grid(axis="y",alpha=.22)
    ax.legend(frameon=False,fontsize=9)
axes[0].set_ylim(.12,.132)
axes[1].set_ylim(1e-10, .3)
fig.savefig(out/"rank_and_matrix_distance.pdf",bbox_inches="tight")
fig.savefig(out/"rank_and_matrix_distance.png",dpi=180,bbox_inches="tight")
print(out/"rank_and_matrix_distance.pdf")

