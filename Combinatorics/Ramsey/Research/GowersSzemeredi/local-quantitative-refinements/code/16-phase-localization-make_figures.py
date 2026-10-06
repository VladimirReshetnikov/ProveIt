#!/usr/bin/env python3
"""Create the exact-formula comparison table and publication plot."""
from pathlib import Path
import csv
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
figures = root / "figures"
data = root / "data"
figures.mkdir(exist_ok=True)
data.mkdir(exist_ok=True)
rows=[]
for k in range(1,21):
    old=2*(k+1)**3
    finite=(k+2)*math.log2(3*(k+2)/4)
    optimized=(k+2)*math.log2((k+2)/2)
    obstruction=math.lgamma(k+3)/math.log(2)-(k+1)
    rows.append(dict(k=k,source_loss_bits=old,
                     finite_sliding_loss_bits=finite,
                     limiting_sliding_loss_bits=optimized,
                     local_obstruction_loss_bits=obstruction))
with (data/"localization_constants.csv").open("w",newline="") as f:
    writer=csv.DictWriter(f,fieldnames=rows[0].keys())
    writer.writeheader()
    writer.writerows(rows)
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                     "axes.labelsize":10,"axes.spines.top":False,
                     "axes.spines.right":False,"figure.dpi":160})
fig,ax=plt.subplots(figsize=(8.4,4.45))
x=[r["k"] for r in rows]
for field,label,color,style in [
    ("source_loss_bits",r"Gowers: $2^{-2(k+1)^3}$","#7c8694","-"),
    ("finite_sliding_loss_bits",r"Finite sliding: $[4/(3(k+2))]^{k+2}$","#176b70","-"),
    ("limiting_sliding_loss_bits",r"Optimized local limit: $[2/(k+2)]^{k+2}$","#2558a4","-"),
    ("local_obstruction_loss_bits",r"Local upper obstruction: $2^{k+1}/(k+2)!$","#be6830","--")]:
    ax.plot(x,[r[field] for r in rows],label=label,color=color,ls=style,lw=2)
ax.set_yscale("log")
ax.set_xlabel(r"Number $k$ of input increments")
ax.set_ylabel(r"$-\log_2(\mathrm{retained\ coefficient})$")
ax.set_xticks([1,2,4,6,8,10,12,14,16,18,20])
ax.grid(True,which="major",alpha=.22)
ax.legend(loc="upper left",frameon=False,fontsize=8.7)
ax.set_title("Local phase removal: exact finite guarantee and local-scale limits",
             loc="left",fontweight="bold",fontsize=11,pad=13)
fig.tight_layout()
fig.savefig(figures/"localization_constants.pdf",bbox_inches="tight")
fig.savefig(figures/"localization_constants.png",bbox_inches="tight",dpi=190)
print("Wrote figures/localization_constants.pdf and data/localization_constants.csv")

