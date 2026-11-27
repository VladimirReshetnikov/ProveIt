#!/usr/bin/env python3
"""Rebuild publication figures and exact-data tables. Requires matplotlib/numpy."""
from pathlib import Path
import csv
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from cycle_laws import cycle_chi_square, cycle_tv

ROOT = Path(__file__).resolve().parents[1]
FIG = ROOT / "figures"
DATA = ROOT / "results"
FIG.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9,
    "axes.titlesize": 10,
    "axes.labelsize": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "savefig.bbox": "tight",
})
teal, orange, purple, blue = "#147d92", "#d47432", "#81559d", "#3e6294"

fig, axes = plt.subplots(1, 2, figsize=(7.2, 3.0), constrained_layout=True)
I = np.linspace(0, 16, 500)
profile = [math.erf(math.sqrt(x)/(2*math.sqrt(2))) for x in I]
axes[0].plot(I, profile, color=teal, lw=2.2)
for x in (1,4,9):
    y=math.erf(math.sqrt(x)/(2*math.sqrt(2)))
    axes[0].scatter([x],[y],color=teal,s=18)
    axes[0].annotate(f"{y:.3f}",(x,y),xytext=(5,-14),textcoords="offset points",fontsize=8)
axes[0].set(xlabel="Total cycle information  I", ylabel="Limiting total variation",
            title="A. Sharp detection profile",xlim=(0,16),ylim=(0,1.02))
axes[0].grid(alpha=.17)
rows=[]
for ell,color,style in [(3,teal,"-"),(4,orange,"--"),(5,purple,"-"),(6,blue,"--")]:
    ns=list(range(1,9))
    values=[]
    for n in ns:
        q=3;N=q**(2*n);r=(ell-1)//2
        info=cycle_chi_square(q,n,ell)
        scaled=info*N**(2*r)/(q-1)**(2*r+1)
        values.append(float(scaled))
        rows.append({"q":q,"n":n,"ambient_dimension":2*n,"cycle_length":ell,
                     "information_exact":str(info),"tv_exact":str(cycle_tv(q,n,ell)),
                     "scaled_information_exact":str(scaled),
                     "scaled_information_decimal":float(scaled)})
    axes[1].plot([2*n for n in ns],values,style,color=color,lw=1.8,
                 marker="o",ms=3,label=f"length {ell}")
axes[1].axhline(1,color="#777777",lw=.8,ls=":")
axes[1].set(xlabel="Ambient dimension  2n",ylabel="Information / leading term",
            title=r"B. Paired lengths over $\mathbb{F}_3$",xlim=(1.5,16.5),ylim=(.9,8.0))
axes[1].set_yscale("log")
axes[1].set_yticks([1,2,4,8],labels=["1","2","4","8"])
axes[1].grid(alpha=.17)
axes[1].legend(frameon=False,fontsize=7.5,ncol=2)
fig.savefig(FIG/"detection_profile.pdf")
fig.savefig(FIG/"detection_profile.png",dpi=220)
plt.close(fig)
with (DATA/"cycle_information.csv").open("w",newline="") as f:
    w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)

fig,axes=plt.subplots(1,2,figsize=(7.2,2.5),constrained_layout=True)
def draw(ax,positions,edges,color):
    for i,j in edges:
        x,y=positions[i],positions[j]
        ax.plot([x[0],y[0]],[x[1],y[1]],color=color,lw=1.8,zorder=1)
    for x,y in positions:
        ax.scatter(x,y,s=45,color=color,edgecolor="white",linewidth=.6,zorder=3)
    ax.set_aspect("equal");ax.axis("off")
positions=[(0,0),(-1,1),(-2,0),(-1,-1),(1,1),(2,0),(1,-1)]
edges=[(0,1),(1,2),(2,3),(3,0),(0,4),(4,5),(5,6),(6,0)]
draw(axes[0],positions,edges,teal)
axes[0].set_title("Cactus: independent cycle blocks",pad=10)
axes[0].text(0,-1.4,"A shared vertex preserves block independence.",ha="center",fontsize=8)
positions=[(-1,.8),(-1,-.8)]+[(1,y) for y in np.linspace(-1.2,1.2,5)]
edges=[(i,j) for i in [0,1] for j in range(2,7)]
draw(axes[1],positions,edges,orange)
axes[1].set_title(r"$K_{2,m}$: overlapping cycles",pad=10)
axes[1].text(0,-1.65,"Rare proportional anchors change the analysis.",ha="center",fontsize=8)
fig.savefig(FIG/"observation_graphs.pdf")
fig.savefig(FIG/"observation_graphs.png",dpi=220)
plt.close(fig)
print("Generated two PDF/PNG figures and cycle_information.csv.")

