"""Draw the analytic images of the two straight segments in the lifting example."""
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

folder = Path(__file__).resolve().parent
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":8.5,"pdf.fonttype":42})
fig, axes = plt.subplots(1,2,figsize=(6.32,1.86))
colors = ["#14676b","#a25138"]
u = np.linspace(0,1,301)
parts = [(1-u)+1j*u, -u+1j*(1-u)]
for j, (ax,title) in enumerate(zip(axes,(r"Closed parameter loop  $z=w^2$",r"Lift starting at  $w=1$"))):
    ax.set_aspect("equal")
    ax.spines[:].set_visible(False)
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_title(title,loc="center",fontsize=9.5,pad=2,color="#1d3344")
    ax.axhline(0, color="#afb8ba", lw=.65, zorder=0)
    ax.axvline(0, color="#afb8ba", lw=.65, zorder=0)
    ax.set_xlim(-1.34,1.34)
    ax.set_ylim(-.70,1.18 if j else .70)
    for p,c in zip(parts,colors):
        curve = p if j else p*p
        ax.plot(curve.real,curve.imag,color=c,lw=1.9)
        a,b = curve[94],curve[111]
        ax.annotate("",xy=(b.real,b.imag),xytext=(a.real,a.imag),
                    arrowprops={"arrowstyle":"-|>","color":c,"lw":1.5,"mutation_scale":9})
    for x in (-1,1):
        ax.scatter([x],[0],s=13,color="#1d3344",zorder=3)
        ax.annotate(str(x).replace("-","−"),(x,0),xytext=(0,-12),textcoords="offset points",ha="center")
    if j:
        ax.scatter([0],[1],s=13,color="#1d3344",zorder=3)
        ax.annotate(r"$i$",(0,1),xytext=(6,0),textcoords="offset points")
    else:
        ax.scatter([0],[0],s=18,marker="x",color="#1d3344",zorder=3)
        ax.annotate(r"$0$",(0,0),xytext=(3,-10),textcoords="offset points")
fig.subplots_adjust(left=.03,right=.97,top=.84,bottom=.10,wspace=.24)
fig.savefig(folder/"square_root_lift.pdf",metadata={"Title":"A square-root lift over a closed parameter loop"})
