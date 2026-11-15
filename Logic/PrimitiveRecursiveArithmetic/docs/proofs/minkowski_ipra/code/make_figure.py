#!/usr/bin/env python3
"""Render the exact two-dimensional example used in the paper."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import numpy as np

out = Path(__file__).resolve().parents[1] / "paper"
fig, ax = plt.subplots(1, 2, figsize=(9.4, 4.0))
navy, teal, orange = "#18364c", "#147d92", "#c66a26"
for a in ax:
    a.set_aspect("equal")
    a.spines[["top", "right"]].set_visible(False)
    a.spines[["left", "bottom"]].set_color("#c4ccd3")
    a.tick_params(labelsize=9, colors=navy)
    a.axhline(0, color="#bbc6cf", lw=.7, zorder=0)
    a.axvline(0, color="#bbc6cf", lw=.7, zorder=0)

a = ax[0]
a.add_patch(Rectangle((-.75,-.75),1.5,1.5,facecolor="#eef5f8",edgecolor=navy,lw=1.4))
for t in np.arange(-.75,1,.25):
    a.plot([t,t],[-.75,.75], color="#c4d4dd", lw=.7)
    a.plot([-.75,.75],[t,t], color="#c4d4dd", lw=.7)
for y in [-.75,.25]:
    a.add_patch(Rectangle((-.75,y),.25,.25,facecolor=teal,alpha=.2,edgecolor=teal,lw=1.2))
c,d = (-.625,.375),(-.625,-.625)
a.scatter(*zip(c,d),c=teal,s=36,zorder=5)
a.annotate("",xy=c,xytext=d,arrowprops=dict(arrowstyle="->",lw=1.8,color=teal))
a.text(-.54,.40,r"$c=(-5/8,\,3/8)$",fontsize=10,color=navy)
a.text(-.54,-.64,r"$d=(-5/8,\,-5/8)$",fontsize=10,color=navy)
a.text(.12,-.10,r"$c-d=(0,1)$",fontsize=11,color=teal)
a.set_title(r"$K/2$: 36 cells, 16 residue classes",loc="left",fontsize=11,color=navy,pad=13)
a.set_xlim(-.91,.91); a.set_ylim(-.91,.91)
a.set_xticks([-.75,0,.75]); a.set_yticks([-.75,0,.75])
a.set_xlabel(r"Mesh $m=4$; the marked cell indices agree modulo $4$",fontsize=9,color=navy,labelpad=10)

a=ax[1]
a.add_patch(Rectangle((-1.5,-1.5),3,3,facecolor="#eef5f8",edgecolor=navy,lw=1.4))
u,v=(-1.25,.75),(1.25,1.25)
a.plot([u[0],v[0]],[u[1],v[1]],color=teal,lw=1.8)
a.scatter(*zip(u,v),c=teal,s=36,zorder=5)
a.scatter([0],[1],s=62,c=orange,zorder=6)
a.text(-1.48,.51,r"$2c$",fontsize=11,color=navy)
a.text(1.02,1.39,r"$-2d$",fontsize=11,color=navy)
a.text(.10,.72,r"$z=(0,1)$",fontsize=11,color=orange)
a.text(-1.03,-.90,r"$z=\frac{2c+(-2d)}{2}\ \in K$",fontsize=14,color=navy)
a.set_title(r"$K$: symmetry followed by one midpoint",loc="left",fontsize=11,color=navy,pad=13)
a.set_xlim(-1.75,1.75);a.set_ylim(-1.75,1.75)
a.set_xticks([-1.5,0,1.5]);a.set_yticks([-1.5,0,1.5])
a.set_xlabel(r"$K=[-3/2,\,3/2]^2$",fontsize=10,color=navy,labelpad=10)
fig.tight_layout(w_pad=3.0)
fig.savefig(out/"finite_minkowski.pdf",bbox_inches="tight")
fig.savefig(out/"finite_minkowski.png",dpi=160,bbox_inches="tight")
