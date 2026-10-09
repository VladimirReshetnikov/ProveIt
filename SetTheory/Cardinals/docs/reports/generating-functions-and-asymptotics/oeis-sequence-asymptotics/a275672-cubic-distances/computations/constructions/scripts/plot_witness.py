#!/usr/bin/env python3
"""Render a point certificate and its exact squared-distance inventory."""
import itertools
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np
from verify import verify

ROOT=Path(__file__).resolve().parent.parent
record=json.loads((ROOT/"data/original_witnesses/n8.json").read_text())
certificate=verify(record)
points=np.array(certificate["points"])
n,k=record["n"],record["k"]
spectrum={x*x+y*y+z*z for x in range(n) for y in range(n) for z in range(n)}-{0}
used=set(certificate["squared_distances"])
blue="#174A73";orange="#C17135";gray="#B6BEC5"
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10})
fig=plt.figure(figsize=(10.8,4.8),constrained_layout=True)
ax=fig.add_subplot(1,2,1,projection="3d")
ax.scatter(*points.T,s=42,c=blue,depthshade=False)
for i,p in enumerate(points,1):
    ax.text(p[0]+.11,p[1]+.1,p[2]+.12,str(i),fontsize=8,color=blue)
for varying in range(3):
    for fixed in itertools.product((0,n-1),repeat=2):
        endpoints=[]
        for value in (0,n-1):
            p=list(fixed);p.insert(varying,value);endpoints.append(p)
        edge=np.array(endpoints)
        ax.plot(*edge.T,color=gray,linewidth=.6,alpha=.7)
ax.set(xlim=(-.2,n-.6),ylim=(-.2,n-.6),zlim=(-.2,n-.6),
       xlabel="$x$",ylabel="$y$",zlabel="$z$",
       xticks=range(0,n,2),yticks=range(0,n,2),zticks=range(0,n,2))
ax.set_box_aspect((1,1,1));ax.view_init(elev=22,azim=-59)
ax.set_title("Twelve certified lattice points",pad=6)
ax2=fig.add_subplot(1,2,2)
for d in sorted(spectrum):
    ax2.plot([d,d],[0,1],color=blue if d in used else gray,
             linewidth=2.2 if d in used else 1.5,solid_capstyle="butt")
ax2.set(xlim=(0,3*(n-1)**2+1),ylim=(-.28,1.3),yticks=[],
        xlabel="Squared distance",title="All 66 pairs have different distances")
ax2.set_xticks(range(0,151,25))
ax2.spines[["top","left","right"]].set_visible(False)
ax2.spines["bottom"].set_position(("data",-.03))
ax2.tick_params(axis="x",direction="out")
ax2.legend(handles=[Line2D([0],[0],color=blue,lw=2.5,label="Used by the certificate (66)"),
                    Line2D([0],[0],color=gray,lw=2.5,label="Possible in the grid, unused (21)")],
           loc="upper left",bbox_to_anchor=(0,1.0),frameon=False,fontsize=9)
fig.suptitle("A 12-point unique-distance subset of the $8\\times8\\times8$ grid",fontsize=13)
for suffix in ("png","pdf","svg"):
    fig.savefig(ROOT/"figures"/f"witness_n8.{suffix}",dpi=220,bbox_inches="tight")
