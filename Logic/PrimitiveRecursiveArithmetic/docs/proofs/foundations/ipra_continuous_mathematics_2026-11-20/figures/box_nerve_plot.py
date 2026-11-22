"""Regenerate box_nerve.pdf using Matplotlib."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

blue, amber, light = "#165879", "#99491c", "#d9e9ee"
fig, (space, nerve) = plt.subplots(1, 2, figsize=(6.7, 2.45), constrained_layout=True)

space.set_aspect("equal")
for x, y, w, h in [(0,0,3,1), (2,0,1,3), (0,2,3,1), (0,0,1,3)]:
    space.add_patch(Rectangle((x,y),w,h,fc=blue,ec=blue,alpha=.19,lw=1))
for i, (x,y) in enumerate([(1.5,.5), (2.5,1.5), (1.5,2.5), (.5,1.5)], 1):
    space.text(x,y,str(i),ha="center",va="center",fontsize=10,color=blue,weight="bold")
space.text(1.5, 1.5, "hole", ha="center", va="center", fontsize=8, color="0.43")
space.scatter([1], [0], s=26, c=amber, zorder=8)
space.annotate("$G(y)$", (1,0), (1.18,-.21), color=amber, fontsize=8)
space.set(xticks=[0,1,2,3],yticks=[0,1,2,3],xlim=(-.06,3.06),ylim=(-.28,3.06),
          title="The four closed bars")
space.spines[["top","right"]].set_visible(False)
space.tick_params(labelsize=8)

nerve.set_aspect("equal")
nerve.plot([0,1,1,0,0],[0,0,1,1,0],c=blue,lw=1.6)
nerve.plot([.25,0],[0,.5],ls="--",color="0.58",lw=1)
nerve.plot([.25,0,0],[0,0,.5],color=amber,lw=3)
nerve.scatter([0,1,1,0],[0,0,1,1],c=blue,s=26,zorder=3)
for i, (x,y,ha) in enumerate([(-.035,-.085,"right"),(1.03,-.085,"left"),
                                (1.03,1.02,"left"),(-.035,1.02,"right")], 1):
    nerve.text(x,y,str(i),color=blue,ha=ha,fontsize=9,weight="bold")
nerve.scatter([.25,0],[0,.5],c=amber,s=23,zorder=4)
nerve.text(.27,-.095,"$y$",fontsize=9,color=amber)
nerve.text(-.04,.51,"$FG(y)$",ha="right",va="center",fontsize=9,color=amber)
nerve.set(xlim=(-.32,1.12),ylim=(-.18,1.12),title="The nerve and the homotopy path")
nerve.axis("off")
for ax in (space,nerve):
    ax.title.set_fontsize(10)
fig.savefig(Path(__file__).with_name("box_nerve.pdf"),bbox_inches="tight")
