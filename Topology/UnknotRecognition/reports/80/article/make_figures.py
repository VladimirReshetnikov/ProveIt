"""Render the exact schematic models and recorded paired timing medians."""
from pathlib import Path
from fractions import Fraction
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "figures"
OUT.mkdir(exist_ok=True)
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9, "axes.titlesize": 11,
    "axes.labelsize": 9, "pdf.fonttype": 42, "svg.fonttype": "none",
    "axes.spines.top": False, "axes.spines.right": False,
})
INK, TEAL, GOLD = "#163449", "#087f8c", "#bd651e"

def simple_axes(ax):
    ax.set_aspect("equal")
    ax.set_xlim(-.075, 1.1)
    ax.set_ylim(-.075, 1.1)
    ax.axis("off")

fig, axes = plt.subplots(1, 2, figsize=(9.5, 4.55))
a = axes[0]
cells = [
    ([(0,0),(.5,0),(1/3,1/3),(0,.5)], "#d2eeee"),
    ([(.5,0),(1,0),(.5,.5),(1/3,1/3)], "#e1e7f2"),
    ([(0,.5),(1/3,1/3),(.5,.5),(0,1)], "#faead7"),
]
for vertices, color in cells:
    a.add_patch(Polygon(vertices, closed=True, facecolor=color,
                        edgecolor=INK, linewidth=1.1))
essential = [(0,0),(.5,0),(0,.5),(1/3,1/3)]
inessential = [(1,0),(0,1),(.5,.5)]
a.scatter(*zip(*essential), s=38, color=TEAL, zorder=4,
          label="Essential disc ray")
a.scatter(*zip(*inessential), s=38, color=GOLD, marker="s", zorder=4,
          label="Inessential disc ray")
a.text(.09,.15, r"$x$ largest", color=INK)
a.text(.60,.12, r"$u$ largest", color=INK)
a.text(.08,.66, r"$v$ largest", color=INK)
for point, text, offset in [
    ((0,0),r"$(1,0,0)$",(-24,-16)),
    ((1,0),r"$(0,1,0)$",(-14,-16)),
    ((0,1),r"$(0,0,1)$",(-12,8)),
    ((1/3,1/3),r"$(1,1,1)/3$",(6,-11)),
]:
    a.annotate(text, point, xytext=offset, textcoords="offset points",
               fontsize=8, color=INK)
simple_axes(a)
a.set_title("Geometric family: 7 rays for every n", loc="left",
            fontweight="bold", color=INK, pad=12)
a.legend(loc="lower center", bbox_to_anchor=(.48,-.11),
         frameon=False, ncol=1, fontsize=8)

b=axes[1]
m=5
cuts=[Fraction(2*j+1,8*m) for j in range(m-1)]
points={(Fraction(0),Fraction(0)),(Fraction(1),Fraction(0)),
        (Fraction(0),Fraction(1))}
points.update((x,y) for x in cuts for y in cuts)
for x in cuts: points.update([(x,Fraction(0)),(x,1-x),
                             (Fraction(0),x),(1-x,x)])
assert len(points)==m*m+2*m
poly=[(0,0),(1,0),(0,1)]
b.add_patch(Polygon(poly,closed=True,facecolor="#f8fafc",edgecolor=INK,lw=1.2))
for cut in cuts:
    x=float(cut)
    b.plot([x,x],[0,1-x],color=TEAL,lw=.9)
    b.plot([0,1-x],[x,x],color=GOLD,lw=.9)
b.scatter(*zip(*[(float(x),float(y)) for x,y in points]),
          s=11,color=INK,zorder=4)
b.add_patch(Rectangle((0,0),.205,.205,fill=False,edgecolor="#6d7780",
                       linestyle="--",lw=.8))
inset=b.inset_axes([.45,.25,.36,.36])
for cut in cuts:
    x=float(cut)
    inset.axvline(x,color=TEAL,lw=.8)
    inset.axhline(x,color=GOLD,lw=.8)
inset.scatter(*zip(*[(float(x),float(y)) for x,y in points
                     if 0<=x<=Fraction(205,1000) and 0<=y<=Fraction(205,1000)]),
              s=11,color=INK,zorder=4)
inset.set(xlim=(0,.205),ylim=(0,.205),xticks=[],yticks=[])
inset.set_aspect("equal")
inset.set_title("16 interior crossings",fontsize=8,pad=4)
simple_axes(b)
b.set_title("Abstract grid: m = 5, 35 rays",loc="left",
            fontweight="bold",color=INK,pad=12)
b.text(.16,-.1,"Two active groups; no triangulation realization claimed",
       fontsize=8,color=INK,ha="left")
fig.subplots_adjust(left=.045,right=.985,bottom=.16,top=.90,wspace=.16)
fig.savefig(OUT/"minimum_diagrams.pdf",bbox_inches="tight")
fig.savefig(OUT/"minimum_diagrams.png",dpi=180,bbox_inches="tight")
plt.close(fig)

data=json.loads((ROOT.parent/"evidence/benchmark_summary.json").read_text())
fig, axes=plt.subplots(1,2,figsize=(9.3,4.0),sharey=True)
for ax,key,title in zip(axes,["full","postkernel"],
                       ["Construction + complete enumeration",
                        "Complete enumeration on the same kernel"]):
    completed=[c for c in data["main"]
               if c[key]["paired_speed_comparison_supported"]]
    ax.plot([c["n"] for c in completed],
            [c[key]["incumbent_median_ms"] for c in completed],
            "o-",color=GOLD,lw=1.6,ms=4,label="Incumbent arrangement")
    ax.plot([c["n"] for c in data["main"]],
            [c[key]["planar_median_ms"] for c in data["main"]],
            "o-",color=TEAL,lw=1.6,ms=4,label="Planar minimum diagrams")
    ax.scatter([32],[40000],marker="^",s=55,color=GOLD,zorder=4)
    ax.annotate("40 s completion cap",(32,40000),
                xytext=(-4,12),textcoords="offset points",
                ha="right",fontsize=8,color=GOLD)
    ax.set_xscale("log",base=2);ax.set_yscale("log")
    ax.set_xticks([1,2,4,8,16,32],labels=["1","2","4","8","16","32"])
    ax.set_xlim(.8,41);ax.set_ylim(1,120000)
    ax.grid(axis="y",which="major",alpha=.17)
    ax.set_xlabel("Base tetrahedra n (total t = n + 2)")
    ax.set_title(title,color=INK,fontsize=10,pad=12)
axes[0].set_ylabel("Median wall time (ms, logarithmic scale)")
axes[0].legend(loc="upper left",fontsize=8,frameon=False)
fig.tight_layout(w_pad=2.2)
fig.savefig(OUT/"paired_times.pdf",bbox_inches="tight")
fig.savefig(OUT/"paired_times.png",dpi=180,bbox_inches="tight")
plt.close(fig)
print("Rendered exact diagram models and paired timing charts.")
