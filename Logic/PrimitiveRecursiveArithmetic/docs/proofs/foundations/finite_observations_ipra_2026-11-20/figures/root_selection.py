"""Reproduce the explanatory figure. The bracket endpoints are computed exactly."""
from fractions import Fraction
from pathlib import Path
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "examples"))
from topology_crossing import shrink

plt.rcParams.update({"font.size": 9, "pdf.fonttype": 42, "font.family": "DejaVu Sans",
                     "axes.spines.top": False, "axes.spines.right": False})
teal, rust, grey = "#15606d", "#a14a30", "#6c7580"
fig, (left, right) = plt.subplots(1, 2, figsize=(7.45, 2.55))
fig.subplots_adjust(left=.095, right=.982, bottom=.22, top=.82, wspace=.42)

nodes = [0, 1/3, 2/3, 1]
left.axhline(0, color="#abb2b5", linewidth=.8)
for shift, color, label in [(1/12, teal, r"$z=+1/12$"), (-1/12, rust, r"$z=-1/12$")]:
    vals = [min(3*t-1, 0)+max(3*t-2, 0)+shift for t in nodes]
    root = (1-shift)/3 if shift > 0 else (2-shift)/3
    left.plot(nodes, vals, color=color, linewidth=1.8, label=label)
    left.plot([root], [0], "o", color=color, markersize=4)
left.plot([1/3, 2/3], [0, 0], linestyle=":", color="#333333", linewidth=2, label=r"$z=0$ zeros")
left.set(xlim=(.22, .78), ylim=(-.38, .38), xlabel="Path parameter", ylabel=r"$f_z(t)$",
         xticks=[1/3, .5, 2/3], xticklabels=["1/3", "1/2", "2/3"], yticks=[-.25, 0, .25])
left.set_title("A flat interval of zeros", loc="left", fontsize=10, fontweight="bold")
left.legend(loc="upper left", ncol=1, frameon=False, fontsize=7, handlelength=1.6, labelspacing=.18)

lo, hi = Fraction(0), Fraction(1)
for j in range(9):
    if j in (0, 1, 2, 4, 6, 8):
        right.plot([float(lo),float(hi)],[j,j],color=teal,linewidth=2.8,solid_capstyle="butt")
        right.plot([float(lo),float(hi)],[j,j],"|",color=teal,markersize=6)
    lo, hi = shrink(lo, hi)
for t in (.25,.5,.75):
    right.axvline(t,ls=":",color=rust if t==.25 else grey,lw=1,zorder=0)
right.set(xlim=(-.025,1.025),ylim=(8.7,-.65), xlabel="Path parameter", ylabel="Number of cuts",
          xticks=[0,.25,.5,.75,1], xticklabels=["0","1/4","1/2","3/4","1"], yticks=[0,2,4,6,8])
right.set_title("Brackets for the circle example",loc="left",fontsize=10,fontweight="bold")
for ax in (left,right):
    ax.tick_params(length=3, color=grey)
    ax.spines["left"].set_color(grey)
    ax.spines["bottom"].set_color(grey)
fig.savefig(HERE / "root_selection.pdf",metadata={"Title":"Root selection and crossing brackets"})
