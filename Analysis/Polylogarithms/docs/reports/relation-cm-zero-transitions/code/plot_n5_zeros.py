"""Plot the certified fifth-index zero locations; no numerical root finding."""
from fractions import Fraction
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, FuncFormatter

HERE = Path(__file__).resolve().parent
DATA = json.loads((HERE.parent/"data"/"n5_zero_certificates.json").read_text())
OUT = HERE.parent/"figures"
OUT.mkdir(exist_ok=True)
ROWS = {}
for row in DATA["certificates"]:
    lower, upper = map(Fraction, row["root_bracket"])
    assert upper-lower == Fraction(1,10**16)
    ROWS.setdefault(row["k"],[]).append((row["j"],(lower+upper)/2))
for k in ROWS:
    ROWS[k].sort()

plt.rcParams.update({
    "font.family":"DejaVu Sans",
    "font.size":9.5,
    "axes.titlesize":10.5,
    "axes.labelsize":10,
    "xtick.labelsize":8.5,
    "ytick.labelsize":9,
    "pdf.fonttype":42,
    "ps.fonttype":42,
    "axes.spines.top":False,
    "axes.spines.right":False,
})
COLORS={1:"#1D4ED8",2:"#0F766E",3:"#A16207"}
fig,axes=plt.subplots(
    1,2,figsize=(8.5,3.7),sharey=True,
    gridspec_kw={"width_ratios":[1,1.48],"wspace":0.16})
fig.subplots_adjust(left=0.115,right=0.982,bottom=0.205,top=0.77)
fig.suptitle("Fifth Stieltjes index: 3, 3, then 5 positive zeros",
             x=0.115,y=0.96,ha="left",fontsize=13,weight="semibold",
             color="#111827")
fig.text(0.115,0.878,"Certified locations for "+r"$\gamma_5^{(k)}(a)$"+
         " at derivative orders "+r"$k=1,2,3$",
         fontsize=10,color="#4B5563")

for ax in axes:
    ax.set_ylim(0.48,3.62)
    ax.set_yticks([1,2,3])
    ax.set_yticklabels([r"$k=1$"+"  (3)",r"$k=2$"+"  (3)",r"$k=3$"+"  (5)"])
    ax.tick_params(axis="y",length=0,pad=8)
    ax.grid(axis="x",color="#E5E7EB",linewidth=.7)
    ax.set_axisbelow(True)
    ax.spines["left"].set_visible(False)
    ax.spines["bottom"].set_color("#9CA3AF")
    for k in (1,2,3):
        ax.axhline(k,color="#E5E7EB",linewidth=.9,zorder=0)
    ax.set_xlabel(r"Positive parameter $a$",labelpad=7)

left,right=axes
left.set_title("Detail near 1",loc="left",pad=13)
left.set_xlim(.82,2.3)
left.set_xticks([1,1.5,2])
right.set_title("All positive zeros",loc="left",pad=13)
right.set_xscale("log")
right.set_xlim(.80,450)
right.xaxis.set_major_locator(FixedLocator([1,2,5,10,50,100,400]))
right.xaxis.set_major_formatter(FuncFormatter(lambda x,pos:f"{x:g}"))
right.minorticks_off()

for k in (1,2,3):
    vals=[float(midpoint) for _,midpoint in ROWS[k]]
    for ax in axes:
        visible=[x for x in vals if ax.get_xlim()[0]<x<ax.get_xlim()[1]]
        ax.scatter(visible,[k]*len(visible),s=31,c=COLORS[k],
                   edgecolors="white",linewidths=.75,zorder=4)
    for x in vals:
        if .82<x<2.3:
            above = k == 3 and x < 1
            left.annotate(f"{x:.3f}",(x,k),xytext=(0,11 if above else -15),
                          textcoords="offset points",ha="center",
                          va="bottom" if above else "top",
                          fontsize=8.2,color=COLORS[k])
        else:
            right.annotate(f"{x:.3f}",(x,k),xytext=(0,-15),
                           textcoords="offset points",ha="center",va="top",
                           fontsize=8.2,color=COLORS[k])
right.text(1.6,3.33,"3 close roots",ha="center",fontsize=8,color=COLORS[3])
right.text(1.6,2.33,"2 close roots",ha="center",fontsize=8,color=COLORS[2])
right.text(1.6,1.33,"3 close roots",ha="center",fontsize=8,color=COLORS[1])

fig.text(.115,.060,
         "Markers show exact rational bracket midpoints; each bracket has width "+
         r"$10^{-16}$"+", below plotting resolution.",
         fontsize=8.2,color="#4B5563")
fig.text(.115,.017,
         "The global theorem and critical-point sign certificates prove completeness and simplicity.",
         fontsize=8.2,color="#4B5563")
pdf=OUT/"n5_certified_zero_locations.pdf"
png=OUT/"n5_certified_zero_locations.png"
fig.savefig(pdf,metadata={"Title":"Certified fifth-index Stieltjes derivative zero locations"})
fig.savefig(png,dpi=220)
plt.close(fig)
print(pdf)
print(png)
