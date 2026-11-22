"""Rebuild the manuscript's diagnostic figure with Matplotlib."""
import sys
from pathlib import Path
from fractions import Fraction as Q
from itertools import accumulate

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MultipleLocator

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root / "examples"))
from laws import ATOMS, DENSITY, read, true_ramp, reconstruct

n = r = 4
N = 2**n
grid = [i/N for i in range(N+1)]
ideal = [float(true_ramp(i, n)) for i in range(N)]
raw = [float(read(i,n,r)) for i in range(N)]
repair = list(accumulate((min(1,max(0,v)) for v in raw), max))
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":9,"axes.spines.top":False,"axes.spines.right":False,
                     "axes.labelcolor":"#243641","axes.edgecolor":"#8a989c","text.color":"#243641",
                     "xtick.color":"#42545d","ytick.color":"#42545d","pdf.fonttype":42})
fig, ax = plt.subplots(1,2,figsize=(8.3,2.8), layout="constrained")
blue, orange = "#155d75","#ae5427"
a=ax[0]
a.plot(grid[:-1], ideal, color="#505b60", lw=1.2, label="Exact probe")
a.scatter(grid[:-1], raw, marker="x", s=21, color=orange, label="Noisy reading", zorder=3)
a.step(grid[:-1],repair,where="post",color=blue,lw=1.5,label="Repaired value")
a.set(xlabel="Left endpoint of ramp",ylabel="Probe expectation",title="Cumulative observations")
a.legend(loc="upper left",frameon=False,fontsize=8)
a=ax[1]
sites=sorted({Q(0), Q(1), *(x for x, _ in ATOMS)})
xx=[]; yy=[]
for x in sites:
    before = DENSITY*x+sum(m for z,m in ATOMS if z<x)
    after = DENSITY*x+sum(m for z,m in ATOMS if z<=x)
    xx.extend([float(x),float(x)]); yy.extend([float(before),float(after)])
a.plot(xx,yy,color="#505b60",lw=1.7,label="Target distribution")
law,_=reconstruct(n,r,read)
ys=[float(sum(m for x,m in law if x<=Q(i,N))) for i in range(N+1)]
a.step(grid,ys,where="post",color=blue,lw=1.5,label="Reconstructed law")
a.set(xlabel="Position on the unit interval",ylabel="Cumulative mass",title="Distribution functions")
a.legend(loc="upper left",frameon=False,fontsize=8)
for a in ax:
    a.set(xlim=(-.025,1.025),ylim=(-.025,1.035))
    a.xaxis.set_major_locator(MultipleLocator(.25))
    a.yaxis.set_major_locator(MultipleLocator(.25))
    a.grid(axis="y",color="#e1e7e9",linewidth=.55)
    a.set_axisbelow(True)
fig.savefig(root/"figures"/"ramp-repair.pdf",metadata={"Title":"Cumulative probe repair and law reconstruction"})
