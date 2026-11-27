#!/usr/bin/env python3
"""Reproduce the scientific figure from exact proved formulas."""
from fractions import Fraction as F
from pathlib import Path
import csv

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

root=Path(__file__).resolve().parents[1]
(root/"figures").mkdir(exist_ok=True)
(root/"results").mkdir(exist_ok=True)
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,
                     "axes.spines.top":False,"axes.spines.right":False,
                     "pdf.fonttype":42,"ps.fonttype":42})
blue="#155e75"; gold="#b7791f"; red="#b45353"
fig,axes=plt.subplots(1,2,figsize=(10.4,3.65),layout="constrained")
v=np.arange(8)
h=np.array([float(F(4,5)*sum((F(1,2)**r for r in range(int(j)+1)),F(0))) for j in v])
axes[0].plot(v,h,"o-",color=blue,linewidth=2,label="Full 2-adic likelihood")
axes[0].axhline(1,color="#52616b",linestyle="--",linewidth=1.2,label="Independent-entry likelihood")
axes[0].hlines(F(4,3),.7,7.2,color=gold,linestyle=":",linewidth=2,label="Uniform lift on odd determinant")
axes[0].fill_between(v,1,h,where=h>1,color=blue,alpha=.12)
axes[0].set(xlabel=r"Valuation $v_2(1-\det A)$",ylabel="Likelihood relative to independent entries",
            title=r"Likelihood varies within the first residue class",xticks=v,ylim=(.73,1.72))
axes[0].legend(loc="lower right",fontsize=7.3,frameon=False)
k=np.arange(1,8)
delta=np.array([float(F(1,10*4**int(j))) for j in k])
axes[1].semilogy(k,np.full(len(k),.125),"s-",color=blue,linewidth=2,label="Distance from independent entries")
axes[1].semilogy(k,delta,"o-",color=gold,linewidth=2,label="Error after uniform completion")
axes[1].set(xlabel="Number of exact digits retained",ylabel="Total variation distance",
            title=r"Exact precision hierarchy ($q=2$, $g=2$)",xticks=k)
axes[1].grid(axis="y",which="major",alpha=.18)
axes[1].legend(loc="lower left",fontsize=7.4,frameon=True,framealpha=.95,edgecolor="none")
fig.savefig(root/"figures"/"precision_laws.pdf",bbox_inches="tight")
fig.savefig(root/"figures"/"precision_laws.png",dpi=180,bbox_inches="tight")
with (root/"results"/"figure_values.csv").open("w",newline="") as f:
    w=csv.writer(f);w.writerow(["index","likelihood_at_defect_valuation_index","iid_tv","uniform_completion_error_after_index_digits"])
    for j in range(1,8):
        w.writerow([j,str(F(4,5)*sum((F(1,2)**r for r in range(j+1)),F(0))),"1/8",str(F(1,10*4**j))])

