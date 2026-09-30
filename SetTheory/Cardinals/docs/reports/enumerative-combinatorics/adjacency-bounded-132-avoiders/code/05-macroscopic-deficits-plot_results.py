"""Rebuild the manuscript's figures from retained exact-count CSV files."""
from __future__ import annotations
import csv, math, pathlib
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
ROOT=pathlib.Path(__file__).resolve().parents[1]
rows=list(csv.DictReader((ROOT/'data/bulk_counts.csv').open()))
x=np.linspace(.10,.60,600)
y=np.zeros_like(x);mask=x<.5
y[mask]=3/math.sqrt(math.pi)*(1-2*x[mask])/np.sqrt(x[mask]*(1-x[mask]))
fig,ax=plt.subplots(figsize=(6.3,3.9))
ax.plot(x,y,label=r'Proved profile $\Phi(x)$',linewidth=1.8)
for n,marker in ((40,'o'),(80,'s'),(160,'^'),(320,'D')):
    rs=[r for r in rows if int(r['n'])==n]
    ax.plot([int(r['d'])/n for r in rs],[float(r['scaled_probability']) for r in rs],
            marker=marker,linestyle='none',label=f'Exact counts, n = {n}',markersize=5)
ax.set_xlabel(r'Deficit fraction $x=d/n$')
ax.set_ylabel(r'$\sqrt{n}\,\mathbb{P}(D_n\geq d)$')
ax.set_xlim(.10,.60);ax.set_ylim(0,4.9)
ax.grid(alpha=.22);ax.legend(frameon=False,fontsize=8.5)
fig.tight_layout();fig.savefig(ROOT/'figures/bulk_profile.pdf');fig.savefig(ROOT/'figures/bulk_profile.png',dpi=160);plt.close(fig)
rows=list(csv.DictReader((ROOT/'data/moment_counts.csv').open()))
fig,ax=plt.subplots(figsize=(6.3,3.35))
ax.plot([int(r['n']) for r in rows],[float(r['scaled_mean']) for r in rows],'o-',label='Exact counts')
ax.axhline(3/math.sqrt(math.pi),linestyle='--',label=r'Proved limit $3/\sqrt{\pi}$')
ax.set_xlabel(r'Permutation size $n$');ax.set_ylabel(r'$\mathbb{E}D_n/\sqrt{n}$')
ax.set_xlim(15,85);ax.set_ylim(1.15,1.77);ax.grid(alpha=.22);ax.legend(frameon=False,fontsize=9)
fig.tight_layout();fig.savefig(ROOT/'figures/mean_constant.pdf');fig.savefig(ROOT/'figures/mean_constant.png',dpi=160);plt.close(fig)
print('Figures written.')
