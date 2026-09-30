#!/usr/bin/env python3
"""Generate illustrative figures with Matplotlib's default palette."""
from pathlib import Path
import csv
import math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]

def theta(k: int,q: float,c: float|None=None)->float:
    if not 0<q<1: raise ValueError('Requires 0<q<1')
    a=1-q
    if c is None: c=math.log(k-1)
    lo=c;hi=c+10
    def e(t): return math.tanh((t-c)/2)-a/math.tanh(a*t/2)
    while e(hi)<0:hi=2*hi+1
    for _ in range(75):
        m=(lo+hi)/2
        if e(m)<0:lo=m
        else:hi=m
    t=(lo+hi)/2
    r=math.sinh(a*t/2)**2/math.cosh((t-c)/2)**2
    return q*r/(a+r)

qs=np.linspace(.004,.996,249)
ks=[2,3,17,18,64]
rows=[]
fig,ax=plt.subplots(figsize=(7.3,4.3))
for k in ks:
    vals=[theta(k,q) for q in qs]
    ax.plot(qs,vals,label=f'{k} symbols')
    rows.extend((k,float(q),v) for q,v in zip(qs,vals))
ax.axhline(1/3,linestyle='--',label='Three-factor boundary')
ax.set(xlabel='Entropy order q',ylabel=r'Maximum block curvature $\Theta_k(q)$',
       xlim=(0,1),ylim=(0,.51))
ax.legend(ncol=2,fontsize=9)
fig.tight_layout();fig.savefig(ROOT/'figures'/'alphabet_profiles.pdf');plt.close(fig)
with (ROOT/'data'/'alphabet_profiles.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['alphabet_size','q','theta_approx']);w.writerows(rows)
ls=np.linspace(.01,7,200)
fig,ax=plt.subplots(figsize=(7.3,4.3))
for c in [5.,10.,20.]:
    ax.plot(ls,[theta(2,1-l/c**2,c=c) for l in ls],label=fr'$\log(k-1)={c:g}$')
ax.plot(ls,ls/(4+ls),linestyle='--',label=r'Limit $\lambda/(4+\lambda)$')
ax.axhline(1/3,linestyle=':',label='Three-factor boundary')
ax.set(xlabel=r'Scaled distance from Shannon order: $\lambda=(1-q)\log^2(k-1)$',
       ylabel=r'$\Theta_k(q)$',xlim=(0,7),ylim=(0,.65))
ax.legend(fontsize=9)
fig.tight_layout();fig.savefig(ROOT/'figures'/'shannon_window.pdf');plt.close(fig)
print('Two figures and profile CSV generated. Plots are illustrative, not proof certificates.')
