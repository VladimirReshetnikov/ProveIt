#!/usr/bin/env python3
"""Reproduce the two research figures; these are plots of exact formulas."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans', 'font.size':10,
                     'axes.spines.top':False, 'axes.spines.right':False,
                     'axes.labelcolor':'#243447', 'text.color':'#243447',
                     'axes.edgecolor':'#8a969f', 'savefig.bbox':'tight'})

d = np.linspace(0,.36,500)
baseline = 1-d
strong = np.maximum.reduce([baseline,1.6-4*d,2.4-12*d])
fig, ax = plt.subplots(figsize=(7.2,3.6))
ax.fill_between(d,baseline,strong,color='#d9ecec',label='Improvement from Pluecker relations')
ax.plot(d,strong,color='#087f8c',lw=2.5,label='Proved lower bound')
ax.plot(d,baseline,color='#7a8792',lw=1.7,ls='--',label='Integrality alone')
ax.scatter([0,.1,.2,.3],[2.4,1.2,.8,.7],color='#17334b',zorder=5,
           label='Exact equality examples (r=2, n=5)')
ax.set(xlabel=r'Fraction of vanishing maximal minors, $\delta=z/\binom{n}{r}$',
       ylabel=r'Lower bound for $\det(AA^T)/(D^2\binom{n}{r})$',xlim=(-.006,.36),ylim=(.58,2.55))
ax.grid(axis='y',alpha=.15)
ax.legend(frameon=False,fontsize=8.5,loc='upper right')
fig.tight_layout()
fig.savefig(OUT/'determinant_bound.pdf')
fig.savefig(OUT/'determinant_bound.png',dpi=180)
plt.close(fig)

data=json.loads((ROOT/'artifacts/certificate_results.json').read_text())
scan=data['K_scan']
ks=[row['K'] for row in scan]
miss=[float(row['missing_bound_decimal']) for row in scan]
fig,(ax, bx)=plt.subplots(1,2,figsize=(8,3.2),gridspec_kw={'width_ratios':[1.05,1.3]})
centers=[1,.5,.25]; radii=[.05,.025,.0125]; mult=[1,2,1]
for a,r,m in zip(centers,radii,mult):
    ax.axvspan(a-r,a+r,color='#d9ecec')
    ax.scatter([a],[m],s=55,color='#087f8c',zorder=3)
    ax.vlines(a,0,m,color='#087f8c',lw=1.7)
tail=2.**(-np.arange(4,13))
ax.scatter(tail,np.ones(len(tail)),s=12,color='#8b98a2')
ax.axvline(.125,color='#cc6b38',ls='--',label=r'Threshold $1/8$')
ax.set(xlabel='Spectral value x',ylabel='Multiplicity',xlim=(-.02,1.08),ylim=(0,2.3),yticks=[0,1,2])
ax.legend(frameon=False,fontsize=8,loc='upper right')
bx.semilogy(ks,miss,'o-',color='#087f8c',ms=4,lw=1.6,label='Bound for missed count')
bx.axhline(1,color='#cc6b38',ls='--',label='Integer exclusion threshold')
bx.set(xlabel='First moment order K',ylabel='Certified upper bound')
bx.grid(axis='y',alpha=.15)
bx.legend(frameon=False,fontsize=8,loc='upper right')
fig.tight_layout()
fig.savefig(OUT/'certificate_example.pdf')
fig.savefig(OUT/'certificate_example.png',dpi=180)
plt.close(fig)
print('Created determinant_bound and certificate_example in PDF and PNG.')
