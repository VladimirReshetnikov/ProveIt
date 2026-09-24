#!/usr/bin/env python3
"""Numerical illustrations, not proof certificates. Requires mpmath/matplotlib/numpy."""
from pathlib import Path
import csv
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=80

def boundaries(q):
    a=mp.mpf(q)-1
    if a<=0:
        raise ValueError('q must exceed one')
    pb=1/(2*(1+mp.power(2,1/a)))
    pc=1/(1+mp.exp(mp.acosh(mp.power(2,a))/a))
    return pb,pc

orders=['1.01','1.05','1.1','1.25','1.5','2','3','4','10','100']
rows=[]
for q in orders:
    pb,pc=boundaries(q)
    rows.append([q,mp.nstr(pb,18),mp.nstr(pc,18)])
with (ROOT/'results'/'phase_boundaries.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['q','p_boundary','p_center']);w.writerows(rows)
tex=['\\begin{tabular}{@{}rrr@{}}','\\toprule',
     '$q$ & $p_{\\mathrm{b}}(q)$ & $p_{\\mathrm{c}}(q)$ \\\\', '\\midrule']
for q,pb,pc in rows:
    def fmt(v):
        x=float(v)
        if x<1e-5:
            e=int(np.floor(np.log10(x)));return f'${x/10**e:.6f}\\times10^{{{e}}}$'
        return f'{x:.9f}'
    tex.append(q+' & '+fmt(pb)+' & '+fmt(pc)+' \\\\')
tex+=['\\bottomrule','\\end{tabular}']
(ROOT/'results'/'phase_table.tex').write_text('\n'.join(tex)+'\n')
qs=np.linspace(1.001,12,650)
pbs=[];pcs=[]
for q in qs:
    pb,pc=boundaries(str(q));pbs.append(float(pb));pcs.append(float(pc))
fig,ax=plt.subplots(figsize=(7.1,3.9))
ax.plot(qs,pbs,label=r'$p_{\mathrm{b}}(q)$: boundary / asymmetric',linewidth=1.8)
ax.plot(qs,pcs,label=r'$p_{\mathrm{c}}(q)$: asymmetric / balanced',linewidth=1.8)
ax.set(xlabel=r'Entropy order $q$',ylabel=r'Half-mean $p$',xlim=(1,12),ylim=(0,.35))
ax.grid(alpha=.25);ax.legend(loc='lower right',fontsize=9)
fig.tight_layout();fig.savefig(ROOT/'figures'/'phase_boundaries.pdf');plt.close(fig)
xs=np.linspace(-1,1,501)
fig,ax=plt.subplots(figsize=(7.1,3.9))
for p in (.10,.19,.25):
    t=p*xs
    D=1-6*p+6*p*p
    gap=2*D*t*t-6*t**4
    ax.plot(xs,gap,label=f'p = {p:.2f}',linewidth=1.8)
ax.set(xlabel=r'Normalized imbalance $t/p$',ylabel=r'$H_{T,2}(p+t,p-t)-H_{T,2}(p,p)$')
ax.grid(alpha=.25);ax.legend(fontsize=9)
fig.tight_layout();fig.savefig(ROOT/'figures'/'collision_profiles.pdf');plt.close(fig)
print('Numerical table and two vector PDF figures written.')
print('\n'.join(', '.join(r) for r in rows))
