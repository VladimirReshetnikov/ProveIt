#!/usr/bin/env python3
"""Plot the two different detection windows; no data are simulated."""
from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify import alpha, rank_profile, poisson_profile

root=Path(__file__).resolve().parent
colors=['#1f5a98','#d66a32','#2c806b']
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False})
fig,ax=plt.subplots(1,2,figsize=(11.8,4.1),constrained_layout=True)
rows=[]
for c,color in zip(range(3),colors):
    ss=np.arange(-10,16)
    vals=[rank_profile(2,c,int(s)) for s in ss]
    ax[0].plot(ss,vals,'o-',ms=3,lw=1.5,color=color,label=f'c = {c}')
    plateau=1-alpha(2,c)
    ax[0].axhline(plateau,ls=':',color=color,lw=.9,alpha=.7)
    rows.extend({'window':'rank','c':c,'x':int(s),'tv':v} for s,v in zip(ss,vals))
    ll=np.linspace(0,8,801)
    vals=[poisson_profile(2,c,float(lam)) for lam in ll]
    ax[1].plot(ll,vals,lw=2,color=color,label=f'c = {c}')
    ax[1].axhline(plateau,ls=':',color=color,lw=.9,alpha=.7)
    rows.extend({'window':'Poisson','c':c,'x':float(lam),'tv':v} for lam,v in zip(ll,vals))
ax[0].set(xlabel='Column excess s  (m = a + s)',ylabel='Total variation distance',
          title='First window: random matrix rank',ylim=(-.02,1.02),xlim=(-10,15))
ax[1].set(xlabel='Scaled column count λ  (m ≈ λ · 2ᵈ)',ylabel='Total variation distance',
          title='Second window: rank flag and zero columns',ylim=(-.02,1.02),xlim=(0,8))
for a in ax:
    a.legend(frameon=False,loc='lower right');a.grid(alpha=.16)
fig.suptitle('Two detection scales over F₂, with a = d − c',fontsize=14,fontweight='bold')
fig.savefig(root/'two_scales.pdf')
fig.savefig(root/'two_scales.png',dpi=180)
with (root/'profile_curves.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=['window','c','x','tv']);w.writeheader();w.writerows(rows)
