#!/usr/bin/env python3
"""Reproduce illustrative plots. Numerical values are not proof certificates."""
import json
from pathlib import Path
import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/"results"
mp.mp.dps=35
data=json.loads((BASE/'gamma_joint_diagnostics.json').read_text())
xs=np.linspace(.001,.999,500)
product=np.array([float(mp.loggamma(float(x))*mp.loggamma(1-float(x))) for x in xs])
a=float(mp.log(mp.pi)/2)
d=float(mp.zeta(2)/(2*mp.euler)-mp.euler)

plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'axes.titlesize':11,'axes.labelsize':9})
fig,axes=plt.subplots(1,2,figsize=(7.2,3.7),layout='constrained')
ax=axes[0]
ax.plot(xs,product,color='#254E70',lw=2.3)
ax.axhline(a*a,color='#9F4A36',ls='--',lw=1.2,label=r'$(\log\pi/2)^2$')
ax.plot([.5],[a*a],'o',color='#9F4A36',ms=4)
ax.set(xlabel=r'$x$',ylabel=r'$\log\Gamma(x)\,\log\Gamma(1-x)$',
       title='Reflected product',xlim=(0,1),ylim=(0,.36))
ax.grid(alpha=.15)
ax.legend(frameon=False,loc='lower center')

ax=axes[1]
ss=np.linspace(-1.08,1.08,250)
ax.plot(ss,np.exp(d*np.exp(-ss)),color='#254E70',lw=2,
        label=r'Limit $\exp(d e^{-s})$')
markers=['o','s','^','D']
colors=['#BD6B42','#D6A13D','#529484','#824D83']
for m,marker,color in zip([25,100,400,1600],markers,colors):
    rows=[r for r in data['critical'] if r['m']==m]
    pos=[float(mp.mpf(r['t'])-mp.log(m)) for r in rows]
    val=[float(r['ratio']) for r in rows]
    ax.scatter(pos,val,s=32,marker=marker,color=color,edgecolors='white',
               linewidths=.5,zorder=3,label=f'$m={m}$')
ax.axhline(1,color='#777777',ls=':',lw=1)
ax.set(xlabel=r'$s=n/(m+1)-\log m$',
       ylabel=r'$M_{n,m}/L_{n,m}$',
       title='Critical-window transition',xlim=(-1.1,1.1))
ax.grid(alpha=.15)
ax.legend(frameon=False,fontsize=8,loc='upper right')
fig.savefig(ROOT/'figures'/'gamma_joint.pdf',bbox_inches='tight')
fig.savefig(ROOT/'figures'/'gamma_joint.png',dpi=190,bbox_inches='tight')
print('Saved gamma_joint.pdf and gamma_joint.png')
