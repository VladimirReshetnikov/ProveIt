#!/usr/bin/env python3
"""Generate exact-formula illustrations; these are not numerical proofs."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

dest = Path(__file__).resolve().parents[1]/'figures'
dest.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Serif', 'font.size':10,
                     'axes.spines.top':False, 'axes.spines.right':False,
                     'axes.titlepad':10, 'pdf.fonttype':42,
                     'savefig.bbox':'tight'})
navy, teal, rust, gray = '#16324F', '#147D80', '#A44435', '#718096'

t = np.linspace(0, 2/3, 1001)
psi = 4*t-10*t*t+6*t*t*t
fig, ax = plt.subplots(figsize=(6.15,3.4))
ax.plot(t,psi,color=navy,lw=2.1,label=r'$\Psi(t)=4t-10t^2+6t^3$')
ax.axhline(1/4,color=rust,ls='--',lw=1,label=r'arbitrary domain: $\varepsilon<1/4$')
ax.axhline(4/9,color=teal,ls='-.',lw=1,label=r'exponent-three domain: $\varepsilon<4/9$')
tau=(2-np.sqrt(2))/3
ax.scatter([tau,1/3,2/3],[4/9,4/9,0],color=[teal,teal,navy],s=22,zorder=4)
ax.set(xlabel='error-support density $t$ relative to an affine map',
       ylabel='parallelogram defect', xlim=(0,2/3), ylim=(-.01,.50))
ax.grid(axis='y',alpha=.18)
ax.legend(loc='lower left',frameon=False,fontsize=8.4)
fig.savefig(dest/'rigidity_profile.pdf')
fig.savefig(dest/'rigidity_profile.png',dpi=170)
plt.close(fig)

t=np.linspace(-.01,.01,501)
excess=96*t*t/(49*(91+12*t))
fig, ax=plt.subplots(figsize=(6.15,2.85))
ax.plot(t,1e6*excess,color=teal,lw=2.1)
ax.axhline(0,color=gray,lw=.6)
ax.set(xlabel=r'third-budget perturbation $t$',
       ylabel=r'exact gain over fixed certificate ($\times10^{-6}$)',
       xlim=(-.01,.01),ylim=(0,2.35))
ax.set_xticks([-.01,-.005,0,.005,.01])
ax.grid(alpha=.18)
fig.savefig(dest/'fourier_curvature.pdf')
fig.savefig(dest/'fourier_curvature.png',dpi=170)
plt.close(fig)
print('Wrote two PDF figures and corresponding PNG previews.')
