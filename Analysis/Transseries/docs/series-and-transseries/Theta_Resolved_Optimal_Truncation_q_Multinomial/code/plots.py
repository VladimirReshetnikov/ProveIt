#!/usr/bin/env python3
"""Figures only: double-precision visualization, not theorem verification."""
from pathlib import Path
import numpy as np
import matplotlib
import matplotlib.pyplot as plt
from scipy.optimize import brentq
# ed. (ProveIt, 2026-09-29): embed TrueType (Type 42) fonts instead of the
# Type 3 fonts that Matplotlib writes by default.
matplotlib.rcParams['pdf.fonttype']=42
matplotlib.rcParams['ps.fonttype']=42
ROOT=Path(__file__).resolve().parents[1]
(ROOT/'figures').mkdir(exist_ok=True)

def profile(lam,th):
    u=lam*(np.arange(-12,13)-th)
    def m1(eta):
        w=np.exp(-u*u/2+eta*u)
        return np.dot(u,w)
    eta=brentq(m1,-max(2,lam),max(2,lam))
    return lam/np.sqrt(2*np.pi)*np.exp(-u*u/2+eta*u).sum(),eta

th=np.linspace(0,1,301)
fig,ax=plt.subplots(figsize=(7.0,4.2))
for lam in [2,4,6]:
    values=np.array([profile(lam,t)[0] for t in th])
    ax.plot(th,values,label=rf'$\lambda={lam}$')
ax.set_xlabel(r'Lattice phase $\theta$')
ax.set_ylabel(r'Optimized factor $\mathcal{M}_\lambda(\theta)$')
ax.legend(); ax.grid(alpha=.25)
fig.tight_layout(); fig.savefig(ROOT/'figures'/'optimized_theta.pdf'); plt.close(fig)

fig,ax=plt.subplots(figsize=(7.0,4.2))
for n in range(1,13):
    a=np.linspace(1/(n+1),1/n,200)
    hs=2*np.pi*a
    values=[]
    for h in hs:
        c=2*np.pi/h
        if abs(c-round(c))<1e-9:
            values.append(1.)
        else:
            m=int(np.floor(c)); tm=h*m; tp=h*(m+1)
            rho=h/np.log(tp/tm)
            values.append((tm-rho*np.log(tm/(2*np.pi)))/(2*np.pi))
    ax.plot(a,values)
ax.set_xlabel(r'Fixed mesh ratio $h/(2\pi)$')
ax.set_ylabel(r'Optimal action ratio $I_h/(2\pi)$')
ax.set_xlim(0,1); ax.grid(alpha=.25)
fig.tight_layout(); fig.savefig(ROOT/'figures'/'arithmetic_action.pdf'); plt.close(fig)
print('Wrote two figures.')
