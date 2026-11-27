#!/usr/bin/env python3
"""Vector figures from the proved formulas. Requires numpy/scipy/matplotlib."""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def halfwidth(r):
    if abs(r-round(r)) < 1e-12 and round(r) % 2:
        return np.pi/2
    k = int(np.floor((r+1)/2))
    if k == 1:
        return 2*np.pi/(r+1)
    s = (-1)**k
    a = brentq(lambda t: r*np.sin(r*t-(k-1)*np.pi)*np.cos(t)
               - np.cos(r*t-(k-1)*np.pi)*np.sin(t),
               (k-1)*np.pi/r, (k-.5)*np.pi/r, xtol=1e-14)
    M = -s*np.cos(r*a)/np.cos(a)
    return brentq(lambda t: s*np.cos(r*t)+M*np.cos(t), np.pi/2,
                  min(np.pi,(k+.5)*np.pi/r), xtol=1e-14)


def main():
    root=Path(__file__).resolve().parents[1]
    figdir=root/'figures';figdir.mkdir(exist_ok=True)
    plt.rcParams.update({'font.family':'serif','font.size':9,'axes.titlesize':10,
                         'axes.spines.top':False,'axes.spines.right':False,
                         'mathtext.fontset':'cm','pdf.fonttype':42})
    fig,(ax,bx)=plt.subplots(1,2,figsize=(7.0,2.85),layout='constrained')
    for low in (1,3,5,7):
        offsets=np.unique(np.r_[np.geomspace(1e-7,.1,45),np.linspace(.1,1.9,140),
                                2-np.geomspace(1e-7,.1,45)])
        rr=low+offsets
        ax.plot(rr,[halfwidth(r)/np.pi for r in rr],color='#195f78',lw=1.5)
    ax.scatter([1,3,5,7,9],[.5]*5,color='#195f78',s=14,zorder=5)
    ax.scatter([1],[1],facecolor='white',edgecolor='#195f78',s=24,zorder=5)
    ax.set(xlabel=r'Frequency ratio $r=\sigma/\tau$',ylabel=r'Optimal half-width $H(r)/\pi$',
           title='Minimum support radius',xlim=(.8,9.15),ylim=(.46,1.04),xticks=[1,3,5,7,9])
    ax.grid(alpha=.16)
    data=json.loads((root/'evidence'/'two_frequency_data.json').read_text())
    # The data records normalized cusp ratios; recover the observed excess.
    records=data['right_cusp_checks']
    records=[x for x in records if x['m']==3]
    eps=np.array([float(x['epsilon']) for x in records])
    C=(np.pi/16)**(1/3)
    ratios=np.array([float(x['v_over_predicted']) for x in records])
    observed=2*C*eps**(1/3)*ratios
    xx=np.geomspace(min(eps)/2,max(eps)*2,100)
    bx.loglog(xx,2*C*xx**(1/3),'--',color='#b45232',lw=1.25,label=r'$2(\pi/16)^{1/3}\varepsilon^{1/3}$')
    bx.loglog(eps,observed,'o',color='#195f78',ms=4,label='Computed optimum')
    bx.set(xlabel=r'$\varepsilon$ in $r=3+\varepsilon$',
           ylabel=r'$H(3+\varepsilon)-\pi/2$',title='Cube-root law at $r=3$')
    bx.grid(alpha=.16,which='major');bx.legend(frameon=False,fontsize=8,loc='upper left')
    fig.savefig(figdir/'resonance.pdf',bbox_inches='tight')
    fig.savefig(figdir/'resonance.png',dpi=220,bbox_inches='tight')
    print('Created figures/resonance.pdf and figures/resonance.png')


if __name__=='__main__':
    main()
