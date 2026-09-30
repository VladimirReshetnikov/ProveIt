#!/usr/bin/env python3
"""Generate the inner-fold comparison figure and its numerical data."""
from pathlib import Path
import csv
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
# ed. (2026-09-29): embed TrueType (Type 42) fonts instead of Type 3 in the PDF figure.
matplotlib.rcParams['pdf.fonttype']=42
matplotlib.rcParams['ps.fonttype']=42
import matplotlib.pyplot as plt
from verify import forward, jets


def main():
    mp.mp.dps=60
    out=Path('figures'); out.mkdir(exist_ok=True)
    a=mp.mpf(13)/10; b=mp.mpf(7)/10
    zetas=[mp.mpf('-0.4')+mp.mpf('2.4')*i/120 for i in range(121)]
    records=[]
    fig,ax=plt.subplots(figsize=(6.6,3.85))
    for gi,ls in [(16,'--'),(32,'-.'),(64,':')]:
        g=mp.mpf(gi); c=jets(g,a,b,1)[0]; Fg=forward(g,a,b)
        values=[]
        for zeta in zetas:
            q=mp.exp(-1)*(1-zeta/g**2)
            guess=-1+mp.sqrt(2*zeta+a)/g
            eq=lambda s:(forward(g+s,a,b)-Fg)/c+q*mp.exp(-s)
            s=mp.findroot(eq,(guess,guess+mp.mpf('.001')),tol=mp.mpf('1e-50'))
            val=g*(s+1)
            values.append(float(val))
            records.append([gi,mp.nstr(zeta,18),mp.nstr(val,35)])
        ax.plot([float(z) for z in zetas],values,ls,label=f'g = {gi}',linewidth=1.3)
    ax.plot([float(z) for z in zetas],[float(mp.sqrt(2*z+a)) for z in zetas],
            '-',label=r'Limit $\sqrt{2\zeta+a}$',linewidth=1.6)
    ax.set_xlabel(r'$\zeta$, where $q=e^{-1}(1-\zeta/g^2)$')
    ax.set_ylabel(r'$g\,[s_g(q)+1]$')
    ax.set_title(r'Curvature-shifted inner limit: $a=1.3$, $b=0.7$')
    ax.legend(frameon=False,fontsize=9)
    ax.grid(True,alpha=.25)
    fig.tight_layout()
    fig.savefig(out/'fold_scaling.pdf')
    fig.savefig(out/'fold_scaling.png',dpi=170)
    plt.close(fig)
    with (out/'fold_scaling.csv').open('w',newline='') as f:
        # ed. (2026-09-29): LF line endings on every platform, like the filed files.
        w=csv.writer(f,lineterminator='\n'); w.writerow(['g','zeta','g_times_s_plus_one']); w.writerows(records)
    print('Generated figure and 363 computed points.')

if __name__=='__main__': main()
