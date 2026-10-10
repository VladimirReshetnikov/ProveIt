#!/usr/bin/env python3
"""Create the research figures from recorded data and stated formulas."""
from pathlib import Path
import json
from fractions import Fraction
import numpy as np
import mpmath as mp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
FIG = ROOT/'figures'
FIG.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'STIXGeneral','mathtext.fontset':'stix',
                     'font.size':10,'axes.labelsize':11,'axes.titlesize':11,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'pdf.fonttype':42,'ps.fonttype':42})
COLORS = ['#183b56','#007c83','#a0444d']


def save(fig, name):
    fig.savefig(FIG/(name+'.pdf'), bbox_inches='tight')
    fig.savefig(FIG/(name+'.png'), dpi=180, bbox_inches='tight')
    plt.close(fig)


mp.mp.dps = 60
def cb(b):
    b = mp.mpf(b)
    beta = mp.pi/4 if b == 1 else (mp.zeta(b,mp.mpf(1)/4)-mp.zeta(b,mp.mpf(3)/4))/4**b
    return beta+mp.altzeta(b)/2**b


fig,axs=plt.subplots(1,2,figsize=(7.0,2.8))
bs=np.linspace(.02,5,220)
axs[0].plot(bs,[float(cb(str(b))) for b in bs],color=COLORS[0],lw=1.7)
bstar=mp.mpf('1.3022165871012412095923717015')
cstar=cb(bstar)
axs[0].plot([float(bstar)],[float(cstar)],'o',color=COLORS[2],ms=4)
axs[0].axhline(57/50,color=COLORS[1],ls='--',lw=1,label=r'$57/50$')
axs[0].set(xlabel='Inner order $b$',ylabel='$C(b)$',title='Sharp constants at fixed inner order',ylim=(.995,1.145))
axs[0].legend(frameon=False,loc='lower right')

from math import comb
seq=[mp.mpf(0)]
hh=mp.mpf(0)
for j in range(1,240):
    hh += mp.mpf(1)/j
    if j%2==0:
        seq.append(hh/(j+1)**2)
def euler(n):
    return mp.fsum([(-1)**j*seq[j]*sum(comb(n,r) for r in range(j+1,n+1))/mp.mpf(2)**n for j in range(n)])
g=euler(120)
ns=list(range(1,19))
rs=[float(2**n*(euler(n)-g)) for n in ns]
axs[1].plot(ns,rs,'o-',color=COLORS[0],ms=3,lw=1.3)
axs[1].set(xlabel='Euler index $N$',ylabel='$R_N(2,1)$',title='Scaled errors need not decrease')
axs[1].set_xticks([1,4,8,12,16,18])
for ax in axs: ax.grid(alpha=.15)
fig.tight_layout(w_pad=2)
save(fig,'euler_constants')

data=json.loads((ROOT/'data/all_ratio_diagnostics.json').read_text())
fig,axs=plt.subplots(1,2,figsize=(7.0,2.8))
for family,label,color in [('balanced','$m=n$',COLORS[0]),('ratio_four','$m=n/4$',COLORS[1]),('fixed_one','$m=1$',COLORS[2])]:
    rows=[r for r in data['rows'] if r['family']==family]
    nn=[float(r['n']) for r in rows]
    for ax,key in zip(axs,['exact_over_leading_minus_one','exact_over_corrected_minus_one']):
        ax.loglog(nn,[abs(float(r[key])) for r in rows],'o-',label=label,color=color,ms=4,lw=1.4)
axs[0].set_title('Leading uniform formula')
axs[1].set_title('Including the first correction')
for ax in axs:
    ax.set_xlabel('Larger exponent $n$')
    ax.set_ylabel('Absolute relative error')
    ax.grid(alpha=.18,which='both')
    ax.legend(frameon=False)
fig.tight_layout(w_pad=2)
save(fig,'uniform_moment_errors')

audit=json.loads((ROOT/'code/lerch/lerch_effective_verification.json').read_text())
rows=audit['finite_product_mesh_checks']
nn=[int(r['n']) for r in rows]
generic=[576*n*n*(3*n)**(2*n-4) for n in nn]
specific=[int(r['threshold_from_certified_finite_product_mesh']) for r in rows]
fig,ax=plt.subplots(figsize=(6.8,2.8))
ax.semilogy(nn,generic,'o-',label='Closed all-index formula',color=COLORS[0],ms=4)
ax.semilogy(nn,specific,'s-',label='Exact finite-product mesh certificate',color=COLORS[1],ms=4)
ax.set(xlabel='Laurent index $n$',ylabel='Sufficient derivative order $k$',title='Two proved uniform saturation bounds')
ax.set_xticks(nn)
ax.grid(alpha=.15,which='both')
ax.legend(frameon=False)
fig.tight_layout()
save(fig,'lerch_thresholds')
print('Created three PDF figures and PNG companions.')
