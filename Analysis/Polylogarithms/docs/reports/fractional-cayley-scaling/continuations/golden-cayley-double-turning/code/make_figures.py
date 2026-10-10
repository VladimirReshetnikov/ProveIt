#!/usr/bin/env python3
"""Reproduce the article's diagnostic axis plot and local normal-form plot.

The figures illustrate proved results; floating-point samples are not used
in any exact certificate. Run from any working directory.
"""
from pathlib import Path
import json
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'figures'
OUT.mkdir(exist_ok=True)
mp.mp.dps = 45

plt.rcParams.update({
    'font.family': 'DejaVu Sans', 'font.size': 10,
    'axes.spines.top': False, 'axes.spines.right': False,
    'axes.labelcolor': '#19344A', 'text.color': '#19344A',
    'xtick.color': '#53616E', 'ytick.color': '#53616E',
    'axes.edgecolor': '#9AA8B0', 'grid.alpha': .20,
    'savefig.bbox': 'tight', 'pdf.fonttype': 42,
})
TEAL, NAVY, GOLD, RED = '#176B70', '#19344A', '#BB872C', '#A5444D'

def C(b):
    return mp.dirichlet(b, [0, 1, 0, -1]) + mp.power(2, -b)*mp.altzeta(b)

b_star = mp.findroot(lambda b: mp.diff(C, b), (mp.mpf('1.2'), mp.mpf('1.4')))
c_star = C(b_star)
bs = np.concatenate(([0.0], np.linspace(.025, 7.0, 225)))
cs = np.array([1.0 if b == 0 else float(C(mp.mpf(str(b)))) for b in bs])
fig, ax = plt.subplots(figsize=(7.1, 3.6))
ax.plot(bs, cs, color=TEAL, lw=2.3, label=r'$C(b)=\beta(b)+2^{-b}\eta(b)$')
ax.axhline(9/8, color=GOLD, lw=1.7, ls='--', label=r'$9/8$: bound for every $N\geq2$')
ax.axhline(1, color='#9AA8B0', lw=.8)
ax.scatter([float(b_star)], [float(c_star)], color=NAVY, s=34, zorder=5)
ax.annotate(r'$C_*\approx1.1365611033$'+'\n'+r'$b_*\approx1.3022165871$',
            xy=(float(b_star), float(c_star)), xytext=(2.6, 1.142),
            arrowprops={'arrowstyle':'-', 'color': NAVY}, va='top', fontsize=10)
ax.set(xlim=(0,7), ylim=(.995,1.152), xlabel='Inner order b', ylabel='Scaled Euler constant')
ax.grid(axis='y')
ax.legend(loc='center right', bbox_to_anchor=(1,.43), frameon=False, fontsize=9)
fig.tight_layout()
fig.savefig(OUT/'euler_axis.pdf')
fig.savefig(OUT/'euler_axis.png', dpi=170)
plt.close(fig)

u = np.linspace(0,1.66,500)
z = np.linspace(0,2.4,500)
fig, axes = plt.subplots(1,2,figsize=(7.4,3.2))
for lam, color in [(.4,TEAL),(1.0,GOLD),(1.3,RED)]:
    axes[0].plot(z, -lam+2*z-z*z, color=color, lw=1.9, label=rf'$\lambda={lam:g}$')
    axes[1].plot(u, -lam*u*u+u**4-u**6/3, color=color, lw=1.9)
roots = np.sqrt([1-np.sqrt(.6),1+np.sqrt(.6)])
heights = -.4*roots**2+roots**4-roots**6/3
axes[1].scatter(roots, heights, color=TEAL, s=25, zorder=4)
axes[1].annotate('minimum', (roots[0],heights[0]), xytext=(.10,-.37),
                 arrowprops={'arrowstyle':'-', 'color':TEAL}, color=TEAL, fontsize=9)
axes[1].annotate('maximum', (roots[1],heights[1]), xytext=(.76,.64),
                 arrowprops={'arrowstyle':'-', 'color':TEAL}, color=TEAL, fontsize=9)
axes[0].set(xlim=(0,2.4),ylim=(-1.7,.8),xlabel=r'$t/\varepsilon$',
            ylabel='Scaled derivative', title='Two roots merge at the fold')
axes[1].set(xlim=(0,1.66),ylim=(-.95,.72),xlabel=r'$\rho/\sqrt{\varepsilon}$',
            ylabel='Scaled change in normalized radius', title='Minimum followed by maximum')
for ax in axes:
    ax.axhline(0,color='#9AA8B0',lw=.8)
    ax.grid(axis='y')
axes[0].legend(frameon=False, fontsize=9, loc='lower center')
fig.tight_layout(w_pad=2)
fig.savefig(OUT/'radial_local_model.pdf')
fig.savefig(OUT/'radial_local_model.png',dpi=170)
plt.close(fig)

receipt = {
    'status':'diagnostic only; not a proof certificate',
    'working_decimal_precision': mp.mp.dps,
    'axis_maximizer':mp.nstr(b_star,40), 'axis_maximum':mp.nstr(c_star,40),
    'radial_model':{
        'path':'q=-3 R0 epsilon, k=3 R0 lambda epsilon^2, R0<0',
        'scaled_derivative':'-lambda+2 z-z^2; z=t/epsilon',
        'scaled_change':'-lambda u^2+u^4-u^6/3; u=rho/sqrt(epsilon)',
        'scale_for_change':'-3 R0 epsilon^3',
        'lambda_values':[.4,1.0,1.3],
        'positive_turning_radii_at_lambda_0.4':[float(r) for r in roots],
    },
}
(ROOT/'data'/'figure_diagnostics.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('Created euler_axis and radial_local_model (PDF and PNG).')
print('Axis diagnostics:',mp.nstr(b_star,24),mp.nstr(c_star,24))
