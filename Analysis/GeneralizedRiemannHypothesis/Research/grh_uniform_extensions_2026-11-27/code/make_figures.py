#!/usr/bin/env python3
"""Publication figures from exact rational checks, using matplotlib."""
import csv
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
rows=list(csv.DictReader((ROOT/'data'/'symplectic_checks.csv').open()))
rows=[r for r in rows if r['q']=='2']
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'axes.labelcolor':'#25304a','text.color':'#25304a',
                     'axes.titleweight':'bold','savefig.bbox':'tight'})
fig,ax=plt.subplots(1,2,figsize=(8.3,3.35),gridspec_kw={'width_ratios':[1,1.08]})
colors=['#18657e','#bd6336','#6550a1']
for label,fun,color in zip([r'$a=b$',r'$a=b+2$',r'$a=2b$'],
                           [lambda b:b,lambda b:b+2,lambda b:2*b],colors):
    rr=sorted([r for r in rows if int(r['a'])==fun(int(r['b']))],key=lambda r:int(r['b']))
    bs=[int(r['b']) for r in rr]
    ax[0].plot(bs,[float(r['full_tv']) for r in rr],marker='o',ms=3,lw=1.6,label=label,color=color)
    ax[1].semilogy(bs,[float(r['rank_tv']) for r in rr],marker='o',ms=3,lw=1.6,label=label,color=color)
    ax[1].semilogy(bs,[float(r['predicted_rank_tv']) for r in rr],ls='--',lw=.85,color=color,alpha=.65)
limit=float(rows[0]['limit'])
ax[0].axhline(limit,color='#364052',ls=':',lw=1.2,label=r'$\Delta_2$')
ax[0].set(title='Full matrix: persistent dependence',xlabel=r'Smaller dimension $b$',ylabel='Total variation distance')
ax[1].set(title='Rank: exponentially vanishing information',xlabel=r'Smaller dimension $b$',ylabel='Total variation distance (log scale)')
for aa in ax:
    aa.grid(alpha=.17)
    aa.set_xticks([2,6,10,14,18,22])
    aa.legend(frameon=False,fontsize=8)
ax[0].set_ylim(.122,.132)
fig.text(.52,-.015,'Solid curves: exact probabilities. Dashed curves: sharp first-order rank formula.',ha='center',fontsize=8,color='#556078')
fig.tight_layout(w_pad=2)
(ROOT/'figures').mkdir(exist_ok=True)
fig.savefig(ROOT/'figures'/'symplectic_separation.pdf')
fig.savefig(ROOT/'figures'/'symplectic_separation.png',dpi=180)
plt.close(fig)
print('Saved figures/symplectic_separation.pdf and .png')
