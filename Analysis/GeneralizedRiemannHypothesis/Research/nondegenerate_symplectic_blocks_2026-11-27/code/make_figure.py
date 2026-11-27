#!/usr/bin/env python3
"""Publication figure from the exact rational calculations (no simulation)."""
import csv
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parents[1]
rows=list(csv.DictReader((root/'results/exact_distances.csv').open()))
rows=[{k:float(v) for k,v in x.items()} for x in rows if x['q']=='2']
constant=json.loads((root/'results/limiting_constants.json').read_text())[0]
n=[int(x['n']) for x in rows]
full=[x['full_tv'] for x in rows]
rank=[x['rank_tv'] for x in rows]
phi=float(constant['gl_product'])
delta=float(constant['delta'])
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.labelsize':10,
                     'axes.titlesize':11,'legend.fontsize':9,'pdf.fonttype':42,
                     'axes.spines.top':False,'axes.spines.right':False})
fig,axs=plt.subplots(1,2,figsize=(10.1,3.7),constrained_layout=True)
axs[0].semilogy(n,full,'o-',color='#185f86',lw=1.8,label='Full matrix law')
axs[0].semilogy(n,rank,'s-',color='#d16d32',lw=1.8,label='Rank alone')
axs[0].semilogy(n,[phi*2.0**(-x) for x in n],'--',color='#555555',lw=1,
               label=r'Sharp rank asymptotic $c_2\,2^{-n}$')
axs[0].set(title='A persistent gap invisible to rank',xlabel='Block dimension n (ambient dimension 2n)',
           ylabel='Total variation distance')
axs[0].set_xticks([2,6,10,14,18,22])
axs[0].grid(axis='y',alpha=.18)
axs[0].legend(loc='lower left',frameon=False)
axs[1].plot(n,[x*2.0**k for x,k in zip(rank,n)],'s-',color='#d16d32',lw=1.8,
            label=r'$2^n$ times the rank distance')
axs[1].axhline(phi,color='#555555',lw=1,ls='--',label=r'Limit $c_2=0.288788\ldots$')
axs[1].set(title='The exponential rate is sharp',xlabel='Block dimension n',ylabel='Scaled rank distance')
axs[1].set_xticks([2,6,10,14,18,22])
axs[1].grid(axis='y',alpha=.18)
axs[1].legend(loc='upper right',frameon=False)
fig.savefig(root/'figures/rank_vs_full.pdf')
fig.savefig(root/'figures/rank_vs_full.png',dpi=180)
print('Wrote figures/rank_vs_full.pdf and .png from exact values.')
