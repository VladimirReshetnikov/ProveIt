#!/usr/bin/env python3
"""Plot exact rational results (matplotlib is needed only for this figure)."""
from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
plt.rcParams['pdf.fonttype']=42
plt.rcParams['ps.fonttype']=42

root=Path(__file__).resolve().parents[1]
rows=list(csv.DictReader((root/'results/exact_distances.csv').open()))
fig,axes=plt.subplots(1,2,figsize=(10,3.8),layout='constrained')
colors=['#176B87','#B35A32','#69549A']
for mode,label,color in zip(['square','gap2','tall'],['a = b','a = b + 2','a = 2b'],colors):
    data=[r for r in rows if r['q']=='2' and int(r['b'])<=24 and
          (int(r['a'])==int(r['b']) if mode=='square' else
           int(r['a'])==int(r['b'])+2 if mode=='gap2' else
           int(r['a'])==2*int(r['b']))]
    data.sort(key=lambda r:int(r['b']))
    x=[int(r['b']) for r in data]
    axes[0].semilogy(x,[float(r['rank_tv']) for r in data],'-o',ms=3,lw=1.5,color=color,label=label)
    axes[1].plot(x,[float(r['full_tv']) for r in data],'-o',ms=3,lw=1.5,color=color,label=label)
delta=float(rows[0]['delta'])
axes[1].axhline(delta,color='#222222',lw=1,ls='--',label=r'$\Delta_2$')
axes[0].set(title='Rank laws become indistinguishable',ylabel='Total variation distance',xlabel='Smaller dimension b')
axes[1].set(title='Full matrix laws remain separated',ylabel='Total variation distance',xlabel='Smaller dimension b',ylim=(.122,.132))
for ax in axes:
    ax.grid(True,alpha=.2)
    ax.spines[['top','right']].set_visible(False)
    ax.legend(frameon=False,fontsize=8)
    ax.set_xticks([2,6,10,14,18,22])
fig.savefig(root/'figures/distances.pdf',bbox_inches='tight')
fig.savefig(root/'figures/distances.png',dpi=180,bbox_inches='tight')
print('Created figures/distances.pdf and figures/distances.png')
