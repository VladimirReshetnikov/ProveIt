#!/usr/bin/env python3
"""Create publication figures from exact formulas, not Monte Carlo."""
from pathlib import Path
import sys
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from verify_formulas import exact_laws, delta_interval

root=Path(__file__).resolve().parents[1]
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'axes.titleweight':'bold','figure.dpi':160})
blue='#146C94'; orange='#CF5C36'; grey='#5B6573'
ns=list(range(2,33,2))
values=[exact_laws(2,n,n//2) for n in ns]
full=[float(x[2]) for x in values];rank=[float(x[3]) for x in values]
delta=float(delta_interval(2)[0])
fig,axs=plt.subplots(1,2,figsize=(10.4,4.0),constrained_layout=True)
ax=axs[0]
ax.plot(ns,full,'o-',c=blue,label='Full matrix distribution',markersize=3)
ax.plot(ns,rank,'s-',c=orange,label='Rank distribution',markersize=3)
ax.axhline(delta,color=grey,ls='--',lw=.9)
ax.annotate(r'$\delta_2\approx0.068805$',(18,delta),xytext=(18,.056),color=grey)
ax.set(xlabel='Matrix dimension n (even)',ylabel='Total variation distance',
       title='A persistent difference in matrix laws',ylim=(-.002,.076))
ax.legend(frameon=False,loc='center right',fontsize=8.5)
ax.grid(axis='y',alpha=.15)
ax=axs[1]
ax.semilogy(ns,rank,'s-',color=orange,markersize=3)
ax.semilogy(ns,[.2887880950866024*2**(-n) for n in ns],ls='--',color=grey,
            label=r'$0.288788\,2^{-n}$')
ax.set(xlabel='Matrix dimension n (even)',ylabel='Distance of rank distributions',
       title='Rank tests lose their distinguishing power')
ax.legend(frameon=False,fontsize=9)
ax.grid(axis='y',alpha=.15)
for ext in ['pdf','png']:
    fig.savefig(root/'figures'/f'rank_vs_matrix.{ext}')
plt.close(fig)

ss=list(range(7));vals=[exact_laws(2,12,s) for s in ss]
fig,ax=plt.subplots(figsize=(6.8,3.7),constrained_layout=True)
ax.plot(ss,[float(x[2]) for x in vals],'o-',c=blue,label='Full matrix distribution')
ax.plot(ss,[float(x[3]) for x in vals],'s-',c=orange,label='Rank distribution')
ax.set(xlabel='Half the rank of the input form, s',ylabel='Total variation distance',
       title='The input pairing changes what rank can detect (q=2, n=12)')
ax.set_xticks(ss)
ax.legend(frameon=False,fontsize=9)
ax.grid(axis='y',alpha=.15)
for ext in ['pdf','png']:
    fig.savefig(root/'figures'/f'form_type.{ext}')
plt.close(fig)
print('Created four figure files from exact rational laws.')
