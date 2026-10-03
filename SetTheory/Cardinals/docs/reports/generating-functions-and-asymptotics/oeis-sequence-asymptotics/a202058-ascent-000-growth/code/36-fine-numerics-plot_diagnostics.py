#!/usr/bin/env python3
"""Render the vector diagnostic figure at its final 6.5-inch report width."""
from pathlib import Path
from datetime import datetime, timezone
import csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

root=Path(__file__).resolve().parent
with (root/'diagnostics.tsv').open() as f:
    rows=list(csv.DictReader(f,delimiter='\t'))
n=np.array([int(r['n']) for r in rows])
h=np.array([float(r['h']) for r in rows])
g=np.array([float(r['g=n*delta_h']) for r in rows])
c=np.array([float(r['c=n*delta_g']) for r in rows])
plt.rcParams.update({'font.size':8,'axes.labelsize':8,'xtick.labelsize':7,
                     'ytick.labelsize':7,'legend.fontsize':7})
fig,axs=plt.subplots(1,3,figsize=(6.5,1.9))
fig.subplots_adjust(left=.075,right=.96,bottom=.23,top=.70,wspace=.42)
for ax,y,label in zip(axs,[h,g,c],[r'$h_n$',r'$g_n$',r'$c_n$']):
    exact=(n>=30)&(n<=400); numeric=n>=400
    ax.plot(n[exact],y[exact],color='#164b83',lw=1.1,label='Exact counts')
    ax.plot(n[numeric],y[numeric],color='#b25817',lw=1.1,ls='--',label='Long-double continuation')
    ax.set(xlabel=r'$n$',ylabel=label,xlim=(0,1000),xticks=[0,500,1000])
    ax.tick_params(length=2.5,pad=2)
    ax.grid(alpha=.2,lw=.4)
axs[0].set(ylim=(12,47),yticks=[15,30,45])
axs[1].set(ylim=(6,12),yticks=[7,9,11])
axs[2].set(ylim=(1.325,1.57),yticks=[1.35,1.45,1.55])
axs[2].axhline(4/3,color='gray',lw=.8,ls=':',label='4/3 conjectural target')
handles,labels=axs[2].get_legend_handles_labels()
fig.legend(handles,labels,loc='upper center',bbox_to_anchor=(.52,.88),
           ncol=3,frameon=False,handlelength=1.8,columnspacing=1.2,
           handletextpad=.4,borderaxespad=0)
fig.suptitle('A202058 correction diagnostics',fontsize=9,y=.995)
fig.savefig(root/'correction-diagnostics.png',dpi=180)
date=datetime(2026,10,2,tzinfo=timezone.utc)
fig.savefig(root/'correction-diagnostics.pdf',metadata={'CreationDate':date,'ModDate':date})
