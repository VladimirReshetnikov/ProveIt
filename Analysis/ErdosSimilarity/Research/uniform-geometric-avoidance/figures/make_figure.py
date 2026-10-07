#!/usr/bin/env python3
"""Create the original explanatory figure; the data are not proof certificates."""
from pathlib import Path
from fractions import Fraction
import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

out = Path(__file__).resolve().parent
Q = Fraction(1,16)
alpha = Fraction(1,4)
qs = [Fraction(1,3), Fraction(1,2), Fraction(2,3), Fraction(3,4)]
js = list(range(1,8))
colors = ['#173d49','#176f76','#bb732d','#a64466']
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
                     'axes.spines.top':False,'axes.spines.right':False,
                     'pdf.fonttype':42})
fig, axs=plt.subplots(1,2,figsize=(10,3.7),layout='constrained')
for q,c in zip(qs,colors):
    axs[0].plot(js,[j*math.log(float(q),float(Q)) for j in js],
                marker='o',ms=3,color=c,label=f'q = {q}')
    logs=[]
    for j in js:
        n=0; value=Fraction(1)
        while value>Q**j:
            n+=1; value*=q
        logs.append(math.log(float(value),float(Q)))
    axs[1].plot(js,logs,marker='o',ms=3,color=c,label=f'q = {q}')
x=np.linspace(1,7,100)
axs[1].fill_between(x,x,x+math.log(float(alpha),float(Q)),
                    color='#176f76',alpha=.12,label='Common envelope')
axs[1].plot(x,x,color='#58616b',lw=.8,ls='--')
axs[1].plot(x,x+math.log(float(alpha),float(Q)),color='#58616b',lw=.8,ls='--')
for ax in axs:
    ax.set_xlabel('Scale index j')
    ax.grid(alpha=.13)
    ax.set_xticks(js)
axs[0].set_title('Original terms: different spatial scales',loc='left',fontsize=11)
axs[1].set_title('Selected terms: one common envelope',loc='left',fontsize=11)
axs[0].set_ylabel('Logarithmic scale  log_Q(value)')
axs[0].legend(frameon=False,fontsize=9)
axs[1].legend(handles=[axs[1].collections[0]],labels=['j ≤ log_Q(a_j) < j + 1/2'],
              loc='upper left',frameon=False,fontsize=9)
fig.savefig(out/'synchronized_scales.pdf',bbox_inches='tight')
fig.savefig(out/'synchronized_scales.png',dpi=170,bbox_inches='tight')
print('Created synchronized_scales.pdf and synchronized_scales.png')
