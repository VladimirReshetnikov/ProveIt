#!/usr/bin/env python3
"""Publication figure; plotted decimals illustrate, but do not certify, roots."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parent.parent
out=ROOT/'figures'
out.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,
 'axes.spines.right':False,'pdf.fonttype':42,'figure.dpi':150})
double=(.22658172537292024855,.02150973859349619539)
infinite=(2/7,1/14)
fig,axes=plt.subplots(1,2,figsize=(11.4,4.4),gridspec_kw={'width_ratios':[1,1.18]})
ax=axes[0]
tt=np.linspace(-.5,.5,1601)
boundary=np.sqrt(np.maximum(0,np.where(tt<=1/6,(.5+tt)**2,4*tt*(1-2*tt))))
ax.fill_between(tt,-boundary,boundary,color='#dcece9',label='Feasible shapes')
ax.plot(tt,boundary,color='#426e6b',lw=1);ax.plot(tt,-boundary,color='#426e6b',lw=1)
linevals=[(1+54*tt)/13,(2+16*tt)/11,1-10*tt]
colors=['#8796a5','#b77d4b','#7d77a5']
for val,col,label in zip(linevals,colors,['$L_1=0$','$L_2=0$','$L_3=0$']):
 masked=np.where(np.abs(val)<=boundary+1e-9,val,np.nan)
 ax.plot(tt,masked,color=col,lw=1.5,ls='--',label=label)
ax.scatter([infinite[1]],[infinite[0]],color='#b94e48',marker='*',s=135,zorder=5,label='Infinitely blind shape')
ax.scatter([double[1]],[double[0]],color='#183b62',s=40,zorder=6,label='Two-frequency shape')
ax.set(xlabel='$t=ac/R$',ylabel='$s=b(a+c)/R$',xlim=(-.5,.5),ylim=(-.76,.76),title='Complete parameter domain')
ax.legend(loc='lower left',fontsize=7.5,framealpha=.95)
ax=axes[1]
xx=np.linspace(0,15,5000)
def symbol(s,t):
 return (-4+7*s-4*t)+(8-32*s+48*t)*np.exp(1j*xx*np.log(2))+(27*s-108*t)*np.exp(1j*xx*np.log(3))+64*t*np.exp(1j*xx*np.log(4))
ax.plot(xx,np.abs(symbol(*double)),color='#183b62',lw=1.6,label='Certified two-frequency shape')
ax.plot(xx,np.abs(symbol(*infinite)),color='#b94e48',lw=1.1,alpha=.8,label='Infinitely blind shape')
for x in [5.698378161005082,10.73724168918561]:
 ax.scatter([x],[0],color='#183b62',s=24,zorder=5)
 ax.annotate(f'{x:.4f}',(x,0),xytext=(0,7),textcoords='offset points',ha='center',fontsize=8)
ax.set(xlabel='Logarithmic frequency $\\xi$',ylabel='$|S_{s,t}(\\xi)|$',xlim=(0,15),ylim=(-.5,None),title='Different blind sets; joint recovery')
ax.legend(loc='upper left',fontsize=8)
fig.tight_layout(pad=1.3)
fig.savefig(out/'five_shapes.pdf',bbox_inches='tight')
fig.savefig(out/'five_shapes.png',bbox_inches='tight')
print('Created figures/five_shapes.pdf and figures/five_shapes.png')
